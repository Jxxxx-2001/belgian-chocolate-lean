import SlitBoundaryGeometry
import SlitStarConvex
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Convex.PathConnected

/-! The radial domain bounded by the two prescribed arcs and its negative slit. -/

namespace BelgianChocolate.SlitBoundaryGeometry

open Complex Metric Set Filter Topology
open BelgianChocolate.SlitStarConvex

private noncomputable def angle (z : ℂ) : ℝ := Real.arccos (z.re / ‖z‖)
private noncomputable def upperRadius (z : ℂ) : ℝ :=
  Real.exp (-Real.sqrt (angle z * (Real.pi - angle z)))

/-- Direction-dependent positive radius of the prescribed outer boundary. -/
noncomputable def radialRadius (z : ℂ) : ℝ := if 0 < z.im then upperRadius z else 1

/-- The open interior of the boundary, written using the radial inequality. -/
def radialDomain : Set ℂ := {z | ‖z‖ < radialRadius z}

/-- The candidate domain with the prescribed real slit. -/
def candidateSlit (α : ℝ) : Set ℂ := radialDomain \ negativeSlit α

theorem radialRadius_eq_norm_upperPoint {z : ℂ} (h : 0 < z.im) :
    radialRadius z = ‖upperPoint z.arg‖ := by
  rw [radialRadius, ite_eq_left h, norm_upperPoint, upperRadius, angle, Complex.arg_of_im_pos h]

theorem radialRadius_bounds (z : ℂ) :
    Real.exp (-(Real.pi / 2)) ≤ radialRadius z ∧ radialRadius z ≤ 1 := by
  by_cases h : 0 < z.im
  · rw [radialRadius_eq_norm_upperPoint h]
    exact norm_upperPoint_bounds ⟨Complex.arg_nonneg_iff.mpr h.le, Complex.arg_le_pi _⟩
  · rw [radialRadius, ite_eq_right h]
    exact ⟨Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos]), le_rfl⟩

theorem radialRadius_pos (z : ℂ) : 0 < radialRadius z :=
  (Real.exp_pos _).trans_le (radialRadius_bounds z).1

theorem radialDomain_subset_ball : radialDomain ⊆ ball (0 : ℂ) 1 :=
  fun z hz ↦ mem_ball_zero_iff.mpr (hz.trans_le (radialRadius_bounds z).2)

theorem innerBall_subset_radialDomain : ball (0 : ℂ) (Real.exp (-(Real.pi / 2))) ⊆ radialDomain :=
  fun z hz ↦ (mem_ball_zero_iff.mp hz).trans_le (radialRadius_bounds z).1

theorem zero_mem_radialDomain : (0 : ℂ) ∈ radialDomain := by
  exact innerBall_subset_radialDomain (mem_ball_self (Real.exp_pos _))

theorem radialRadius_smul {a : ℝ} (ha : 0 < a) (z : ℂ) :
    radialRadius (a • z) = radialRadius z := by
  have him : (a • z).im = a * z.im := Complex.smul_im _ _
  by_cases hp : 0 < z.im
  · rw [radialRadius_eq_norm_upperPoint (him.symm ▸ mul_pos ha hp),
      radialRadius_eq_norm_upperPoint hp, Complex.real_smul, Complex.arg_real_mul _ ha]
  · have hn : ¬0 < (a • z).im := by
      rw [him]
      exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hp))
    simp only [radialRadius, ite_eq_right hn, ite_eq_right hp]

theorem radialDomain_starConvex : StarConvex ℝ (0 : ℂ) radialDomain := by
  intro z hz a b ha hb hab
  simp only [smul_zero, zero_add]
  rcases hb.eq_or_lt with rfl | hpos
  · simpa only [zero_smul] using zero_mem_radialDomain
  change ‖b • z‖ < radialRadius (b • z)
  rw [radialRadius_smul hpos, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
  have hle : b ≤ 1 := by linarith
  exact (mul_le_of_le_one_left (norm_nonneg z) hle).trans_lt hz

private theorem continuousOn_upperRadius : ContinuousOn upperRadius ({0}ᶜ : Set ℂ) := by
  have hratio : ContinuousOn (fun z : ℂ ↦ z.re / ‖z‖) ({0}ᶜ : Set ℂ) :=
    continuous_re.continuousOn.div continuous_norm.continuousOn (fun _ hz ↦ norm_ne_zero_iff.mpr hz)
  have hangle : ContinuousOn angle ({0}ᶜ : Set ℂ) :=
    Real.continuous_arccos.comp_continuousOn hratio
  exact Real.continuous_exp.comp_continuousOn
    (Real.continuous_sqrt.comp_continuousOn (hangle.mul (continuousOn_const.sub hangle))).neg

private theorem upperRadius_eq_one {z : ℂ} (hz : z ≠ 0) (him : z.im = 0) :
    upperRadius z = 1 := by
  have hc : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [him])
  have hangle : angle z = z.arg := by
    unfold angle
    rw [← Complex.cos_arg hz,
      Real.arccos_cos (Complex.arg_nonneg_iff.mpr him.ge) (Complex.arg_le_pi _)]
  rw [upperRadius, hangle, ← hc]
  by_cases hn : 0 ≤ z.re
  · simp [Complex.arg_ofReal_of_nonneg hn]
  · simp [Complex.arg_ofReal_of_neg (lt_of_not_ge hn)]

theorem continuousOn_radialRadius : ContinuousOn radialRadius ({0}ᶜ : Set ℂ) := by
  classical
  let H : Set ℂ := {z | 0 < z.im}
  have hopen : IsOpen H := isOpen_lt continuous_const continuous_im
  change ContinuousOn (H.piecewise upperRadius (fun _ ↦ (1 : ℝ))) _
  refine ContinuousOn.piecewise ?_ (continuousOn_upperRadius.mono inter_subset_left) continuousOn_const
  intro z hz
  apply upperRadius_eq_one hz.1
  have hnot : z ∉ H := by
    intro h
    exact hz.2.2 (hopen.interior_eq.symm ▸ h)
  have hle : z.im ≤ 0 := le_of_not_gt hnot
  have hu : closure H ⊆ {z : ℂ | 0 ≤ z.im} :=
    closure_minimal (fun z hz ↦ show 0 ≤ z.im from le_of_lt hz) (isClosed_le continuous_const continuous_im)
  exact hle.antisymm (hu (frontier_subset_closure hz.2))

theorem isOpen_radialDomain : IsOpen radialDomain := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  by_cases h : z = 0
  · subst z
    exact Filter.mem_of_superset (ball_mem_nhds _ (Real.exp_pos _)) innerBall_subset_radialDomain
  have hr := (continuousOn_radialRadius z h).continuousAt
    (isClosed_singleton.isOpen_compl.mem_nhds h)
  exact (continuous_norm.continuousAt.eventually_lt hr hz)

theorem isOpen_candidateSlit (α : ℝ) : IsOpen (candidateSlit α) :=
  isOpen_radialDomain.sdiff ((isClosed_eq continuous_im continuous_const).inter
    ((isClosed_le continuous_const continuous_re).inter (isClosed_le continuous_re continuous_const)))

theorem candidateSlit_starConvex {α : ℝ} (hα : α < 0) :
    StarConvex ℝ (0 : ℂ) (candidateSlit α) :=
  starConvex_remove_negativeSlit radialDomain_starConvex radialDomain_subset_ball hα

/-- The radial equality describes the entire frontier of the open candidate domain. -/
theorem frontier_radialDomain_eq_level :
    frontier radialDomain = {z | ‖z‖ = radialRadius z} := by
  ext z
  rw [frontier, isOpen_radialDomain.interior_eq]
  constructor
  · rintro ⟨hz, hnot⟩
    have hn : radialRadius z ≤ ‖z‖ := le_of_not_gt hnot
    have hz₀ : z ≠ 0 := fun h ↦ hnot (h.symm ▸ zero_mem_radialDomain)
    have hc := (continuousOn_radialRadius z hz₀).continuousAt
      (isClosed_singleton.isOpen_compl.mem_nhds hz₀)
    apply le_antisymm _ hn
    by_contra! h
    have he := hc.eventually_lt continuous_norm.continuousAt h
    have hmem : radialDomainᶜ ∈ 𝓝 z :=
      Filter.mem_of_superset he (fun y hy ↦ show ¬ ‖y‖ < radialRadius y from not_lt.mpr hy.le)
    exact (mem_closure_iff_nhds.mp hz _ hmem).elim fun _ ⟨ha, hb⟩ ↦ ha hb
  · intro he
    change ‖z‖ = radialRadius z at he
    refine ⟨?_, fun hz ↦ (show ‖z‖ < radialRadius z from hz).ne he⟩
    let f : ℝ → ℂ := fun r ↦ r • z
    have hone : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num)]
      exact ⟨zero_le_one, le_rfl⟩
    have hcont : Continuous f := by fun_prop
    have hs : f '' (Ioo (0 : ℝ) 1) ⊆ radialDomain := by
      rintro _ ⟨r, hr, rfl⟩
      change ‖r • z‖ < radialRadius (r • z)
      rw [radialRadius_smul hr.1, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, he]
      exact mul_lt_of_lt_one_left (radialRadius_pos _) hr.2
    have hcl := image_closure_subset_closure_image hcont (s := Ioo (0 : ℝ) 1)
      ⟨1, hone, rfl⟩
    simpa [f] using closure_mono hs hcl

/-- The outer frontier is the union of the two prescribed open arcs and their endpoints. -/
theorem frontier_radialDomain :
    frontier radialDomain = ({1,-1} ∪ MarkedRealAxis.curvedEdge ∪ lowerEdge : Set ℂ) := by
  rw [frontier_radialDomain_eq_level]
  ext z
  change (‖z‖ = radialRadius z) ↔ _
  constructor
  · intro hz
    rcases lt_trichotomy z.im 0 with hn | hreal | hp
    · right
      have hr : radialRadius z = 1 := by rw [radialRadius, ite_eq_right (not_lt.mpr hn.le)]
      refine ⟨-z.arg, ⟨neg_pos.mpr (Complex.arg_neg_iff.mpr hn), by linarith [z.neg_pi_lt_arg]⟩, ?_⟩
      have h := Complex.norm_mul_exp_arg_mul_I z
      rw [hz, hr, Complex.ofReal_one, one_mul] at h
      simpa using h.symm
    · left
      left
      have hr : radialRadius z = 1 := by simp [radialRadius, hreal]
      have hc : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [hreal])
      have ha : |z.re| = 1 := by
        have h := hz.trans hr
        rwa [← hc, Complex.norm_real, Real.norm_eq_abs] at h
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ha with h | h
      · have h1 : z = (1 : ℂ) := hc.symm.trans (by exact_mod_cast h)
        rw [h1]
        exact mem_insert _ _
      · have h1 : z = (-1 : ℂ) := hc.symm.trans (by exact_mod_cast h)
        exact mem_insert_of_mem _ (mem_singleton_iff.mpr h1)
    · left
      right
      have hθ₀ : 0 < z.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hp.le)
        (Ne.symm fun h ↦ hp.ne' (Complex.arg_eq_zero_iff.mp h).2)
      have hθ₁ : z.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hp.ne')
      refine ⟨z.arg, ⟨hθ₀,hθ₁⟩, ?_⟩
      change z = upperPoint z.arg
      rw [radialRadius_eq_norm_upperPoint hp, norm_upperPoint] at hz
      nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I z]
      rw [hz, upperPoint]
  · intro hz
    rcases hz with (hz | hz) | hz
    · simp only [mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> simp [radialRadius]
    · obtain ⟨θ, hθ, rfl⟩ := hz
      change ‖upperPoint θ‖ = radialRadius (upperPoint θ)
      have him : 0 < (upperPoint θ).im := by
        simp only [upperPoint, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, Complex.exp_im, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.I_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_one,
          sub_zero, Real.exp_zero, one_mul]
        exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
      have ha : (upperPoint θ).arg = θ := by
        rw [upperPoint, Complex.arg_real_mul _ (Real.exp_pos _), Complex.arg_exp_mul_I,
          toIocMod_eq_self]
        constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
      rw [radialRadius_eq_norm_upperPoint him, ha]
    · obtain ⟨θ, hθ, rfl⟩ := hz
      have hi : (Complex.exp ((-(θ : ℂ)) * I)).im ≤ 0 := by
        simp only [Complex.exp_im, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.neg_im, Complex.ofReal_im, neg_zero,
          Complex.I_im, mul_one, sub_zero, Complex.mul_im, add_zero,
          Real.exp_zero, one_mul, Real.sin_neg]
        exact neg_nonpos.mpr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le
      change ‖Complex.exp ((-(θ : ℂ)) * I)‖ = radialRadius (Complex.exp ((-(θ : ℂ)) * I))
      rw [radialRadius, ite_eq_right (not_lt.mpr hi)]
      simp [Complex.norm_exp, Complex.mul_re]

theorem radialDomain_frontier_isJordanCurve : TauCeti.IsJordanCurve (frontier radialDomain) := by
  rw [frontier_radialDomain]
  exact manuscript_boundary_isJordanCurve

end BelgianChocolate.SlitBoundaryGeometry