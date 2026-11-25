import UnfoldedSlitPrimeEnds
import SlitBankOrientation
import TauCeti.Analysis.Complex.Conformal.Jordan.UpperHalfPlane
import Mathlib.Analysis.SpecificLimits.RCLike

/-! A boundary-normalized upper half-plane chart. Its prevertex order is fixed
by the nonnegative boundary derivative along the straight slit bank. -/
namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Metric Filter Topology Bornology
open scoped unitInterval
open BelgianChocolate.SlitSquareRoot

structure UnfoldedHalfPlaneChart (α : ℝ) (F : ℂ → ℂ) : Prop where
  cont : ContinuousOn F {z : ℂ | 0 ≤ z.im}
  holo : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet
  interior_bij : BijOn F UpperHalfPlane.upperHalfPlaneSet (unfoldedDomain α)
  closed_bij : BijOn F {z : ℂ | 0 ≤ z.im} (closure (unfoldedDomain α) \ {upperBankEnd α})
  boundary_bij : BijOn F {z : ℂ | z.im = 0} (frontier (unfoldedDomain α) \ {upperBankEnd α})
  at_infty : Tendsto F (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 (upperBankEnd α))

theorem exists_unfoldedHalfPlaneChart {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    ∃ F, UnfoldedHalfPlaneChart α F := by
  have hJ := unfoldedDomain_isJordanDomain hl hr
  obtain ⟨F,hc,hd,hi,hb,hf,ht⟩ :=
    TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier
      hJ.isOpen hJ.isConnected hJ.isBounded hJ.isJordanCurve_frontier (upperBankEnd_mem_frontier hl hr)
  exact ⟨F,hc,hd,hi,hb,hf,ht⟩

theorem UnfoldedHalfPlaneChart.real_prevertex {α : ℝ} {F : ℂ → ℂ} (h : UnfoldedHalfPlaneChart α F)
    {p : ℂ} (hp : p ∈ frontier (unfoldedDomain α)) (hne : p ≠ upperBankEnd α) :
    ∃ x : ℝ, F (x : ℂ) = p := by
  obtain ⟨z,hz,he⟩ := h.boundary_bij.surjOn ⟨hp,hne⟩
  exact ⟨z.re, by rw [show (z.re : ℂ) = z from Complex.ext (by simp) (by simpa using hz.symm), he]⟩

private theorem rightEnd_re_pos {α : ℝ} (hr : α < 0) : 0 < (rightEnd α).re :=
  Real.sqrt_pos.mpr (by linarith)

private theorem zero_mem_bank {α : ℝ} (hl : -1 < α) : (0 : ℂ) ∈ range (bankPath α) := by
  rw [range_bankPath hl]; simp

private theorem rightEnd_not_bank {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    rightEnd α ∉ range (bankPath α) := by
  rw [range_bankPath hl]
  exact fun h ↦ (rightEnd_re_pos hr).ne' h.1

private theorem continuous_real_trace {F : ℂ → ℂ} (h : ContinuousOn F {z : ℂ | 0 ≤ z.im}) :
    Continuous (fun x : ℝ ↦ F (x : ℂ)) :=
  h.comp_continuous continuous_ofReal (fun _ ↦ by simp)

/-- A connected real boundary interval avoiding the lower bank end cannot
meet both the outer path and the bank segment. Infinity is the upper bank end. -/
theorem UnfoldedHalfPlaneChart.no_cross {α : ℝ} {F : ℂ → ℂ}
    (h : UnfoldedHalfPlaneChart α F) (hl : -1 < α) (hr : α < 0)
    {q : ℝ} (hq : F (q : ℂ) = lowerBankEnd α)
    {S : Set ℝ} (hS : IsPreconnected S) (hqS : q ∉ S)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hao : F (a : ℂ) ∈ range (liftedOuter hl hr)) (hbb : F (b : ℂ) ∈ range (bankPath α)) :
    False := by
  let f : ℝ → ℂ := fun t ↦ F (t : ℂ)
  have him := hS.image f (continuous_real_trace h.cont).continuousOn
  have ho : IsClosed (range (liftedOuter hl hr)) := (isCompact_range (liftedOuter hl hr).continuous).isClosed
  have hv : IsClosed (range (bankPath α)) := (isCompact_range (bankPath α).continuous).isClosed
  have hsub : f '' S ⊆ range (liftedOuter hl hr) ∪ range (bankPath α) := by
    rintro _ ⟨t,ht,rfl⟩
    have hfr := (h.boundary_bij.mapsTo (show (t : ℂ) ∈ {z : ℂ | z.im = 0} from by simp)).1
    rwa [frontier_unfoldedDomain hl hr] at hfr
  obtain ⟨w,⟨t,ht,rfl⟩,hw⟩ := isPreconnected_closed_iff.mp him _ _ ho hv hsub
    ⟨_, ⟨a,ha,rfl⟩,hao⟩ ⟨_, ⟨b,hb,rfl⟩,hbb⟩
  rw [liftedOuter_bankPath_inter] at hw
  have htR : (t : ℂ) ∈ {z : ℂ | z.im = 0} := by simp
  rcases hw with hP | hQ
  · exact (h.boundary_bij.mapsTo htR).2 hP
  · have he : (t : ℂ) = (q : ℂ) :=
      h.boundary_bij.injOn htR (by simp) (hQ.trans hq.symm)
    exact hqS ((Complex.ofReal_inj.mp he) ▸ ht)

theorem UnfoldedHalfPlaneChart.prevertex_order {α : ℝ} {F : ℂ → ℂ}
    (h : UnfoldedHalfPlaneChart α F) (hl : -1 < α) (hr : α < 0)
    {q r : ℝ} (hq : F (q : ℂ) = lowerBankEnd α) (hright : F (r : ℂ) = rightEnd α) :
    q < r := by
  have sqpos : 0 < Real.sqrt (1 + α) := Real.sqrt_pos.mpr (by linarith)
  have hPQ : upperBankEnd α ≠ 0 := by
    simp [upperBankEnd, sqpos.ne']
  have hQ0 : lowerBankEnd α ≠ 0 := by
    simp [lowerBankEnd, sqpos.ne']
  have hRb := rightEnd_not_bank hl hr
  have hQb : lowerBankEnd α ∈ range (bankPath α) := ⟨1,(bankPath α).target⟩
  have hRo : F (r : ℂ) ∈ range (liftedOuter hl hr) := by
    rw [hright, range_liftedOuter]
    exact Or.inl ⟨0,(liftedUpper hl hr).source⟩
  have hz : (0 : ℂ) ∈ frontier (unfoldedDomain α) := by
    rw [frontier_unfoldedDomain hl hr]; exact Or.inr (zero_mem_bank hl)
  obtain ⟨m,hm⟩ := h.real_prevertex hz hPQ.symm
  have hmB : F (m : ℂ) ∈ range (bankPath α) := hm ▸ zero_mem_bank hl
  by_contra! hqr
  have hrq : r < q := lt_of_le_of_ne hqr (by
    rintro rfl
    exact hRb ((hright.symm.trans hq).symm ▸ hQb))
  have hqm : q < m := by
    by_contra! hmq
    rcases hmq.lt_or_eq with hm' | he
    · exact h.no_cross hl hr hq isPreconnected_Iio (by simp) hrq hm' hRo hmB
    · subst m; exact hQ0 (hq.symm.trans hm)
  have hbank (t : ℝ) (ht : q < t) : F (t : ℂ) ∈ range (bankPath α) := by
    have hf := (h.boundary_bij.mapsTo (show (t : ℂ) ∈ {z : ℂ | z.im = 0} from by simp)).1
    rw [frontier_unfoldedDomain hl hr] at hf
    exact hf.resolve_left fun ho ↦ h.no_cross hl hr hq isPreconnected_Ioi (by simp) ht hqm ho hmB
  let g : ℂ → ℂ := fun z ↦ Complex.I * F z
  have hmono : MonotoneOn (fun t : ℝ ↦ (g (t : ℂ)).re) (Ioi q) := by
    apply monotoneOn_real_boundary isOpen_Ioi (convex_Ioi _)
    · exact continuousOn_const.mul h.cont
    · exact h.holo.const_mul Complex.I
    · intro z hzi
      simpa [g, Complex.mul_im] using (h.interior_bij.mapsTo hzi).1.le
    · intro t ht
      have hb := hbank t ht
      rw [range_bankPath hl] at hb
      simpa [g, Complex.mul_im] using hb.1
  have hrealTop : Tendsto (fun t : ℝ ↦ (t : ℂ)) atTop (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) :=
    tendsto_inf.mpr ⟨RCLike.tendsto_ofReal_atTop_cobounded ℂ,
      tendsto_principal.mpr (Eventually.of_forall fun _ ↦ by simp)⟩
  have hlim : Tendsto (fun t : ℝ ↦ (g (t : ℂ)).re) atTop (𝓝 ((Complex.I * upperBankEnd α).re)) :=
    (continuous_re.comp (continuous_const.mul continuous_id)).continuousAt.tendsto.comp
      (h.at_infty.comp hrealTop)
  have hineq : 0 ≤ (Complex.I * upperBankEnd α).re := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop m] with t ht
    have he := hmono hqm (hqm.trans_le ht) ht
    simpa [g, hm] using he
  simp [upperBankEnd, Complex.mul_re] at hineq
  linarith

end BelgianChocolate.SlitBoundaryGeometry
