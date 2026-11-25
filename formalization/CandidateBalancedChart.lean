import SlitPrevertexMasses
import CandidateNormalizedChart
import BalancedParameters

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Filter Metric Topology
open BelgianChocolate.NormalizationCenter BelgianChocolate.HarmonicComparison
open BelgianChocolate.SlitHarmonicMeasure BelgianChocolate.SlitSquareRoot

private theorem measurable_curvedEdge : MeasurableSet MarkedRealAxis.curvedEdge := by
  have he : MarkedRealAxis.curvedEdge = range upperArc \ {(1 : ℂ),-1} := by
    rw [range_upperArc]
    ext z
    constructor
    · intro hz
      refine ⟨Or.inr hz,?_⟩
      obtain ⟨θ,hθ,rfl⟩ := hz
      have hi : 0 < ((Real.exp (-Real.sqrt (θ*(Real.pi-θ))) : ℂ) * cexp ((θ : ℂ)*I)).im := by
        simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero,
          Complex.exp_im, Complex.mul_I_re, neg_zero, Real.exp_zero, Complex.I_im, mul_one, one_mul]
        exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
      rintro (hz | hz)
      · rw [hz] at hi; simp at hi
      · change _ = -1 at hz
        rw [hz] at hi; simp at hi
    · exact fun hz => hz.1.resolve_left hz.2
  rw [he]
  exact (isCompact_range upperArc.continuous).isClosed.measurableSet.diff (by measurability)

private theorem measurable_slit (α : ℝ) : MeasurableSet (SlitStarConvex.negativeSlit α) :=
  ((isClosed_eq continuous_im continuous_const).inter
    ((isClosed_le continuous_const continuous_re).inter (isClosed_le continuous_re continuous_const))).measurableSet

/-- The boundary-normalized physical chart transports the two centered slit
masses to the explicit half-plane ray distribution at the preimage of zero. -/
theorem normalized_chart_ray_masses {α : ℝ} {F H : ℂ → ℂ}
    (hl : -1 < α) (hr : α < 0) (hF : CenteredUnfoldedChart α F)
    (hH : UnfoldedHalfPlaneChart α H) (hQ : H (-2) = lowerBankEnd α)
    (hR : H 2 = rightEnd α) {p : ℂ} (hp : p ∈ comparisonHalfDisk)
    (hz : physicalDiskChart α H p = 0) :
    a α F = leftWeight p ∧ b α F = rightWeight p ∧ d α F = arcWeight p := by
  let w := joukowski p
  let c := -w.re
  let s := -w.im
  have hp' : p ∈ UpperHalfDisk.domain := by simpa only [comparisonHalfDisk_eq_norm,UpperHalfDisk.domain] using hp
  have hp0 : p ≠ 0 := by rintro rfl; exact (lt_irrefl 0) hp'.2
  have hs : 0 < s := neg_pos.mpr (joukowski_mapsTo hp')
  have hw : (s : ℂ)*I + c = -w := by
    apply Complex.ext <;> simp [s,c,Complex.mul_re,Complex.mul_im]
  let G := fun z : ℂ => H ((s : ℂ)*z + c)
  have hG : UnfoldedHalfPlaneChart α G := hH.precomp_affine hs
  have h0 : G I = unfolding α 0 := by
    change H ((s : ℂ)*I+c) = _
    rw [hw, ← hz]
    rw [physicalDiskChart_of_ne_zero hp0,rawPhysicalChart,unfolding_folding_of_re_pos]
    exact (hH.interior_bij.mapsTo (negJ_bij.mapsTo hp)).1
  have hC := hG.centered_disk_chart hl hr h0
  let q := (-2-c)/s
  let r := (2-c)/s
  have hq : G (q : ℂ) = lowerBankEnd α := by
    change H _ = _
    convert hQ using 2
    dsimp [q]; push_cast; field_simp [hs.ne']; ring
  have hr' : G (r : ℂ) = rightEnd α := by
    change H _ = _
    convert hR using 2
    dsimp [r]; push_cast; field_simp [hs.ne']; ring
  obtain ⟨ha,hb⟩ := centered_prevertex_masses hl hr hG hq hr'
  have hA : a α F = leftWeight p := by
    calc
      _ = a α (halfPlaneDiskChart α G) := mass_chart_independent hF hC measurable_curvedEdge
      _ = _ := by
        rw [ha]
        unfold leftWeight rayCDF cayleyAngle
        have he : (-2 - (joukowski p).re) / -(joukowski p).im = -r := by dsimp [r,c,s,w]; ring
        rw [he, Real.arctan_neg]
        field_simp [Real.pi_ne_zero]; ring
  have hB : b α F = rightWeight p := by
    calc
      _ = b α (halfPlaneDiskChart α G) := mass_chart_independent hF hC (measurable_slit α)
      _ = _ := by
        rw [hb]
        unfold rightWeight rayCDF cayleyAngle
        have he : (2 - (joukowski p).re) / -(joukowski p).im = -q := by dsimp [q,c,s,w]; ring
        rw [he, Real.arctan_neg]
        field_simp [Real.pi_ne_zero]; ring
  refine ⟨hA,hB,?_⟩
  have hsum := a_add_b_add_d hF hl hr
  rw [hA,hB] at hsum
  unfold leftWeight rightWeight at hsum
  unfold arcWeight
  linarith

theorem exists_candidate_of_balanced_slit {α : ℝ} {F : ℂ → ℂ}
    (hl : -1 < α) (hr : α < 0) (hF : CenteredUnfoldedChart α F) (hbal : a α F = b α F) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ Φ : ℂ → ℂ, BijOn Φ comparisonHalfDisk (candidateSlit α) ∧
      ComparisonCandidate t Φ ∧
      Tendsto (fun z => unfolding α (Φ z)) (𝓝[{z : ℂ | 0 < z.im}] 0)
        (𝓝 ((Real.sqrt (1+α) : ℂ)*I)) ∧
      d α F = (4/Real.pi)*Real.arctan t ∧
      Real.cos ((Real.pi/2)*d α F) = (1-t^2)/(1+t^2) := by
  obtain ⟨H,hH,hQ,hR,hbank,hlower,hupper⟩ := exists_normalized_physical_chart hl hr
  have hbij := physicalDiskChart_bij hH
  have hz : (0 : ℂ) ∈ candidateSlit α := by
    refine ⟨zero_mem_radialDomain, ?_⟩
    intro h
    exact hr.not_ge (by simpa using h.2.2)
  obtain ⟨p,hp,h0⟩ := hbij.surjOn hz
  obtain ⟨ha,hb,hd⟩ := normalized_chart_ray_masses hl hr hF hH hQ hR hp h0
  have hp' : p ∈ UpperHalfDisk.domain := by simpa only [comparisonHalfDisk_eq_norm,UpperHalfDisk.domain] using hp
  obtain ⟨t,ht,hpt,hat,hcos⟩ := exact_marked_parameters hp' (ha.symm.trans (hbal.trans hb))
  refine ⟨t,ht,_,hbij,physicalDiskChart_comparisonCandidate hl hr hH hR hbank hlower hupper
    (by rw [hpt] at h0; exact h0),hH.unfolding_folded_extension_at_zero,hd.trans hat,?_⟩
  rwa [hd]

end BelgianChocolate.SlitBoundaryGeometry

