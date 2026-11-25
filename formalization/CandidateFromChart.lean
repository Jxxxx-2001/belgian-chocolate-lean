import CandidateBoundaryValues
import CandidateUpperHalfDisk
import CandidateDiskExtension

namespace BelgianChocolate.CandidateReflection
open Complex Filter Metric Set Topology
open BelgianChocolate.HarmonicComparison BelgianChocolate.ModularLambdaRatio
open BelgianChocolate.MarkedRealAxis BelgianChocolate.CandidateModularBoundary
open BelgianChocolate.SourceDiskPaths BelgianChocolate.CandidateUpperHalfDisk

theorem norm_lt_one_of_curvedEdge {w : ℂ} (hw : w ∈ curvedEdge) : ‖w‖ < 1 := by
  obtain ⟨θ, hθ, rfl⟩ := hw
  have ha : 0 < Real.sqrt (θ * (Real.pi - θ)) :=
    Real.sqrt_pos.mpr (mul_pos hθ.1 (sub_pos.mpr hθ.2))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, Complex.ofReal_im,
    zero_sub, neg_zero, Real.exp_zero, mul_one]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)

theorem cuspU_comp_diameter_data {Φ : ℂ → ℂ}
    (hn : ∀ x ∈ Ioo (-1 : ℝ) 0, Φ (x : ℂ) ∈ curvedEdge)
    (hp : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (-1 : ℝ) 0, Φ (x : ℂ) = (y : ℂ))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1 \ {0}) (him : z.im = 0) :
    ‖Φ z‖ < 1 ∧ (cuspU (Φ z)).im = 0 ∧ cuspU (Φ z) ∈ ({0,1}ᶜ : Set ℂ) := by
  have he : (z.re : ℂ) = z := Complex.ext rfl (by simpa using him.symm)
  have hr : |z.re| < 1 := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, he]
    exact mem_ball_zero_iff.mp hz.1
  have hr0 : z.re ≠ 0 := by
    intro h
    apply hz.2
    rw [← he, h, ofReal_zero]
    exact mem_singleton 0
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · have hΦ : Φ z ∈ curvedEdge := he ▸ hn z.re ⟨(abs_lt.mp hr).1, hneg⟩
    obtain ⟨hi, hs⟩ := cuspU_curvedEdge_negative hΦ
    refine ⟨norm_lt_one_of_curvedEdge hΦ, hi, ?_⟩
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor <;> intro h <;> rw [h] at hs <;> norm_num at hs
  · obtain ⟨y, hy, hΦ⟩ := hp z.re ⟨hpos, (abs_lt.mp hr).2⟩
    rw [he] at hΦ
    rw [hΦ]
    refine ⟨?_, cuspU_real_interval hy⟩
    rw [norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨hy.1, by linarith [hy.2]⟩

/-- The actual normalized univalent chart and its two marked real edges
supply all interior and ordinary-boundary candidate data. Only the cusp
limit and the cusp upper-side sign remain geometric inputs. -/
theorem marked_of_normalized_chart {t : ℝ} {Φ : ℂ → ℂ}
    (ht : 0 < t) (ht1 : t < 1)
    (hd : DifferentiableOn ℂ Φ comparisonHalfDisk)
    (hm : MapsTo Φ comparisonHalfDisk (ball 0 1))
    (hi : InjOn Φ comparisonHalfDisk) (hz : Φ ((t : ℂ) * I) = 0)
    (hc : ContinuousOn Φ ((ball 0 1 \ {0}) ∩ {z : ℂ | 0 ≤ z.im}))
    (hn : ∀ x ∈ Ioo (-1 : ℝ) 0, Φ (x : ℂ) ∈ curvedEdge)
    (hp : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (-1 : ℝ) 0, Φ (x : ℂ) = (y : ℂ))
    (hlim : Tendsto (fun z => cuspU (Φ z)) (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝 0))
    (hsign : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] 0, 0 < (cuspU (Φ z)).im) :
    MarkedCompetitor t (fillReflection (fun z => cuspU (Φ z))) ∧
      RealSymmetricOnDisk (fillReflection (fun z => cuspU (Φ z))) ∧
      (∃ d : ℝ, 0 < d ∧ HasDerivAt (fillReflection (fun z => cuspU (Φ z))) (d : ℂ) 0) ∧
      EqOn (fillReflection (fun z => cuspU (Φ z))) (fun z => cuspU (Φ z)) comparisonHalfDisk := by
  have hboundary := fun z hz him => cuspU_comp_diameter_data hn hp (z := z) hz him
  have hfullmaps : MapsTo Φ ((ball 0 1 \ {0}) ∩ {z : ℂ | 0 ≤ z.im}) {w : ℂ | ‖w‖ < 1} := by
    intro z hz
    rcases (show 0 ≤ z.im from hz.2).eq_or_lt with hzero | hpos
    · exact (hboundary z hz.1 hzero.symm).1
    · exact mem_ball_zero_iff.mp (hm ⟨hz.1.1, hpos⟩)
  have hcont : ContinuousOn (fun z => cuspU (Φ z))
      ((ball 0 1 \ {0}) ∩ {z : ℂ | 0 ≤ z.im}) :=
    cuspU_differentiableOn.continuousOn.comp hc hfullmaps
  obtain ⟨hnozero, hone, honeval, hsimple⟩ := cuspU_comp_upper_markings ht ht1 hd hm hi hz
  apply fillReflection_marked_of_upper_data ht hcont (cuspU_comp_differentiableOn hd hm)
    (fun z hz him => (hboundary z hz him).2.1) _ honeval hsimple hlim hsign
  intro z hz hzim hnz hnplus
  rcases hzim.eq_or_lt with heq | hpos
  · exact (hboundary z ⟨hz, hnz⟩ heq.symm).2.2
  · simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hnozero z ⟨hz, hpos⟩, fun h => hnplus ((hone z ⟨hz, hpos⟩).mp h)⟩

end BelgianChocolate.CandidateReflection
