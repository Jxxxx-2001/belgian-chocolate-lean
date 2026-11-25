import ComparisonSourceChart
import CuspLiftFilling

/-! Interior analytic data of the candidate `U ∘ Φ`, derived from its actual
univalent half-disk chart. Boundary reflection is handled separately. -/
namespace BelgianChocolate.CandidateUpperHalfDisk
open Complex Metric Set Topology
open BelgianChocolate.HarmonicComparison BelgianChocolate.ModularLambdaRatio

theorem cuspU_comp_differentiableOn {Φ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ Φ comparisonHalfDisk)
    (hm : MapsTo Φ comparisonHalfDisk (ball 0 1)) :
    DifferentiableOn ℂ (fun z => cuspU (Φ z)) comparisonHalfDisk :=
  cuspU_differentiableOn.comp hd (fun _ hz => mem_ball_zero_iff.mp (hm hz))

/-- A univalent centered half-disk chart gives exactly one simple one-point
of `U ∘ Φ` in the upper half-disk, and gives no zero there. -/
theorem cuspU_comp_upper_markings {t : ℝ} {Φ : ℂ → ℂ}
    (ht : 0 < t) (ht1 : t < 1)
    (hd : DifferentiableOn ℂ Φ comparisonHalfDisk)
    (hm : MapsTo Φ comparisonHalfDisk (ball 0 1))
    (hi : InjOn Φ comparisonHalfDisk) (hc : Φ ((t : ℂ) * I) = 0) :
    (∀ z ∈ comparisonHalfDisk, cuspU (Φ z) ≠ 0) ∧
      (∀ z ∈ comparisonHalfDisk, cuspU (Φ z) = 1 ↔ z = (t : ℂ) * I) ∧
      cuspU (Φ ((t : ℂ) * I)) = 1 ∧
      ∃ d, HasDerivAt (fun z => cuspU (Φ z)) d ((t : ℂ) * I) ∧ d ≠ 0 := by
  have hp := central_point_mem_comparisonHalfDisk ht ht1
  refine ⟨fun z hz => cuspU_ne_zero (mem_ball_zero_iff.mp (hm hz)), ?_, ?_, ?_⟩
  · intro z hz
    rw [cuspU_eq_one_iff (mem_ball_zero_iff.mp (hm hz))]
    constructor
    · intro he
      exact hi hz hp (he.trans hc.symm)
    · rintro rfl
      exact hc
  · rw [hc, cuspU_zero]
  · have hΦ := (hd.differentiableAt (isOpen_comparisonHalfDisk.mem_nhds hp)).hasDerivAt
    have hΦne := TauCeti.deriv_ne_zero_of_injOn hd isOpen_comparisonHalfDisk hi hp
    refine ⟨16 * deriv Φ ((t : ℂ) * I), ?_, mul_ne_zero (by norm_num) hΦne⟩
    exact (hc.symm ▸ cuspU_hasDerivAt_zero).comp _ hΦ

end BelgianChocolate.CandidateUpperHalfDisk
