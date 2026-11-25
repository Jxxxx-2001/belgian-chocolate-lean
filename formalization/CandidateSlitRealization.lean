import CandidateFromChart
import CandidateCuspCoordinate
import MarkedCompetitorComparison

/-! Realization of the comparison candidate by reflection of its actual
modular projection. The remaining inputs are normalized slit-chart data.
-/
namespace BelgianChocolate.CandidateReflection
open Complex Filter Metric Set Topology
open BelgianChocolate.HarmonicComparison BelgianChocolate.ModularLambdaRatio
open BelgianChocolate.SlitBoundaryGeometry BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SourceDiskPaths

theorem marked_of_unfolded_slit_chart {t α : ℝ} {Φ : ℂ → ℂ}
    (ht : 0 < t) (ht1 : t < 1) (hα : -1 < α)
    (hd : DifferentiableOn ℂ Φ comparisonHalfDisk)
    (hm : MapsTo Φ comparisonHalfDisk (candidateSlit α))
    (hi : InjOn Φ comparisonHalfDisk) (hz : Φ ((t : ℂ) * I) = 0)
    (hc : ContinuousOn Φ ((ball 0 1 \ {0}) ∩ {z : ℂ | 0 ≤ z.im}))
    (hn : ∀ x ∈ Ioo (-1 : ℝ) 0, Φ (x : ℂ) ∈ BelgianChocolate.MarkedRealAxis.curvedEdge)
    (hp : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (-1 : ℝ) 0, Φ (x : ℂ) = (y : ℂ))
    (hP : Tendsto (fun z => unfolding α (Φ z)) (𝓝[{z : ℂ | 0 < z.im}] 0)
      (𝓝 ((Real.sqrt (1+α) : ℂ) * I))) :
    MarkedCompetitor t (fillReflection (fun z => cuspU (Φ z))) ∧
      RealSymmetricOnDisk (fillReflection (fun z => cuspU (Φ z))) ∧
      (∃ d : ℝ, 0 < d ∧ HasDerivAt (fillReflection (fun z => cuspU (Φ z))) (d : ℂ) 0) ∧
      EqOn (fillReflection (fun z => cuspU (Φ z))) (fun z => cuspU (Φ z)) comparisonHalfDisk := by
  have hmem : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ), Φ z ∈ candidateSlit α := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) zero_lt_one),
      self_mem_nhdsWithin] with z hz him
    exact hm ⟨hz, him⟩
  obtain ⟨hlim, hsign⟩ := cuspU_of_unfolded_upper_endpoint hα hmem hP
  exact marked_of_normalized_chart ht ht1 hd
    (fun z hz => radialDomain_subset_ball (hm hz).1) hi hz hc hn hp hlim hsign

/-- The analytic realization is now a conclusion of the geometric comparison
candidate, its univalence, slit range and marked prime-end approach. -/
theorem exists_marked_realization_of_comparisonCandidate {t α : ℝ} {Φ : ℂ → ℂ}
    (ht : 0 < t) (ht1 : t < 1) (hα : -1 < α)
    (hΦ : ComparisonCandidate t Φ) (hi : InjOn Φ comparisonHalfDisk)
    (hm : MapsTo Φ comparisonHalfDisk (candidateSlit α))
    (hP : Tendsto (fun z => unfolding α (Φ z)) (𝓝[{z : ℂ | 0 < z.im}] 0)
      (𝓝 ((Real.sqrt (1+α) : ℂ) * I))) :
    ∃ fs : ℂ → ℂ, MarkedCompetitor t fs ∧ RealSymmetricOnDisk fs ∧
      (∀ z ∈ comparisonHalfDisk, cuspU (Φ z) = fs z) ∧
      ∃ d : ℝ, 0 < d ∧ HasDerivAt fs (d : ℂ) 0 := by
  have hc : ContinuousOn Φ ((ball 0 1 \ {0}) ∩ {z : ℂ | 0 ≤ z.im}) := by
    apply hΦ.continuous.mono
    intro z hz
    rw [closure_comparisonHalfDisk]
    exact ⟨(mem_ball_zero_iff.mp hz.1.1).le, hz.2⟩
  obtain ⟨hM, hR, hD, hEq⟩ := marked_of_unfolded_slit_chart ht ht1 hα hΦ.differentiable
    hm hi hΦ.center hc hΦ.negative hΦ.positive hP
  exact ⟨_, hM, hR, fun z hz => (hEq hz).symm, hD⟩

/-- The disk threshold no longer assumes that `U ∘ Φ` has a disk realization.
That analytic assertion is supplied by the slit-chart construction above. -/
theorem disk_threshold_of_unfolded_candidate {t α : ℝ} {Φ : ℂ → ℂ}
    (ht : 0 < t) (ht1 : t < 1) (hα : -1 < α)
    (hΦ : ComparisonCandidate t Φ) (hi : InjOn Φ comparisonHalfDisk)
    (hm : MapsTo Φ comparisonHalfDisk (candidateSlit α))
    (hP : Tendsto (fun z => unfolding α (Φ z)) (𝓝[{z : ℂ | 0 < z.im}] 0)
      (𝓝 ((Real.sqrt (1+α) : ℂ) * I))) :
    t ≤ ControlWitness.witnessT ∧ t < 1/10 ∧
      {u : ℝ | 0 < u ∧ u < 1 ∧ ∃ f : ℂ → ℂ,
        MarkedCompetitor u f ∧ RealSymmetricOnDisk f} = Ico t 1 := by
  obtain ⟨fs, hfs, hr, hrep, _⟩ :=
    exists_marked_realization_of_comparisonCandidate ht ht1 hα hΦ hi hm hP
  obtain ⟨hle, hsmall, hset, _⟩ := disk_threshold_of_certified_witness ht ht1 hΦ hfs hr hrep
  exact ⟨hle, hsmall, hset⟩

end BelgianChocolate.CandidateReflection
