import BalancedParameters
import BalancedSlitRoot
import CandidateBalancedChart
import CandidateSlitRealization
import ControllerCandidateThreshold

/-! The original disk and finite-controller problems at the slit threshold. -/

namespace BelgianChocolate

open Complex Filter Metric Set Topology
open CandidateReflection ControlWitness HarmonicComparison
open NormalizationCenter SlitBoundaryGeometry SlitHarmonicMeasure SlitSquareRoot
open SourceDiskPaths

def DiskFeasibleParameters : Set ℝ :=
  {t | 0 < t ∧ t < 1 ∧ ∃ f : ℂ → ℂ, MarkedCompetitor t f ∧ RealSymmetricOnDisk f}

def ControllerFeasibleParameters : Set ℝ :=
  {δ | 0 < δ ∧ δ < 1 ∧ Feasible δ}

/-- The geometric parameter, the disk threshold and the strict finite-controller
threshold in the original problem. -/
structure ThresholdConclusion (α t : ℝ) (Φ fs : ℂ → ℂ) : Prop where
  balanced : IsBalanced α
  t_mem : t ∈ Ioo (0 : ℝ) 1
  chart : ComparisonCandidate t Φ
  chart_bij : BijOn Φ comparisonHalfDisk (candidateSlit α)
  marked : MarkedCompetitor t fs
  symmetric : RealSymmetricOnDisk fs
  modular_representation : ∀ z ∈ comparisonHalfDisk, ModularLambdaRatio.cuspU (Φ z) = fs z
  positive_derivative : ∃ k : ℝ, 0 < k ∧ HasDerivAt fs (k : ℂ) 0
  t_formula : t = Real.tan (Real.pi * lowerMass α / 4)
  delta_formula : Real.cos (Real.pi * lowerMass α / 2) = (1 - t ^ 2) / (1 + t ^ 2)
  disk_interval : DiskFeasibleParameters = Ico t 1
  disk_unique : ∀ f : ℂ → ℂ, MarkedCompetitor t f → RealSymmetricOnDisk f →
    ∀ k : ℝ, HasDerivAt f (k : ℂ) 0 → 0 < k → EqOn f fs (ball 0 1)
  controller_interval : ControllerFeasibleParameters = Ioo 0 (Real.cos (Real.pi * lowerMass α / 2))
  endpoint_excluded : ¬ Feasible (Real.cos (Real.pi * lowerMass α / 2))
  controller_supremum : sSup ControllerFeasibleParameters = Real.cos (Real.pi * lowerMass α / 2)

/-- The disk comparison, controller realization and endpoint obstruction applied
to a balanced slit chart whose center has the exact harmonic-measure formula. -/
theorem threshold_of_balanced_chart {α t : ℝ} {Φ : ℂ → ℂ}
    (hα : IsBalanced α) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hΦ : ComparisonCandidate t Φ)
    (hbij : BijOn Φ comparisonHalfDisk (candidateSlit α))
    (hP : Tendsto (fun z => unfolding α (Φ z)) (𝓝[{z : ℂ | 0 < z.im}] 0)
      (𝓝 ((Real.sqrt (1 + α) : ℂ) * I)))
    (hmass : lowerMass α = (4 / Real.pi) * Real.arctan t) :
    ∃ fs : ℂ → ℂ, ThresholdConclusion α t Φ fs := by
  obtain ⟨fs, hmarked, hreal, hrep, hderiv⟩ :=
    exists_marked_realization_of_comparisonCandidate ht.1 ht.2 hα.1.1 hΦ
      hbij.injOn hbij.mapsTo hP
  obtain ⟨_, hsmall, hdisk, hrigid⟩ :=
    disk_threshold_of_certified_witness ht.1 ht.2 hΦ hmarked hreal hrep
  obtain ⟨hfinite, hsup⟩ := controller_threshold_of_candidate ht.1 ht.2 hΦ hmarked hreal hrep
  have htExact : Real.pi * lowerMass α / 4 = Real.arctan t := by
    rw [hmass]
    field_simp [Real.pi_ne_zero]
  have hδExact : Real.cos (Real.pi * lowerMass α / 2) = controllerParameter t := by
    rw [show Real.pi * lowerMass α / 2 = (Real.pi / 2) *
      NormalizationCenter.arcWeight (UpperHalfDisk.puncture t) by
        rw [hmass, arcWeight_puncture ht]
        ring]
    exact cos_arcWeight_puncture ht
  refine ⟨fs, hα, ht, hΦ, hbij, hmarked, hreal, hrep, hderiv, ?_, hδExact, hdisk,
    fun f hf hr => (hrigid f hf hr).1, ?_, ?_, ?_⟩
  · rw [htExact, Real.tan_arctan]
  · rw [hδExact]
    exact hfinite
  · rw [hδExact]
    exact controller_endpoint_excluded_of_candidate ht.1 ht.2 hsmall.le hΦ
  · rw [hδExact]
    exact hsup

/-- Every balanced physical slit yields the full threshold conclusion
for the original problems. -/
theorem threshold_of_balanced_slit {α : ℝ} (hα : IsBalanced α) :
    ∃ (t : ℝ) (Φ fs : ℂ → ℂ), ThresholdConclusion α t Φ fs := by
  obtain ⟨t, ht, Φ, hbij, hΦ, hP, hmass, _⟩ :=
    exists_candidate_of_balanced_slit hα.1.1 hα.1.2 (centeredChart_spec hα.1) hα.2
  obtain ⟨fs, hresult⟩ := threshold_of_balanced_chart hα ht hΦ hbij hP hmass
  exact ⟨t, Φ, fs, hresult⟩

/-- The Belgian Chocolate threshold. The unique balanced slit determines
the closed disk threshold, the open finite-controller threshold, and its
unattained supremum. -/
theorem belgian_chocolate_threshold :
    ∃ (α t : ℝ) (Φ fs : ℂ → ℂ), ThresholdConclusion α t Φ fs ∧
      ∀ β : ℝ, IsBalanced β → β = α := by
  obtain ⟨α, hα, huniq⟩ := existsUnique_balanced_slit
  obtain ⟨t, Φ, fs, hthreshold⟩ := threshold_of_balanced_slit hα
  exact ⟨α, t, Φ, fs, hthreshold, huniq⟩

end BelgianChocolate
