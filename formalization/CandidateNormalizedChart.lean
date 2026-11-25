import CandidateJoukowskiAssembly
import UnfoldedSlitSourceContinuity

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Filter Metric Set Topology
open BelgianChocolate.NormalizationCenter BelgianChocolate.HarmonicComparison
open BelgianChocolate.SlitSquareRoot

noncomputable def physicalDiskChart (α : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  folding α (diskUnfoldedExtension α F z)

theorem physicalDiskChart_of_ne_zero {α : ℝ} {F : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    physicalDiskChart α F z = rawPhysicalChart α F z := by
  rw [physicalDiskChart, diskUnfoldedExtension_of_ne_zero _ _ hz]
  rfl

private theorem halfDisk_ne_zero {z : ℂ} (hz : z ∈ comparisonHalfDisk) : z ≠ 0 := by
  rintro rfl
  exact (lt_irrefl (0 : ℝ)) (by simpa only [Set.mem_ofPred_eq, Complex.zero_im] using hz.2)

theorem physicalDiskChart_bij {α : ℝ} {F : ℂ → ℂ} (hF : UnfoldedHalfPlaneChart α F) :
    BijOn (physicalDiskChart α F) comparisonHalfDisk (candidateSlit α) :=
  (rawPhysicalChart_bij hF).congr (fun _ hz => (physicalDiskChart_of_ne_zero (halfDisk_ne_zero hz)).symm)

theorem physicalDiskChart_holo {α : ℝ} {F : ℂ → ℂ} (hF : UnfoldedHalfPlaneChart α F) :
    DifferentiableOn ℂ (physicalDiskChart α F) comparisonHalfDisk :=
  (rawPhysicalChart_holo hF).congr (fun _ hz => physicalDiskChart_of_ne_zero (halfDisk_ne_zero hz))

theorem physicalDiskChart_continuous {α : ℝ} {F : ℂ → ℂ} (hF : UnfoldedHalfPlaneChart α F) :
    ContinuousOn (physicalDiskChart α F) (closure comparisonHalfDisk) :=
  (differentiable_folding α).continuous.comp_continuousOn hF.continuousOn_diskUnfoldedExtension

/-- The three-point-normalized target chart, composed with `-J`, gives every
comparison boundary condition. The sole remaining normalization is its center. -/
theorem physicalDiskChart_comparisonCandidate {t α : ℝ} {F : ℂ → ℂ}
    (hl : -1 < α) (hr : α < 0) (hF : UnfoldedHalfPlaneChart α F)
    (hR : F 2 = rightEnd α)
    (hbank : ∀ x : ℝ, x < -2 → ∃ y ∈ Ioo (-1 : ℝ) 0, folding α (F (x : ℂ)) = (y : ℂ))
    (hlower : ∀ x ∈ Ioo (-2 : ℝ) 2,
      ‖folding α (F (x : ℂ))‖ = 1 ∧ (folding α (F (x : ℂ))).im < 0)
    (hupper : ∀ x : ℝ, 2 < x → folding α (F (x : ℂ)) ∈ MarkedRealAxis.curvedEdge)
    (hcenter : physicalDiskChart α F ((t : ℂ) * I) = 0) :
    ComparisonCandidate t (physicalDiskChart α F) where
  differentiable := physicalDiskChart_holo hF
  maps := fun z hz => radialDomain_subset_ball ((physicalDiskChart_bij hF).mapsTo hz).1
  center := hcenter
  continuous := physicalDiskChart_continuous hF
  negative := by
    intro x hx
    rw [physicalDiskChart_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.2.ne)]
    exact rawPhysicalChart_negative hupper hx
  positive := by
    intro x hx
    rw [physicalDiskChart_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.1.ne')]
    exact rawPhysicalChart_positive hbank hx
  outer := by
    intro z hz
    have hn : z ≠ 0 := by
      intro h
      have hv := hz.1
      rw [h, norm_zero] at hv
      norm_num at hv
    rw [physicalDiskChart_of_ne_zero hn]
    exact rawPhysicalChart_outer hlower hz
  endValues := by
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · left
      rw [physicalDiskChart_of_ne_zero (by norm_num : (-1 : ℂ) ≠ 0), rawPhysicalChart,
        joukowski_neg_one, neg_neg, hR, folding_rightEnd hl hr]
    · right
      rw [physicalDiskChart, diskUnfoldedExtension_zero, folding_upperBankEnd hl hr]

/-- For every slit parameter, all geometric data needed by the comparison are
constructed. Only locating the center on the source imaginary axis is left. -/
theorem exists_normalized_comparison_chart {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    ∃ Φ : ℂ → ℂ, BijOn Φ comparisonHalfDisk (candidateSlit α) ∧
      (∀ t : ℝ, Φ ((t : ℂ) * I) = 0 → ComparisonCandidate t Φ) ∧
      Tendsto (fun z => unfolding α (Φ z)) (𝓝[{z : ℂ | 0 < z.im}] 0)
        (𝓝 ((Real.sqrt (1+α) : ℂ) * I)) := by
  obtain ⟨F,hF,_,hR,hbank,hlower,hupper⟩ := exists_normalized_physical_chart hl hr
  refine ⟨physicalDiskChart α F, physicalDiskChart_bij hF,
    fun t hcenter => physicalDiskChart_comparisonCandidate hl hr hF hR hbank hlower hupper hcenter, ?_⟩
  exact hF.unfolding_folded_extension_at_zero

end BelgianChocolate.SlitBoundaryGeometry

