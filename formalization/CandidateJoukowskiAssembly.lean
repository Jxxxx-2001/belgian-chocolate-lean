import UnfoldedSlitPhysicalSides
import JoukowskiBoundary
import CandidateSlitRealization

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Filter Metric Set Topology
open BelgianChocolate.NormalizationCenter BelgianChocolate.HarmonicComparison
open BelgianChocolate.SlitSquareRoot

theorem negJ_bij : BijOn (fun z => -joukowski z) comparisonHalfDisk
    UpperHalfPlane.upperHalfPlaneSet := by
  have he : comparisonHalfDisk = BelgianChocolate.UpperHalfDisk.domain := comparisonHalfDisk_eq_norm
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    change 0 < (-joukowski z).im
    rw [neg_im, neg_pos]
    exact joukowski_mapsTo hz
  · intro z hz w hw h
    exact joukowski_injOn hz hw (neg_injective h)
  · intro w hw
    have hn : -w ∈ lowerHalfPlane := by
      change (-w).im < 0
      rw [neg_im]
      exact neg_neg_of_pos hw
    obtain ⟨z, hz, he⟩ := joukowski_surjOn hn
    exact ⟨z, hz, by change -joukowski z = w; rw [he, neg_neg]⟩

theorem negJ_holo : DifferentiableOn ℂ (fun z => -joukowski z) comparisonHalfDisk := by
  rw [comparisonHalfDisk_eq_norm]
  exact differentiableOn_joukowski.neg

noncomputable def rawPhysicalChart (α : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  folding α (F (-joukowski z))

theorem rawPhysicalChart_bij {α : ℝ} {F : ℂ → ℂ} (hF : UnfoldedHalfPlaneChart α F) :
    BijOn (rawPhysicalChart α F) comparisonHalfDisk (candidateSlit α) :=
  (folding_bijOn_unfoldedDomain α).comp (hF.interior_bij.comp negJ_bij)

theorem rawPhysicalChart_holo {α : ℝ} {F : ℂ → ℂ} (hF : UnfoldedHalfPlaneChart α F) :
    DifferentiableOn ℂ (rawPhysicalChart α F) comparisonHalfDisk :=
  (differentiable_folding α).comp_differentiableOn (hF.holo.comp negJ_holo negJ_bij.mapsTo)

theorem rawPhysicalChart_negative {α : ℝ} {F : ℂ → ℂ}
    (hside : ∀ x : ℝ, 2 < x → folding α (F (x : ℂ)) ∈ MarkedRealAxis.curvedEdge)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 0) :
    rawPhysicalChart α F (x : ℂ) ∈ MarkedRealAxis.curvedEdge := by
  have hj : joukowski (x : ℂ) ∈ Complex.ofReal '' Iio (-2 : ℝ) := by
    rw [← image_joukowski_negDiameter]
    exact mem_image_of_mem _ ⟨x, hx, rfl⟩
  obtain ⟨y,hy,he⟩ := hj
  unfold rawPhysicalChart
  rw [← he, ← ofReal_neg]
  exact hside (-y) (by change y < -2 at hy; linarith)

theorem rawPhysicalChart_positive {α : ℝ} {F : ℂ → ℂ}
    (hside : ∀ x : ℝ, x < -2 → ∃ y ∈ Ioo (-1 : ℝ) 0, folding α (F (x : ℂ)) = (y : ℂ))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∃ y ∈ Ioo (-1 : ℝ) 0, rawPhysicalChart α F (x : ℂ) = (y : ℂ) := by
  have hj : joukowski (x : ℂ) ∈ Complex.ofReal '' Ioi (2 : ℝ) := by
    rw [← image_joukowski_posDiameter]
    exact mem_image_of_mem _ ⟨x, hx, rfl⟩
  obtain ⟨y,hy,he⟩ := hj
  unfold rawPhysicalChart
  rw [← he, ← ofReal_neg]
  exact hside (-y) (by change 2 < y at hy; linarith)

theorem rawPhysicalChart_outer {α : ℝ} {F : ℂ → ℂ}
    (hside : ∀ x ∈ Ioo (-2 : ℝ) 2,
      ‖folding α (F (x : ℂ))‖ = 1 ∧ (folding α (F (x : ℂ))).im < 0) :
    MapsTo (rawPhysicalChart α F) comparisonOuterArc {p | ‖p‖ = 1 ∧ p.im < 0} := by
  intro z hz
  have hj : joukowski z ∈ Complex.ofReal '' Ioo (-2 : ℝ) 2 := by
    rw [← image_joukowski_outerArc]
    exact mem_image_of_mem _ hz
  obtain ⟨y,hy,he⟩ := hj
  change ‖folding α (F (-joukowski z))‖ = 1 ∧ (folding α (F (-joukowski z))).im < 0
  rw [← he, ← ofReal_neg]
  exact hside (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩

end BelgianChocolate.SlitBoundaryGeometry
