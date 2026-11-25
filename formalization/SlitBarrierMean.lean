import SlitHarmonicMeasure
import Mathlib.Analysis.Complex.MeanValue

namespace BelgianChocolate.SlitHarmonicMeasure

open Complex Metric Set MeasureTheory
open BelgianChocolate.SlitBoundaryGeometry BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex
open scoped Topology

/-- A complex analytic boundary majorant bounds the centered harmonic
measure by its real part at the origin. -/
theorem mass_le_re_barrier {α : ℝ} {F H : ℂ → ℂ} {E : Set ℂ}
    (h : CenteredUnfoldedChart α F) (hE : MeasurableSet E)
    (hd : DifferentiableOn ℂ H (ball 0 1)) (hc : ContinuousOn H (closedBall 0 1))
    (hbound : ∀ ζ ∈ sphere (0 : ℂ) 1,
      E.indicator (fun _ => (1 : ℝ)) (folding α (F ζ)) ≤ (H ζ).re) :
    mass α F E ≤ (H 0).re := by
  have hi : CircleIntegrable H 0 1 := (hc.mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hir : CircleIntegrable (Complex.reCLM ∘ H) 0 1 :=
    ((continuous_re.comp_continuousOn hc).mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hm : Real.circleAverage H 0 1 = H 0 := by
    apply circleAverage_of_differentiable_on_off_countable (s := ∅) countable_empty
    · simpa using hc
    · intro z hz
      exact hd.differentiableAt (isOpen_ball.mem_nhds (by simpa using hz.1))
  rw [mass_eq_circleAverage h hE, ← hm]
  change _ ≤ Complex.reCLM (Real.circleAverage H 0 1)
  rw [← Complex.reCLM.circleAverage_comp_comm hi]
  apply Real.circleAverage_mono (circleIntegrable_physicalIndicator h hE) hir
  intro z hz
  exact hbound z (by simpa only [abs_one] using hz)

theorem norm_folded_chart_le_one {α : ℝ} {F : ℂ → ℂ} (h : CenteredUnfoldedChart α F)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : ‖folding α (F z)‖ ≤ 1 := by
  let G := folding α ∘ F
  have hG : MapsTo G (ball 0 1) (ball 0 1) := fun _ hx =>
    radialDomain_subset_ball (h.folded_interior.2.2.mapsTo hx).1
  have hc : ContinuousOn G (closedBall 0 1) :=
    (differentiable_folding α).continuous.comp_continuousOn h.closed_continuous
  have hclosed := hG.closure_of_continuousOn
    (by simpa only [closure_ball _ one_ne_zero] using hc)
  rw [closure_ball _ one_ne_zero] at hclosed
  exact mem_closedBall_zero_iff.mp (hclosed hz)

end BelgianChocolate.SlitHarmonicMeasure
