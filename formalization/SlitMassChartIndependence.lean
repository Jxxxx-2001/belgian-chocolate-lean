import SlitHarmonicMeasure
import UnfoldedSlitChartRotation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Angular harmonic measure does not depend on the rotation left free in
the centered Carathéodory chart. -/
namespace BelgianChocolate.SlitHarmonicMeasure
open Complex Set Metric MeasureTheory
open BelgianChocolate.SlitBoundaryGeometry

private noncomputable def angularIndicator (α : ℝ) (F : ℂ → ℂ) (E : Set ℂ) (θ : ℝ) : ℝ :=
  (physicalAngle α F ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) θ

private theorem indicator_integral {α : ℝ} {F : ℂ → ℂ} (h : CenteredUnfoldedChart α F)
    {E : Set ℂ} (hE : MeasurableSet E) :
    ∫ θ in 0..(2 * Real.pi), angularIndicator α F E θ = (volume (angularSet α F E)).toReal := by
  change (∫ θ in 0..(2 * Real.pi), (physicalAngle α F ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) θ) = _
  rw [intervalIntegral.integral_of_le (by positivity),
    setIntegral_indicator ((continuous_physicalAngle h).measurable hE),setIntegral_const]
  simp [angularSet,Measure.real_def]

private theorem indicator_periodic (α : ℝ) (F : ℂ → ℂ) (E : Set ℂ) :
    Function.Periodic (angularIndicator α F E) (2 * Real.pi) := by
  intro θ
  classical
  simp only [angularIndicator, Set.indicator_apply, mem_preimage, physicalAngle,
    periodic_circleMap (0 : ℂ) 1 θ]

/-- For every measurable physical boundary set the mass is the same in all centered charts. -/
theorem mass_chart_independent {α : ℝ} {F G : ℂ → ℂ} (hF : CenteredUnfoldedChart α F)
    (hG : CenteredUnfoldedChart α G) {E : Set ℂ} (hE : MeasurableSet E) :
    mass α F E = mass α G E := by
  obtain ⟨u,hu⟩ := hF.eqOn_rotation hG
  let a := (u : ℂ).arg
  have he : Complex.exp ((a : ℂ) * Complex.I) = (u : ℂ) := by
    simpa [a] using Complex.norm_mul_exp_arg_mul_I (u : ℂ)
  have hshift (θ : ℝ) : (u : ℂ) * circleMap 0 1 θ = circleMap 0 1 (θ + a) := by
    simp only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.ofReal_add, add_mul, Complex.exp_add,he]
    exact mul_comm _ _
  have heq (θ : ℝ) : physicalAngle α F θ = physicalAngle α G (θ + a) := by
    unfold physicalAngle
    have hθ := hu (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (zero_le_one' ℝ) θ))
    change F (circleMap 0 1 θ) = G ((u : ℂ) * circleMap 0 1 θ) at hθ
    rw [hθ,hshift]
  have hi (θ : ℝ) : angularIndicator α F E θ = angularIndicator α G E (θ + a) := by
    classical
    simp only [angularIndicator,Set.indicator_apply,mem_preimage,heq]
  unfold mass
  rw [← indicator_integral hF hE, ← indicator_integral hG hE]
  congr 1
  simp_rw [hi]
  rw [intervalIntegral.integral_comp_add_right]
  simpa [add_comm] using (indicator_periodic α G E).intervalIntegral_add_eq a 0

end BelgianChocolate.SlitHarmonicMeasure
