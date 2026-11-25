import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Mean-value formula for bounded real parts with almost-everywhere
radial boundary limits. -/

namespace BelgianChocolate.SlitHarmonicMeasure

open Complex Filter MeasureTheory Metric Set
open scoped Topology

theorem circleAverage_eq_re_of_radial_limits {H : ℂ → ℂ} {g : ℂ → ℝ} {M : ℝ}
    (hH : DifferentiableOn ℂ H (ball 0 1))
    (hbound : ∀ z ∈ ball 0 1, ‖(H z).re‖ ≤ M)
    (hlim : ∀ᵐ θ ∂volume.restrict (Ioc 0 (2 * Real.pi)),
      Tendsto (fun r : ℝ => (H (circleMap 0 r θ)).re) (𝓝[<] (1 : ℝ))
        (𝓝 (g (circleMap 0 1 θ)))) :
    Real.circleAverage g 0 1 = (H 0).re := by
  have hradius : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one),
      self_mem_nhdsWithin] with r hr₀ hr₁
    exact ⟨hr₀, hr₁⟩
  have hpt {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (θ : ℝ) : circleMap 0 r θ ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, abs_of_pos hr.1] using hr.2
  let μ := volume.restrict (Ioc 0 (2 * Real.pi))
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hint : Tendsto (fun r : ℝ => ∫ θ, (H (circleMap 0 r θ)).re ∂μ) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ θ, g (circleMap 0 1 θ) ∂μ)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    · filter_upwards [hradius] with r hr
      have hc : Continuous (fun θ : ℝ => (H (circleMap 0 r θ)).re) :=
        continuous_re.comp (hH.continuousOn.comp_continuous (by fun_prop [circleMap]) (hpt hr))
      exact hc.aestronglyMeasurable
    · filter_upwards [hradius] with r hr
      exact ae_of_all μ fun θ => hbound _ (hpt hr θ)
    · exact integrable_const M
    · exact hlim
  have hmean {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
      Real.circleAverage (fun z => (H z).re) 0 r = (H 0).re := by
    have hclosed : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
      intro z hz
      have hsmall : |r| < 1 := by simpa only [abs_of_pos hr.1] using hr.2
      exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hsmall)
    have hc := hH.continuousOn.mono hclosed
    have hI := (hc.mono sphere_subset_closedBall).circleIntegrable (abs_nonneg r)
    have hI' : CircleIntegrable H 0 r := by simpa [abs_of_pos hr.1] using hI
    have he : Real.circleAverage H 0 r = H 0 := by
      apply circleAverage_of_differentiable_on_off_countable (s := ∅) countable_empty hc
      intro z hz
      apply hH.differentiableAt (isOpen_ball.mem_nhds (hclosed _))
      exact ball_subset_closedBall hz.1
    change Real.circleAverage (Complex.reCLM ∘ H) 0 r = _
    rw [Complex.reCLM.circleAverage_comp_comm hI', he]
    rfl
  have hav : Tendsto (fun r : ℝ => Real.circleAverage (fun z => (H z).re) 0 r)
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.circleAverage g 0 1)) := by
    simpa [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity :
      (0 : ℝ) ≤ 2 * Real.pi), μ] using tendsto_const_nhds.mul hint
  exact tendsto_nhds_unique hav (tendsto_const_nhds.congr' (hradius.mono fun _ hr => (hmean hr).symm))

/-- A countable exceptional set on the circle has zero angular measure. -/
theorem ae_circleMap_not_mem_of_countable {E : Set ℂ} (hE : E.Countable) :
    ∀ᵐ θ ∂volume.restrict (Ioc 0 (2 * Real.pi)), circleMap 0 1 θ ∉ E := by
  have h := (hE.preimage_circleMap (0 : ℂ) one_ne_zero).measure_zero
    (volume.restrict (Ioc 0 (2 * Real.pi)))
  exact ae_iff.mpr (by simpa only [not_not, preimage] using h)

/-- The same mean formula when ordinary limits within the disk hold
away from a countable subset of the circle. -/
theorem circleAverage_eq_re_of_boundary_limits {H : ℂ → ℂ} {g : ℂ → ℝ} {M : ℝ}
    {E : Set ℂ} (hE : E.Countable) (hH : DifferentiableOn ℂ H (ball 0 1))
    (hbound : ∀ z ∈ ball 0 1, ‖(H z).re‖ ≤ M)
    (hlim : ∀ ζ ∈ sphere (0 : ℂ) 1, ζ ∉ E →
      Tendsto (fun z : ℂ => (H z).re) (𝓝[ball 0 1] ζ) (𝓝 (g ζ))) :
    Real.circleAverage g 0 1 = (H 0).re := by
  apply circleAverage_eq_re_of_radial_limits hH hbound
  filter_upwards [ae_circleMap_not_mem_of_countable hE] with θ hθ
  have hcircle : Tendsto (fun r : ℝ => circleMap 0 r θ) (𝓝[<] (1 : ℝ))
      (𝓝[ball (0 : ℂ) 1] (circleMap 0 1 θ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(show Continuous (fun r : ℝ => circleMap 0 r θ) by
      fun_prop [circleMap]).continuousAt.continuousWithinAt, ?_⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one),
      self_mem_nhdsWithin] with r hr₀ hr₁
    simpa [mem_ball_zero_iff, abs_of_pos (show 0 < r from hr₀)] using hr₁
  exact (hlim _ (circleMap_mem_sphere _ zero_le_one _) hθ).comp hcircle

end BelgianChocolate.SlitHarmonicMeasure
