import ComparisonCayley
import ComparisonGraph
import HarmonicBoundaryComparison

/-! Comparison of two lifts once the geometric boundary markings are available. -/

namespace BelgianChocolate.HarmonicComparison

open Complex Filter Metric Set Topology
open BelgianChocolate.ComparisonGraph

private theorem norm_lt_one_of_mem_curvedEdge {w : ℂ} (hw : w ∈ MarkedRealAxis.curvedEdge) :
    ‖w‖ < 1 := by
  obtain ⟨θ, hθ, rfl⟩ := hw
  have ha : 0 < Real.sqrt (θ * (Real.pi - θ)) :=
    Real.sqrt_pos.mpr (mul_pos hθ.1 (sub_pos.mpr hθ.2))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, Complex.ofReal_im,
    zero_sub, neg_zero, Real.exp_zero, mul_one]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)

private theorem continuousAt_comparisonLog_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    ContinuousAt comparisonLog w :=
  differentiableOn_comparisonLog.continuousOn.continuousAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw))

/-- Two normalized lifts with the specified curved-edge, real and lower-circle
boundary data agree on the unit disc. The finite set `E` contains the seams
between the arcs. Its points require only the candidate's limit from the
curved-edge arc; a seam outside that arc's closure is covered by the bottom
filter case. -/
theorem eqOn_of_markedLifts {f₀ f₁ : ℂ → ℂ} {G E : Set ℂ}
    (hf₀ : DifferentiableOn ℂ f₀ (ball 0 1)) (hf₁ : DifferentiableOn ℂ f₁ (ball 0 1))
    (hzero₀ : f₀ 0 = 0) (hzero₁ : f₁ 0 = 0)
    (hmap₀ : ∀ z ∈ ball (0 : ℂ) 1, ‖f₀ z‖ < 1)
    (hmap₁ : ∀ z ∈ ball (0 : ℂ) 1, ‖f₁ z‖ < 1)
    (hE : E.Finite)
    (hGraph : ∀ ξ ∈ G, ‖ξ‖ = 1 → ξ ∉ E →
      ContinuousWithinAt f₁ (closedBall 0 1) ξ ∧ ContinuousWithinAt f₀ (closedBall 0 1) ξ ∧
      f₁ ξ ∈ MarkedRealAxis.curvedEdge ∧ f₀ ξ ∈ MarkedRealAxis.curvedEdge)
    (hOther : ∀ ξ : ℂ, ‖ξ‖ = 1 → ξ ∉ G → ξ ∉ E →
      (∃ p q : ℂ, Tendsto f₁ (𝓝[ball (0 : ℂ) 1] ξ) (𝓝 p) ∧
        Tendsto f₀ (𝓝[ball (0 : ℂ) 1] ξ) (𝓝 q) ∧
        ‖p‖ < 1 ∧ p.im = 0 ∧ ‖q‖ < 1 ∧ q.im = 0) ∨
      (∃ p : ℂ, Tendsto f₀ (𝓝[ball (0 : ℂ) 1] ξ) (𝓝 p) ∧ ‖p‖ = 1 ∧ p.im < 0))
    (hSeams : ∀ ξ ∈ E, ‖ξ‖ = 1 →
      𝓝[G] ξ = ⊥ ∨ Tendsto f₀ (𝓝[G] ξ) (𝓝[MarkedRealAxis.curvedEdge] (1 : ℂ)) ∨
        Tendsto f₀ (𝓝[G] ξ) (𝓝[MarkedRealAxis.curvedEdge] (-1 : ℂ))) :
    EqOn f₁ f₀ (ball 0 1) := by
  classical
  let graphHeight (x : ℝ) : ℝ :=
    if hx : ∃ w ∈ MarkedRealAxis.curvedEdge, (comparisonLog w).re = x
    then (comparisonLog (Classical.choose hx)).im else 0
  have hHeight {w : ℂ} (hw : w ∈ MarkedRealAxis.curvedEdge) :
      (comparisonLog w).im = graphHeight (comparisonLog w).re := by
    have hex : ∃ p ∈ MarkedRealAxis.curvedEdge, (comparisonLog p).re = (comparisonLog w).re :=
      ⟨w, hw, rfl⟩
    simp only [graphHeight, dite_eq_left hex]
    exact curvedEdge_log_same_real hw (Classical.choose_spec hex).1 (Classical.choose_spec hex).2.symm
  have hW₀ : DifferentiableOn ℂ (fun z ↦ comparisonLog (f₀ z)) (ball 0 1) :=
    differentiableOn_comparisonLog.comp hf₀ (fun z hz ↦ mem_ball_zero_iff.mpr (hmap₀ z hz))
  have hW₁ : DifferentiableOn ℂ (fun z ↦ comparisonLog (f₁ z)) (ball 0 1) :=
    differentiableOn_comparisonLog.comp hf₁ (fun z hz ↦ mem_ball_zero_iff.mpr (hmap₁ z hz))
  have hM (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      |(comparisonLog (f₁ z) - comparisonLog (f₀ z)).im| ≤ Real.pi := by
    obtain ⟨hl₀, hu₀⟩ := abs_lt.mp (abs_im_comparisonLog_lt (hmap₀ z hz))
    obtain ⟨hl₁, hu₁⟩ := abs_lt.mp (abs_im_comparisonLog_lt (hmap₁ z hz))
    rw [Complex.sub_im, abs_le]
    constructor <;> linarith
  have heq := eqOn_of_graph_and_boundary_lowerBounds (G := G) (g := graphHeight)
    hW₀ hW₁ (by simp [hzero₀]) (by simp [hzero₁]) hM hE (by
      intro ξ hξG hξ hξE
      obtain ⟨hc₁, hc₀, hr₁, hr₀⟩ := hGraph ξ hξG hξ hξE
      have hk₁ : ContinuousWithinAt (fun z ↦ comparisonLog (f₁ z)) (closedBall 0 1) ξ :=
        ContinuousAt.comp_continuousWithinAt (g := comparisonLog) (f := f₁)
          (continuousAt_comparisonLog_of_norm_lt_one (norm_lt_one_of_mem_curvedEdge hr₁)) hc₁
      have hk₀ : ContinuousWithinAt (fun z ↦ comparisonLog (f₀ z)) (closedBall 0 1) ξ :=
        ContinuousAt.comp_continuousWithinAt (g := comparisonLog) (f := f₀)
          (continuousAt_comparisonLog_of_norm_lt_one (norm_lt_one_of_mem_curvedEdge hr₀)) hc₀
      exact ⟨hk₁, hk₀, hHeight hr₁, hHeight hr₀, curvedEdge_log_im_nonneg hr₁⟩) (by
      intro ξ hξ hξG hξE
      rcases hOther ξ hξ hξG hξE with ⟨p, q, h₁, h₀, hp, hpi, hq, hqi⟩ | ⟨p, h₀, hp, hpi⟩
      · exact im_comparisonLog_difference_lower_at_realValues h₁ h₀ hp hpi hq hqi
      · exact im_comparisonLog_difference_lower_at_lowerCircle h₀ hp hpi hmap₁) (by
      intro ξ hξE hξ
      rcases hSeams ξ hξE hξ with h | h | h
      · rw [h]
        exact tendsto_bot
      · exact tendsto_curvedEdge_log_im_one.comp h
      · exact tendsto_curvedEdge_log_im_neg_one.comp h)
  intro z hz
  exact injOn_comparisonLog (mem_ball_zero_iff.mpr (hmap₁ z hz))
    (mem_ball_zero_iff.mpr (hmap₀ z hz)) (heq hz)

end BelgianChocolate.HarmonicComparison
