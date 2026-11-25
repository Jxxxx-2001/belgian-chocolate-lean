import HarmonicBoundaryBarrier
import HarmonicTrace

/-! The boundary estimates for the harmonic comparison of two holomorphic maps. -/

namespace BelgianChocolate.HarmonicComparison

open Complex Filter Metric Set Topology

/-- The three seams of the disc comparison are instances of this estimate. On
the graph arc the competing trace is nonnegative, and the candidate's trace
approaches zero. On the remaining open arcs the interior lower bound is already
available. The seam itself needs no boundary value of either function. -/
theorem im_lowerBound_near_seam {W₀ W₁ : ℂ → ℂ} {G E : Set ℂ} {M : ℝ} {ξ : ℂ}
    (hW : DifferentiableOn ℂ (fun z ↦ W₁ z - W₀ z) (ball 0 1))
    (hM : ∀ z ∈ ball (0 : ℂ) 1, -M ≤ (W₁ z - W₀ z).im)
    (hξ : ‖ξ‖ = 1)
    (hE : E.Finite)
    (hGraph : ∀ η ∈ G, ‖η‖ = 1 → η ∉ E →
      ContinuousWithinAt W₁ (closedBall 0 1) η ∧ ContinuousWithinAt W₀ (closedBall 0 1) η ∧
      0 ≤ (W₁ η).im)
    (hOther : ∀ η : ℂ, ‖η‖ = 1 → η ∉ G → η ∉ E →
      ∀ ε > 0, ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z η < d → -ε ≤ (W₁ z - W₀ z).im)
    (hTrace : Tendsto (fun z ↦ (W₀ z).im) (𝓝[G] ξ) (𝓝 0)) :
    ∀ ε > 0, ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z ξ < d → -ε ≤ (W₁ z - W₀ z).im := by
  apply im_lowerBound_near_boundary_of_puncturedArc hW hM hξ
  intro ε hε
  have hEopen : IsOpen ((E \ {ξ})ᶜ) := hE.sdiff.isClosed.isOpen_compl
  have hEnhds : (E \ {ξ})ᶜ ∈ 𝓝 ξ := hEopen.mem_nhds (by simp)
  obtain ⟨r, hr, hrE⟩ := Metric.nhds_basis_ball.mem_iff.mp hEnhds
  have hCandidate : ∀ᶠ z in 𝓝[G] ξ, (W₀ z).im < ε :=
    hTrace.eventually (gt_mem_nhds hε)
  obtain ⟨d, hd, hdGraph⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hCandidate
  refine ⟨min r d, lt_min hr hd, ?_⟩
  intro η hη hηξ hdist
  have hηE : η ∉ E := fun h ↦
    (hrE (mem_ball.mpr (hdist.trans_le (min_le_left _ _)))) ⟨h, hηξ⟩
  by_cases hηG : η ∈ G
  · obtain ⟨hW₁, hW₀, hpos⟩ := hGraph η hηG hη hηE
    have hsmall := hdGraph ⟨mem_ball.mpr (hdist.trans_le (min_le_right _ _)), hηG⟩
    have hηlower : -ε < (W₁ η - W₀ η).im := by
      rw [Complex.sub_im]
      linarith
    have hCont : ContinuousWithinAt (fun z ↦ (W₁ z - W₀ z).im) (closedBall 0 1) η :=
      Complex.continuous_im.continuousAt.comp_continuousWithinAt (hW₁.sub hW₀)
    have hLoc : ∀ᶠ z in 𝓝[closedBall (0 : ℂ) 1] η, -ε < (W₁ z - W₀ z).im :=
      hCont.eventually (lt_mem_nhds hηlower)
    obtain ⟨s, hs, hsLower⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hLoc
    exact ⟨s, hs, fun z hz hdist ↦
      (hsLower ⟨mem_ball.mpr hdist, ball_subset_closedBall hz⟩).le⟩
  · exact hOther η hη hηG hηE ε hε

/-- Disc comparison with a common graph arc and finitely many seams. The
normalized primitive and its continuous trace are constructed in the proof. -/
theorem eqOn_of_graph_and_boundary_lowerBounds {W₀ W₁ : ℂ → ℂ} {G E : Set ℂ}
    {g : ℝ → ℝ} {M : ℝ}
    (hW₀ : DifferentiableOn ℂ W₀ (ball 0 1))
    (hW₁ : DifferentiableOn ℂ W₁ (ball 0 1))
    (h₀ : W₀ 0 = 0) (h₁ : W₁ 0 = 0)
    (hM : ∀ z ∈ ball (0 : ℂ) 1, |(W₁ z - W₀ z).im| ≤ M)
    (hE : E.Finite)
    (hGraph : ∀ ξ ∈ G, ‖ξ‖ = 1 → ξ ∉ E →
      ContinuousWithinAt W₁ (closedBall 0 1) ξ ∧ ContinuousWithinAt W₀ (closedBall 0 1) ξ ∧
      (W₁ ξ).im = g (W₁ ξ).re ∧ (W₀ ξ).im = g (W₀ ξ).re ∧ 0 ≤ (W₁ ξ).im)
    (hOther : ∀ ξ : ℂ, ‖ξ‖ = 1 → ξ ∉ G → ξ ∉ E →
      ∀ ε > 0, ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z ξ < d → -ε ≤ (W₁ z - W₀ z).im)
    (hTrace : ∀ ξ ∈ E, ‖ξ‖ = 1 → Tendsto (fun z ↦ (W₀ z).im) (𝓝[G] ξ) (𝓝 0)) :
    EqOn W₁ W₀ (ball 0 1) := by
  have hW : DifferentiableOn ℂ (fun z ↦ W₁ z - W₀ z) (ball 0 1) := hW₁.sub hW₀
  have hW0 : W₁ 0 - W₀ 0 = 0 := by rw [h₁, h₀, sub_zero]
  have heq := eqOn_zero_of_boundedIm_boundaryComparison hW hW0 hM (by
    intro F D _ hdF hFW hD hDF ξ hξ hmin
    by_cases hξE : ξ ∈ E
    · apply radial_im_lowerBound_of_local (W := fun z ↦ W₁ z - W₀ z) hξ
      apply im_lowerBound_near_seam hW (fun z hz ↦ (abs_le.mp (hM z hz)).1) hξ hE
      · intro η hηG hη hηE
        obtain ⟨hc₁, hc₀, _, _, hp⟩ := hGraph η hηG hη hηE
        exact ⟨hc₁, hc₀, hp⟩
      · exact hOther
      · exact hTrace ξ hξE hξ
    · by_cases hξG : ξ ∈ G
      · obtain ⟨hc₁, hc₀, hg₁, hg₀, _⟩ := hGraph ξ hξG hξ hξE
        have hF : DifferentiableOn ℂ F (ball 0 1) :=
          fun z hz ↦ (hdF z hz).differentiableAt.differentiableWithinAt
        exact graph_arc_radial_lowerBound hξ hF hFW hD hDF hc₁ hc₀ hmin hg₁ hg₀
      · exact radial_im_lowerBound_of_local hξ (hOther ξ hξ hξG hξE))
  exact fun z hz ↦ sub_eq_zero.mp (heq hz)

end BelgianChocolate.HarmonicComparison
