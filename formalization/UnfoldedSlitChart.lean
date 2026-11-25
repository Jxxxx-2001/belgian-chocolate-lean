import UnfoldedSlitDomain
import TauCeti.Analysis.Complex.Conformal.Caratheodory
import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
import TauCeti.Analysis.Complex.Conformal.Jordan.Approach

/-! Centered Riemann charts of the actual square-root unfolding. -/
namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Metric Topology
open BelgianChocolate.SlitSquareRoot

structure CenteredUnfoldedChart (α : ℝ) (F : ℂ → ℂ) : Prop where
  zero : F 0 = unfolding α 0
  holomorphic : DifferentiableOn ℂ F (ball 0 1)
  interior_bij : BijOn F (ball 0 1) (unfoldedDomain α)
  closed_continuous : ContinuousOn F (closedBall 0 1)
  closed_bij : BijOn F (closedBall 0 1) (closure (unfoldedDomain α))
  frontier_bij : BijOn F (sphere 0 1) (frontier (unfoldedDomain α))

theorem exists_centeredUnfoldedChart {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    ∃ F : ℂ → ℂ, CenteredUnfoldedChart α F := by
  have hJ := unfoldedDomain_isJordanDomain hl hr
  let _ : LocallyConnectedSpace (frontier (unfoldedDomain α)) :=
    hJ.isJordanCurve_frontier.locallyConnectedSpace
  obtain ⟨F, hc, hd, hbij, hz⟩ :=
    TauCeti.exists_continuousOn_closedBall_bijOn_ball_of_locallyConnectedSpace_frontier_of_mem
      hJ.isOpen hJ.isSimplyConnected hJ.isBounded (unfolding_zero_mem hr)
  have hi := hbij.image_eq
  have hI : InjOn F (closedBall 0 1) :=
    TauCeti.injOn_closedBall_of_isJordanCurve_frontier (by norm_num) hd hbij.injOn
      (by rw [hi]; exact hJ.isBounded) (by rw [hi]; exact hJ.isJordanCurve_frontier) hc
      (fun _ _ => rfl)
  refine ⟨F, hz, hd, hbij, hc, ?_, ?_⟩
  · have h := TauCeti.bijOn_closure_closure_image (isBounded_ball (x := (0 : ℂ)) (r := 1))
      (by simpa only [closure_ball _ one_ne_zero] using hc) (fun _ _ => rfl)
      (by simpa only [closure_ball _ one_ne_zero] using hI)
    simpa only [closure_ball _ one_ne_zero, hi] using h
  · have hf := TauCeti.image_frontier_eq_frontier_image isOpen_ball
      (isBounded_ball (x := (0 : ℂ)) (r := 1)) hd hbij.injOn
      (by simpa only [closure_ball _ one_ne_zero] using hc) (fun _ _ => rfl)
    rw [frontier_ball _ one_ne_zero, hi] at hf
    rw [← hf]
    exact (hI.mono sphere_subset_closedBall).bijOn_image

theorem folding_bijOn_unfoldedDomain (α : ℝ) :
    BijOn (folding α) (unfoldedDomain α) (candidateSlit α) := by
  rw [← unfolding_image_candidateSlit]
  constructor
  · rintro _ ⟨z,hz,rfl⟩
    simpa only [folding_unfolding] using hz
  constructor
  · rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩ he
    simp only [folding_unfolding] at he
    rw [he]
  · intro z hz
    exact ⟨unfolding α z, ⟨z,hz,rfl⟩, folding_unfolding α z⟩

/-- Folding the chart gives a conformal parametrization of the physical slit
interior and identifies the normalized origin in physical coordinates. -/
theorem CenteredUnfoldedChart.folded_interior {α : ℝ} {F : ℂ → ℂ}
    (h : CenteredUnfoldedChart α F) :
    (folding α ∘ F) 0 = 0 ∧ DifferentiableOn ℂ (folding α ∘ F) (ball 0 1) ∧
      BijOn (folding α ∘ F) (ball 0 1) (candidateSlit α) := by
  exact ⟨by simp [h.zero], (differentiable_folding α).comp_differentiableOn h.holomorphic,
    (folding_bijOn_unfoldedDomain α).comp h.interior_bij⟩

end BelgianChocolate.SlitBoundaryGeometry
