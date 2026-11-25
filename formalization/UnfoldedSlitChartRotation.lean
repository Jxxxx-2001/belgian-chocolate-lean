import UnfoldedSlitChart
import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Uniqueness

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Metric

/-- Two centered unfolded charts differ on the entire closed disc by a rotation. -/
theorem CenteredUnfoldedChart.eqOn_rotation {α : ℝ} {F G : ℂ → ℂ}
    (hF : CenteredUnfoldedChart α F) (hG : CenteredUnfoldedChart α G) :
    ∃ u : Circle, EqOn F (fun z ↦ G ((u : ℂ) * z)) (closedBall 0 1) := by
  let D := ball (0 : ℂ) 1
  let I := Function.invFunOn F D
  let J := Function.invFunOn G D
  have hi : BijOn I (unfoldedDomain α) D :=
    hF.interior_bij.symm hF.interior_bij.invOn_invFunOn.symm
  have hj : BijOn J (unfoldedDomain α) D :=
    hG.interior_bij.symm hG.interior_bij.invOn_invFunOn.symm
  have hdI : DifferentiableOn ℂ I (unfoldedDomain α) :=
    hF.interior_bij.image_eq ▸ hF.holomorphic.invFunOn isOpen_ball hF.interior_bij.injOn
  have hdJ : DifferentiableOn ℂ J (unfoldedDomain α) :=
    hG.interior_bij.image_eq ▸ hG.holomorphic.invFunOn isOpen_ball hG.interior_bij.injOn
  have hz : (0 : ℂ) ∈ D := mem_ball_self one_pos
  have hI : I (F 0) = 0 := hF.interior_bij.invOn_invFunOn.1 hz
  have hJ : J (F 0) = 0 := by
    rw [hF.zero, ← hG.zero]; exact hG.interior_bij.invOn_invFunOn.1 hz
  obtain ⟨u,hu⟩ := TauCeti.exists_eqOn_const_mul_of_image_eq_ball_of_apply_eq_zero
    (unfoldedDomain_isOpen α) hdI hdJ hi.injOn hj.injOn hi.image_eq hj.image_eq
    (hF.interior_bij.mapsTo hz) hI hJ
  refine ⟨u,?_⟩
  have he : EqOn F (fun z ↦ G ((u : ℂ) * z)) D := by
    intro z hz
    have h := hu (hF.interior_bij.mapsTo hz)
    change J (F z) = (u : ℂ) * I (F z) at h
    rw [show I (F z) = z from hF.interior_bij.invOn_invFunOn.1 hz] at h
    change F z = G ((u : ℂ) * z)
    rw [← h]
    exact (hG.interior_bij.invOn_invFunOn.2 (hF.interior_bij.mapsTo hz)).symm
  apply he.of_subset_closure hF.closed_continuous (hG.closed_continuous.comp
    (continuous_const.mul continuous_id).continuousOn ?_) ball_subset_closedBall
  · exact (closure_ball (0 : ℂ) one_ne_zero).symm.subset
  · intro z hz
    simpa only [mem_closedBall_zero_iff, norm_mul, Circle.norm_coe, one_mul] using hz

end BelgianChocolate.SlitBoundaryGeometry
