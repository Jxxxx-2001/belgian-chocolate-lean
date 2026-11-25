import UnfoldedSlitNormalization
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Metric Filter Topology
open BelgianChocolate.SlitSquareRoot

noncomputable def halfPlaneDiskChart (α : ℝ) (G : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ G (I * (1+z)/(1-z))) 1 (upperBankEnd α)

theorem halfPlaneDiskChart_regular {α : ℝ} {G : ℂ → ℂ} {z : ℂ} (hz : z ≠ 1) :
    halfPlaneDiskChart α G z = G (I * (1+z)/(1-z)) := by simp [halfPlaneDiskChart,hz]

theorem UnfoldedHalfPlaneChart.centered_disk_chart {α : ℝ} {G : ℂ → ℂ}
    (h : UnfoldedHalfPlaneChart α G) (hl : -1 < α) (hr : α < 0)
    (hc : G I = unfolding α 0) : CenteredUnfoldedChart α (halfPlaneDiskChart α G) := by
  let K := fun z : ℂ ↦ I*(1+z)/(1-z)
  let F := halfPlaneDiskChart α G
  have hreg {z : ℂ} (hz : z ≠ 1) : F z = G (K z) := halfPlaneDiskChart_regular hz
  have h1 : F 1 = upperBankEnd α := by simp [F,halfPlaneDiskChart]
  have hn {z : ℂ} (hz : z ∈ ball 0 1) : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hi : BijOn F (ball 0 1) (unfoldedDomain α) :=
    (h.interior_bij.comp TauCeti.bijOn_I_mul_one_add_div_one_sub_ball).congr
      (fun _ hz => (hreg (hn hz)).symm)
  have hd : DifferentiableOn ℂ F (ball 0 1) :=
    (h.holo.comp (fun _ hz => (TauCeti.hasDerivAt_I_mul_one_add_div_one_sub (hn hz)).differentiableAt.differentiableWithinAt)
        TauCeti.bijOn_I_mul_one_add_div_one_sub_ball.mapsTo).congr (fun _ hz => hreg (hn hz))
  have hcl : ContinuousOn F (closedBall 0 1) := by
    dsimp only [F, halfPlaneDiskChart]
    rw [continuousOn_update_iff]
    constructor
    · exact h.cont.comp (fun _ hz => (TauCeti.hasDerivAt_I_mul_one_add_div_one_sub hz.2).continuousAt.continuousWithinAt)
        TauCeti.bijOn_I_mul_one_add_div_one_sub_closedBall_sdiff.mapsTo
    · intro _
      exact h.at_infty.comp TauCeti.tendsto_I_mul_one_add_div_one_sub_nhdsWithin_closedBall_sdiff_one
  have hpre : BijOn F (closedBall 0 1 \ {1}) (closure (unfoldedDomain α) \ {upperBankEnd α}) :=
    (h.closed_bij.comp TauCeti.bijOn_I_mul_one_add_div_one_sub_closedBall_sdiff).congr
      (fun _ hz => (hreg hz.2).symm)
  have he1 : (1 : ℂ) ∈ closedBall 0 1 := by simp
  have heP : upperBankEnd α ∈ closure (unfoldedDomain α) :=
    frontier_subset_closure (upperBankEnd_mem_frontier hl hr)
  have hb := hpre.insert (a := (1 : ℂ)) (by simp [h1])
  rw [h1] at hb
  have hf1 : insert 1 (closedBall (0 : ℂ) 1 \ {1}) = closedBall 0 1 := by ext; simp_all
  have hfP : insert (upperBankEnd α) (closure (unfoldedDomain α) \ {upperBankEnd α}) = closure (unfoldedDomain α) := by ext; simp_all
  rw [hf1,hfP] at hb
  refine ⟨by simpa [halfPlaneDiskChart] using hc,hd,hi,hcl,hb,?_⟩
  have hf := TauCeti.image_frontier_eq_frontier_image isOpen_ball
    (isBounded_ball (x := (0 : ℂ)) (r := 1)) hd hi.injOn
    (by simpa only [closure_ball _ one_ne_zero] using hcl) (fun _ _ => rfl)
  rw [frontier_ball _ one_ne_zero,hi.image_eq] at hf
  rw [← hf]
  exact (hb.injOn.mono sphere_subset_closedBall).bijOn_image

end BelgianChocolate.SlitBoundaryGeometry


