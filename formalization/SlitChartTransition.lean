import UnfoldedSlitPrimeEnds
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

/-! The inclusion of one physical slit domain in another, in their closed
unfolded charts. -/

namespace BelgianChocolate.SlitBoundaryGeometry

open Complex Function Metric Set
open BelgianChocolate.SlitSquareRoot BelgianChocolate.SlitStarConvex

private noncomputable def transition (k : ℝ) (v : ℂ) : ℂ :=
  Complex.sqrt (v + (k : ℂ) * I) * Complex.sqrt (v - (k : ℂ) * I)

private theorem transition_continuousOn (k : ℝ) :
    ContinuousOn (transition k) {v : ℂ | 0 ≤ v.re} := by
  intro v hv
  have hp : 0 ≤ (v + (k : ℂ) * I).re := by simpa using hv
  have hm : 0 ≤ (v - (k : ℂ) * I).re := by simpa using hv
  have hc₁ : ContinuousAt (fun x : ℂ => x + (k : ℂ) * I) v := by fun_prop
  have hc₂ : ContinuousAt (fun x : ℂ => x - (k : ℂ) * I) v := by fun_prop
  have h₁ : ContinuousAt (fun x : ℂ => Complex.sqrt (x + (k : ℂ) * I)) v :=
    (Complex.continuousAt_sqrt (Or.inl hp)).comp
      (f := fun x : ℂ => x + (k : ℂ) * I) (g := Complex.sqrt) (x := v) hc₁
  have h₂ : ContinuousAt (fun x : ℂ => Complex.sqrt (x - (k : ℂ) * I)) v :=
    (Complex.continuousAt_sqrt (Or.inl hm)).comp
      (f := fun x : ℂ => x - (k : ℂ) * I) (g := Complex.sqrt) (x := v) hc₂
  exact (h₁.mul h₂).continuousWithinAt

private theorem transition_differentiableOn (k : ℝ) :
    DifferentiableOn ℂ (transition k) {v : ℂ | 0 < v.re} := by
  intro v hv
  have hp : v + (k : ℂ) * I ∈ slitPlane := Or.inl (by simpa using hv)
  have hm : v - (k : ℂ) * I ∈ slitPlane := Or.inl (by simpa using hv)
  have h₁ := (Complex.differentiableAt_sqrt hp).comp v
    ((differentiableAt_id : DifferentiableAt ℂ (id : ℂ → ℂ) v).add (differentiableAt_const _))
  have h₂ := (Complex.differentiableAt_sqrt hm).comp v
    ((differentiableAt_id : DifferentiableAt ℂ (id : ℂ → ℂ) v).sub (differentiableAt_const _))
  exact (h₁.mul h₂).differentiableWithinAt

private theorem abs_sqrt_im_lt_re {z : ℂ} (hz : 0 < z.re) :
    |z.sqrt.im| < z.sqrt.re := by
  apply (sq_lt_sq₀ (abs_nonneg _) (Complex.sqrt_re_nonneg _)).mp
  rw [sq_abs]
  have he := congrArg Complex.re (Complex.sq_sqrt z)
  rw [pow_two, Complex.mul_re] at he
  nlinarith

private theorem transition_re_pos {k : ℝ} {v : ℂ} (hv : 0 < v.re) :
    0 < (transition k v).re := by
  unfold transition
  let a := Complex.sqrt (v + (k : ℂ) * I)
  let b := Complex.sqrt (v - (k : ℂ) * I)
  change 0 < (a * b).re
  rw [Complex.mul_re, sub_pos]
  have ha : |a.im| < a.re := abs_sqrt_im_lt_re (by simpa using hv)
  have hb : |b.im| < b.re := abs_sqrt_im_lt_re (by simpa using hv)
  calc
    a.im * b.im ≤ |a.im * b.im| := le_abs_self _
    _ = |a.im| * |b.im| := abs_mul ..
    _ < a.re * b.re := mul_lt_mul'' ha hb (abs_nonneg _) (abs_nonneg _)

private theorem folding_transition (α β : ℝ) (hαβ : α ≤ β) (v : ℂ) :
    folding α (transition (Real.sqrt (β - α)) v) = folding β v := by
  have hk : ((Real.sqrt (β - α) : ℝ) : ℂ) ^ 2 = (β : ℂ) - (α : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hαβ)
  rw [folding, transition, mul_pow, Complex.sq_sqrt, Complex.sq_sqrt, folding]
  calc
    (v + (Real.sqrt (β - α) : ℂ) * I) * (v - (Real.sqrt (β - α) : ℂ) * I) + (α : ℂ) =
        v ^ 2 - (Real.sqrt (β - α) : ℂ) ^ 2 * I ^ 2 + (α : ℂ) := by ring
    _ = v ^ 2 + (β : ℂ) := by rw [hk, I_sq]; ring

/-- A closed-disk extension of the chart map induced by inclusion of slit
domains. Both old slit banks are handled by the same continuous extension. -/
structure SlitChartTransition (α β : ℝ) (F G K : ℂ → ℂ) : Prop where
  center : K 0 = 0
  holomorphic : DifferentiableOn ℂ K (ball 0 1)
  continuous : ContinuousOn K (closedBall 0 1)
  mapsInterior : MapsTo K (ball 0 1) (ball 0 1)
  mapsClosed : MapsTo K (closedBall 0 1) (closedBall 0 1)
  physical : ∀ z ∈ closedBall (0 : ℂ) 1, folding α (F (K z)) = folding β (G z)

theorem exists_slitChartTransition {α β : ℝ} (hαβ : α ≤ β) {F G : ℂ → ℂ}
    (hF : CenteredUnfoldedChart α F) (hG : CenteredUnfoldedChart β G) :
    ∃ K : ℂ → ℂ, SlitChartTransition α β F G K := by
  let T := transition (Real.sqrt (β - α))
  have hfold (v : ℂ) : folding α (T v) = folding β v := folding_transition α β hαβ v
  have hT : MapsTo T (unfoldedDomain β) (unfoldedDomain α) := by
    intro v hv
    refine ⟨transition_re_pos hv.1, ?_⟩
    rw [hfold]
    exact hv.2
  have hTclosed : ContinuousOn T (closure (unfoldedDomain β)) :=
    (transition_continuousOn _).mono (closure_minimal
      (fun _ hv => hv.1.le) (isClosed_le continuous_const continuous_re))
  let H := T ∘ G
  have hH : MapsTo H (ball 0 1) (unfoldedDomain α) := hT.comp hG.interior_bij.mapsTo
  have hHclosed : MapsTo H (closedBall 0 1) (closure (unfoldedDomain α)) :=
    (hT.closure_of_continuousOn hTclosed).comp hG.closed_bij.mapsTo
  let K := invFunOn F (closedBall 0 1) ∘ H
  have hinvMap := hF.closed_bij.surjOn.mapsTo_invFunOn
  have hKclosed : MapsTo K (closedBall 0 1) (closedBall 0 1) := hinvMap.comp hHclosed
  have hinvEq (v : ℂ) (hv : v ∈ unfoldedDomain α) :
      invFunOn F (closedBall 0 1) v = invFunOn F (ball 0 1) v := by
    apply hF.closed_bij.injOn (hinvMap (subset_closure hv))
      (ball_subset_closedBall (hF.interior_bij.surjOn.mapsTo_invFunOn hv))
    rw [hF.closed_bij.surjOn.rightInvOn_invFunOn (subset_closure hv),
      hF.interior_bij.surjOn.rightInvOn_invFunOn hv]
  have hK : MapsTo K (ball 0 1) (ball 0 1) := by
    intro z hz
    change invFunOn F (closedBall 0 1) (H z) ∈ _
    rw [hinvEq _ (hH hz)]
    exact hF.interior_bij.surjOn.mapsTo_invFunOn (hH hz)
  have hphys (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) :
      folding α (F (K z)) = folding β (G z) := by
    change folding α (F (invFunOn F (closedBall 0 1) (H z))) = _
    rw [hF.closed_bij.surjOn.rightInvOn_invFunOn (hHclosed hz)]
    exact hfold _
  have h0 : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hz : K 0 = 0 := hF.folded_interior.2.2.injOn (hK h0) h0 (by
    rw [Function.comp_apply, hphys _ (ball_subset_closedBall h0),
      hG.zero, Function.comp_apply, hF.zero, folding_unfolding, folding_unfolding])
  have hinvDiff := hF.holomorphic.invFunOn isOpen_ball hF.interior_bij.injOn
  rw [hF.interior_bij.image_eq] at hinvDiff
  have hHDiff : DifferentiableOn ℂ H (ball 0 1) :=
    (transition_differentiableOn _).comp hG.holomorphic
      (fun z hz => (hG.interior_bij.mapsTo hz).1)
  have hKDiff : DifferentiableOn ℂ K (ball 0 1) :=
    (hinvDiff.comp hHDiff hH).congr fun _ hz => hinvEq _ (hH hz)
  have hinvCont := hF.closed_continuous.continuousOn_invFunOn_image_of_isCompact
    (isCompact_closedBall (0 : ℂ) 1) subset_rfl hF.closed_bij.injOn (by simp)
  rw [hF.closed_bij.image_eq] at hinvCont
  exact ⟨K, hz, hKDiff, hinvCont.comp (hTclosed.comp hG.closed_continuous
    hG.closed_bij.mapsTo) hHclosed, hK, hKclosed, hphys⟩

/-- Boundary preimages of finite exceptional sets are finite, even where
two points on the new slit banks map to the same interior point. -/
theorem SlitChartTransition.finite_frontier_preimage {α β : ℝ} {F G K : ℂ → ℂ}
    (hK : SlitChartTransition α β F G K) (hG : CenteredUnfoldedChart β G)
    {E : Set ℂ} (hE : E.Finite) : (sphere (0 : ℂ) 1 ∩ K ⁻¹' E).Finite := by
  apply (hE.biUnion fun w _ => hG.finite_folded_fiber (folding α (F w))).subset
  intro z hz
  refine mem_iUnion₂.mpr ⟨K z, hz.2, hz.1, ?_⟩
  exact (hK.physical z (sphere_subset_closedBall hz.1)).symm

end BelgianChocolate.SlitBoundaryGeometry
