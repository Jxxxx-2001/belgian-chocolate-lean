import ModularLambdaCuspPath
import FirstAnnulusModularGenerators
import FirstAnnulusTransport

/-! Transport the actual modular cusp labels through tailed homotopies. -/

namespace BelgianChocolate.ModularLambdaRatio

open Set UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open BelgianChocolate.FirstAnnulus BelgianChocolate.FirstAnnulusTransport
open scoped MatrixGroups

/-- The effective positive peripheral generator at zero. -/
noncomputable def zeroCuspDeck : gammaTwoProjective :=
  ⟨sl2zToPSL2R zeroGenerator, zeroGenerator, zeroGenerator_mem_gammaTwo, rfl⟩

/-- The effective positive peripheral generator at one. -/
noncomputable def oneCuspDeck : gammaTwoProjective :=
  ⟨sl2zToPSL2R oneGenerator, oneGenerator, oneGenerator_mem_gammaTwo, rfl⟩

theorem zeroCuspDeck_smul (z : UpperHalfPlane) :
    zeroCuspDeck • z = ModularGroup.T ^ (2:ℕ) • z := by
  change sl2zToPSL2R zeroGenerator • z = _
  rw [UpperHalfPlane.sl2zToPSL2R_smul, zeroGenerator_eq_T_sq]

theorem oneCuspDeck_smul (z : UpperHalfPlane) :
    oneCuspDeck • z = (ModularGroup.S * ModularGroup.T ^ (2:ℕ) * ModularGroup.S⁻¹) • z := by
  change sl2zToPSL2R oneGenerator • z = _
  rw [UpperHalfPlane.sl2zToPSL2R_smul, oneGenerator_eq_S_T_sq_S_inv]

/-- The loop has exactly the indicated deck label at one lift. At every other
lift the change-of-lift deck element conjugates that label. -/
def HasPeripheralLabel {b : ({0,1}ᶜ : Set ℂ)} (α : Path b b) (g : gammaTwoProjective) : Prop :=
  ∃ e : lambdaPunctured ⁻¹' {b},
    lambdaPunctured_isCoveringMap.monodromy (.mk α) e =
      lambdaPunctured_quotientCovering.toPermFiber b g e ∧
    ∀ e' : lambdaPunctured ⁻¹' {b}, ∃ k : gammaTwoProjective,
      lambdaPunctured_quotientCovering.toPermFiber b k e = e' ∧
      lambdaPunctured_isCoveringMap.monodromy (.mk α) e' =
        lambdaPunctured_quotientCovering.toPermFiber b (k*g*k⁻¹) e'

/-- Pull a specified peripheral label back along the tail using bijective covering transport. -/
theorem peripheralLabel_of_tailed_homotopy {b c : ({0,1}ᶜ : Set ℂ)} (tail : Path b c)
    (core : Path c c) (α : Path b b) (ht : ((tail.trans core).trans tail.symm).Homotopic α)
    (v : lambdaPunctured ⁻¹' {c}) (g : gammaTwoProjective)
    (hv : lambdaPunctured_isCoveringMap.monodromy (.mk core) v =
      lambdaPunctured_quotientCovering.toPermFiber c g v) : HasPeripheralLabel α g := by
  let hp := lambdaPunctured_quotientCovering
  let hc := lambdaPunctured_isCoveringMap
  obtain ⟨e,he⟩ := (hc.monodromy_bijective (.mk tail)).surjective v
  have hcancel : hc.monodromy (.mk tail.symm) v = e := by
    rw [← he, Path.Homotopic.Quotient.mk_symm, ← hc.monodromy_trans_apply,
      Path.Homotopic.Quotient.trans_symm, hc.monodromy_refl]
    rfl
  have hlabel : hc.monodromy (.mk α) e = hp.toPermFiber b g e := by
    rw [← Path.Homotopic.Quotient.eq.mpr ht, transport_trans, transport_trans, he, hv,
      hp.monodromy_toPermFiber, hcancel]
  refine ⟨e,hlabel,fun e' => ?_⟩
  obtain ⟨k,hk⟩ := hp.exists_toPermFiber_eq e e'
  exact ⟨k,hk,hk ▸ deck_label_change_initial_lift hp α e g k hlabel⟩

/-- At sufficient height, any two based loops identified with the corresponding positive
peripheral circles by the supplied tailed homotopies have the standard cusp labels.
Each initial lift can be chosen independently. -/
theorem tailed_positiveCircles_peripheralLabels :
    ∃ Y : ℝ, ∀ τ : UpperHalfPlane, Y ≤ τ.im →
      ∃ (h₀ : ‖lambdaRatio τ‖ < 1) (h₁ : ‖1-lambdaRatio (ModularGroup.S • τ)‖ < 1),
      (∀ {b : ({0,1}ᶜ : Set ℂ)} (tail : Path b (lambdaPunctured τ)) (α : Path b b),
        ((tail.trans (positiveZeroCircle (lambdaPunctured τ) h₀)).trans tail.symm).Homotopic α →
          HasPeripheralLabel α zeroCuspDeck) ∧
      (∀ {b : ({0,1}ᶜ : Set ℂ)} (tail : Path b (lambdaPunctured (ModularGroup.S • τ))) (α : Path b b),
        ((tail.trans (positiveOneCircle (lambdaPunctured (ModularGroup.S • τ)) h₁)).trans tail.symm).Homotopic α →
          HasPeripheralLabel α oneCuspDeck) := by
  obtain ⟨Y,hY⟩ := positiveCircles_monodromy
  refine ⟨Y, fun τ hτ => ?_⟩
  obtain ⟨h₀,h₁,hz,ho⟩ := hY τ hτ
  refine ⟨h₀,h₁,?_,?_⟩
  · intro b tail α hα
    apply peripheralLabel_of_tailed_homotopy tail _ α hα ⟨τ,rfl⟩ zeroCuspDeck
    apply Subtype.ext
    exact hz.trans (zeroCuspDeck_smul τ).symm
  · intro b tail α hα
    apply peripheralLabel_of_tailed_homotopy tail _ α hα ⟨ModularGroup.S • τ,rfl⟩ oneCuspDeck
    apply Subtype.ext
    exact ho.trans (oneCuspDeck_smul _).symm

/-- Normalize the zero peripheral loop at the common base lift. The one-loop label then
has its conjugate form there, and the pair word has the corresponding ordered product. -/
theorem peripheral_pair_at_common_lift {b : ({0,1}ᶜ : Set ℂ)} (α β : Path b b)
    (hz : HasPeripheralLabel α zeroCuspDeck) (ho : HasPeripheralLabel β oneCuspDeck) :
    ∃ (e : lambdaPunctured ⁻¹' {b}) (k : gammaTwoProjective),
      lambdaPunctured_isCoveringMap.monodromy (.mk α) e =
        lambdaPunctured_quotientCovering.toPermFiber b zeroCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy (.mk β) e =
        lambdaPunctured_quotientCovering.toPermFiber b (k*oneCuspDeck*k⁻¹) e ∧
      lambdaPunctured_isCoveringMap.monodromy (.mk (α.trans β)) e =
        lambdaPunctured_quotientCovering.toPermFiber b (zeroCuspDeck*(k*oneCuspDeck*k⁻¹)) e := by
  obtain ⟨e,he,_⟩ := hz
  obtain ⟨_,_,hall⟩ := ho
  obtain ⟨k,_,hk⟩ := hall e
  exact ⟨e,k,he,hk,deck_labels_trans lambdaPunctured_quotientCovering α β e _ _ he hk⟩

end BelgianChocolate.ModularLambdaRatio

