import ModularLambdaReflection
import ModularLambdaCuspLabels
import TauCeti.Topology.Homotopy.Monodromy.Functoriality

namespace BelgianChocolate.ModularLambdaReflection

open Complex UpperHalfPlane Filter Set Topology
open BelgianChocolate.ModularLambdaRatio
open scoped MatrixGroups ComplexConjugate

/-- Complex conjugation on the twice-punctured target. -/
noncomputable def targetConjugation : C(({0,1}ᶜ : Set ℂ), ({0,1}ᶜ : Set ℂ)) where
  toFun z := ⟨(starRingEnd ℂ) (z : ℂ), by
    have hz := z.property
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h
      apply hz.1
      simpa using congrArg (starRingEnd ℂ) h
    · intro h
      apply hz.2
      simpa using congrArg (starRingEnd ℂ) h⟩
  continuous_toFun := by fun_prop

/-- The actual lambda covering commutes with the two reflections. -/
theorem lambdaPunctured_J (τ : ℍ) :
    lambdaPunctured (J • τ) = targetConjugation (lambdaPunctured τ) := by
  apply Subtype.ext
  change lambdaRatio (J • τ) = (starRingEnd ℂ) (lambdaRatio τ)
  exact lambdaRatio_J τ

/-- Compose standard reflection upstairs with an effective level-two deck map. -/
noncomputable def deckReflection (g : gammaTwoProjective) : C(ℍ, ℍ) where
  toFun τ := g • (J • τ)
  continuous_toFun := by fun_prop

/-- Every correction by a deck map still covers target conjugation. -/
theorem lambdaPunctured_deckReflection (g : gammaTwoProjective) (τ : ℍ) :
    lambdaPunctured (deckReflection g τ) = targetConjugation (lambdaPunctured τ) := by
  change lambdaPunctured (g • (J • τ)) = _
  rw [lambdaPunctured_quotientCovering.map_smul, lambdaPunctured_J]

/-- Above a real target value one can correct reflection by a genuine level-two
 deck map so that it fixes the chosen lift. No branch marking is assumed. -/
theorem exists_deckReflection_fixed {b : ({0,1}ᶜ : Set ℂ)}
    (hb : (b : ℂ).im = 0) (e : lambdaPunctured ⁻¹' {b}) :
    ∃ g : gammaTwoProjective, deckReflection g (e : ℍ) = (e : ℍ) := by
  have he : lambdaRatio (e : ℍ) = (b : ℂ) := congrArg Subtype.val e.property
  have hLambda : lambdaRatio (J • (e : ℍ)) = lambdaRatio (e : ℍ) := by
    rw [lambdaRatio_J, he]
    apply Complex.ext <;> simp [hb]
  obtain ⟨γ, hγ, hfix⟩ := lambdaRatio_fiber.mp hLambda
  refine ⟨⟨sl2zToPSL2R γ, ⟨γ, hγ, rfl⟩⟩, ?_⟩
  change sl2zToPSL2R γ • (J • (e : ℍ)) = (e : ℍ)
  rw [UpperHalfPlane.sl2zToPSL2R_smul]
  exact hfix

/-- Reflecting a loop downstairs and correcting the reflection to fix its
initial lift reflects its monodromy endpoint. The input is the actual
pointwise target reflection, not a presumed deck label. -/
theorem reflected_loop_monodromy {b : ({0,1}ᶜ : Set ℂ)}
    (α β : Path b b) (e : lambdaPunctured ⁻¹' {b}) (g : gammaTwoProjective)
    (hfix : deckReflection g (e : ℍ) = (e : ℍ))
    (hβ : ∀ u, (β u : ℂ) = (starRingEnd ℂ) (α u : ℂ)) :
    (lambdaPunctured_isCoveringMap.monodromy (.mk β) e : ℍ) =
      deckReflection g (lambdaPunctured_isCoveringMap.monodromy (.mk α) e : ℍ) := by
  let hp := lambdaPunctured_isCoveringMap
  let Γ := hp.liftPath α (e : ℍ) (α.source.trans e.property.symm)
  let Δ := (deckReflection g).comp Γ
  have hproj : lambdaPunctured ∘ Δ = β := by
    funext u
    change lambdaPunctured (deckReflection g (Γ u)) = β u
    rw [lambdaPunctured_deckReflection]
    apply Subtype.ext
    change (starRingEnd ℂ) (lambdaRatio (Γ u)) = (β u : ℂ)
    have hΓ : lambdaRatio (Γ u) = (α u : ℂ) :=
      congrArg Subtype.val (congrFun (hp.liftPath_lifts α (e : ℍ) _) u)
    rw [hΓ, hβ]
  have hΔ : Δ 0 = (e : ℍ) := by
    change deckReflection g (Γ 0) = (e : ℍ)
    rw [hp.liftPath_zero]
    exact hfix
  calc
    (hp.monodromy (.mk β) e : ℍ) = Δ 1 := hp.monodromy_eq_apply_one hproj hΔ
    _ = deckReflection g (hp.monodromy (.mk α) e : ℍ) := by
      rw [hp.coe_monodromy_mk]
      rfl

#print axioms exists_deckReflection_fixed
#print axioms reflected_loop_monodromy
end BelgianChocolate.ModularLambdaReflection
