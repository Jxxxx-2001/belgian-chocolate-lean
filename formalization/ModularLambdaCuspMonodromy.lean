import ModularLambdaCuspMarked
import ModularLambdaCuspLabels

/-! The marked cusp projection intertwines the modular and cusp coverings.
A one-cusp modular deck transformation becomes the identity on the cusp fibre. -/

namespace BelgianChocolate.ModularLambdaRatio

open Complex Set UpperHalfPlane
open scoped MatrixGroups

/-- The marked cusp projection valued in the punctured unit disc. -/
noncomputable def markedCuspDisc (τ : ℍ) : PuncturedUnitDisc :=
  ⟨BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ), markedCusp_mem_puncturedUnitDisc τ⟩

theorem markedCuspDisc_continuous : Continuous markedCuspDisc := by
  apply Continuous.subtype_mk
  have h : Continuous (fun τ : ℍ => ModularGroup.S • τ) :=
    continuous_const_smul ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S).toGL)
  have hn := (continuous_subtype_val.comp cuspNomeDisc_isQuotientMap.continuous).comp h
  exact hn.neg.congr fun τ => (markedCusp_eq_neg_nome τ).symm

theorem cuspUPunctured_markedCuspDisc (τ : ℍ) :
    cuspUPunctured (markedCuspDisc τ) = lambdaPunctured τ := by
  apply Subtype.ext
  rw [cuspUPunctured_coe]
  exact cuspU_markedCusp τ

private theorem S_action_involutive (τ : ℍ) :
    ModularGroup.S • (ModularGroup.S • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [ModularGroup.coe_S_smul, ModularGroup.coe_S_smul]
  field_simp [τ.ne_zero]

private theorem S_inv_smul_eq_S_smul (τ : ℍ) :
    ModularGroup.S⁻¹ • τ = ModularGroup.S • τ := by
  rw [← inv_smul_smul ModularGroup.S (ModularGroup.S • τ), S_action_involutive]

theorem markedCuspDisc_oneCuspDeck (τ : ℍ) :
    markedCuspDisc (oneCuspDeck • τ) = markedCuspDisc τ := by
  apply Subtype.ext
  change BelgianChocolate.MarkedRealAxis.cusp (↑(oneCuspDeck • τ) : ℂ) =
    BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ)
  rw [oneCuspDeck_smul, mul_smul, mul_smul, S_inv_smul_eq_S_smul τ]
  have h := markedCusp_conjPeriod (1 : ℤ) τ
  rw [S_inv_smul_eq_S_smul] at h
  simpa using h

/-- Projecting a modular monodromy endpoint through the marked cusp map gives
the corresponding endpoint for the cusp covering. -/
theorem cuspU_monodromy_projection {b c : ({0,1}ᶜ : Set ℂ)} (γ : Path b c)
    (e : lambdaPunctured ⁻¹' {b}) :
    (cuspUPunctured_isCoveringMap.monodromy (.mk γ)
      ⟨markedCuspDisc e, (cuspUPunctured_markedCuspDisc e).trans e.2⟩ : PuncturedUnitDisc) =
      markedCuspDisc (lambdaPunctured_isCoveringMap.monodromy (.mk γ) e) := by
  let P := lambdaPunctured_isCoveringMap
  let Q := cuspUPunctured_isCoveringMap
  have he : γ 0 = lambdaPunctured (e : ℍ) := γ.source.trans e.2.symm
  let Γ := P.liftPath γ e he
  let m : C(ℍ, PuncturedUnitDisc) := ⟨markedCuspDisc, markedCuspDisc_continuous⟩
  have hΓ := P.liftPath_lifts γ e he
  have hΓ' : cuspUPunctured ∘ (m.comp Γ : unitInterval → PuncturedUnitDisc) = γ := by
    funext s
    change cuspUPunctured (markedCuspDisc (Γ s)) = γ s
    rw [cuspUPunctured_markedCuspDisc]
    exact congrFun hΓ s
  have h0 : (m.comp Γ) 0 = markedCuspDisc e := by
    change markedCuspDisc (Γ 0) = _
    rw [P.liftPath_zero]
  rw [Q.monodromy_eq_apply_one hΓ' h0, P.monodromy_eq_apply_one hΓ (P.liftPath_zero ..)]
  rfl

/-- If the positive one-cusp deck step is the actual modular monodromy,
the projected cusp lift is closed. -/
theorem cuspU_monodromy_eq_self_of_oneCuspDeck {b : ({0,1}ᶜ : Set ℂ)}
    (γ : Path b b) (e : lambdaPunctured ⁻¹' {b})
    (h : (lambdaPunctured_isCoveringMap.monodromy (.mk γ) e : ℍ) = oneCuspDeck • (e : ℍ)) :
    cuspUPunctured_isCoveringMap.monodromy (.mk γ)
      ⟨markedCuspDisc e, (cuspUPunctured_markedCuspDisc e).trans e.2⟩ =
      ⟨markedCuspDisc e, (cuspUPunctured_markedCuspDisc e).trans e.2⟩ := by
  apply Subtype.ext
  rw [cuspU_monodromy_projection, h, markedCuspDisc_oneCuspDeck]

#print axioms cuspU_monodromy_projection
#print axioms cuspU_monodromy_eq_self_of_oneCuspDeck

/-- A based cusp lift agrees at every path endpoint with the marked projection
of transport of the matching modular fibre point. -/
theorem cuspLift_eq_projection_at_path_target {A : Type*} [TopologicalSpace A]
    (f : C(A, ({0,1}ᶜ : Set ℂ))) (F : C(A, PuncturedUnitDisc))
    (hF : cuspUPunctured ∘ F = f) {a b : A} (γ : Path a b)
    (e : lambdaPunctured ⁻¹' {f a}) (ha : F a = markedCuspDisc e) :
    F b = markedCuspDisc (lambdaPunctured_isCoveringMap.monodromy (.mk (γ.map f.continuous)) e) := by
  let Γ := F.comp γ.toContinuousMap
  have hΓ : cuspUPunctured ∘ (Γ : unitInterval → PuncturedUnitDisc) = γ.map f.continuous := by
    funext u
    exact congrFun hF (γ u)
  let ed : cuspUPunctured ⁻¹' {f a} := ⟨markedCuspDisc e, (cuspUPunctured_markedCuspDisc e).trans e.2⟩
  have h0 : Γ 0 = (ed : PuncturedUnitDisc) := by
    change F (γ 0) = markedCuspDisc e
    rw [γ.source, ha]
  have h1 : Γ 1 = F b := by
    change F (γ 1) = F b
    rw [γ.target]
  have hlift := cuspUPunctured_isCoveringMap.monodromy_eq_apply_one (Γ := Γ) (e := ed) hΓ h0
  rw [h1] at hlift
  exact hlift.symm.trans (cuspU_monodromy_projection (γ.map f.continuous) e)

#print axioms cuspLift_eq_projection_at_path_target
end BelgianChocolate.ModularLambdaRatio



