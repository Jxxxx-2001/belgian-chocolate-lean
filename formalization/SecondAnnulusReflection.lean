import ModularLambdaDeckReflection
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.ConjJ

namespace BelgianChocolate.SecondAnnulusReflection

open Complex UpperHalfPlane Filter Set Topology
open BelgianChocolate.ModularLambdaRatio BelgianChocolate.ModularLambdaReflection
open BelgianChocolate.FirstAnnulus
open TauCeti.UpperHalfPlane
open scoped MatrixGroups

private theorem pslConjJ_sl2z (M : SL(2, ℤ)) :
    pslConjJ (sl2zToPSL2R M) = sl2zToPSL2R (Matrix.SpecialLinearGroup.conjJ M) := by
  simp only [sl2zToPSL2R_apply, pslConjJ_mk]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change -((M 0 1 : ℤ) : ℝ) = ((-(M 0 1) : ℤ) : ℝ)
    simp only [Int.cast_neg]
  · change -((M 1 0 : ℤ) : ℝ) = ((-(M 1 0) : ℤ) : ℝ)
    simp only [Int.cast_neg]
  · rfl

private theorem conjJ_zero : Matrix.SpecialLinearGroup.conjJ zeroGenerator = zeroGenerator⁻¹ := by
  decide

private theorem conjJ_one : Matrix.SpecialLinearGroup.conjJ oneGenerator = oneGenerator⁻¹ := by
  decide

/-- Standard reflection reverses the actual zero-cusp deck generator. -/
theorem pslConjJ_zeroCuspDeck :
    pslConjJ (zeroCuspDeck : PSL(2, ℝ)) = ((zeroCuspDeck⁻¹ : gammaTwoProjective) : PSL(2, ℝ)) := by
  change pslConjJ (sl2zToPSL2R zeroGenerator) = (sl2zToPSL2R zeroGenerator)⁻¹
  rw [pslConjJ_sl2z, conjJ_zero, map_inv]

/-- Standard reflection reverses the actual one-cusp deck generator. -/
theorem pslConjJ_oneCuspDeck :
    pslConjJ (oneCuspDeck : PSL(2, ℝ)) = ((oneCuspDeck⁻¹ : gammaTwoProjective) : PSL(2, ℝ)) := by
  change pslConjJ (sl2zToPSL2R oneGenerator) = (sl2zToPSL2R oneGenerator)⁻¹
  rw [pslConjJ_sl2z, conjJ_one, map_inv]

theorem J_zeroCuspDeck (τ : ℍ) :
    J • (zeroCuspDeck • τ) = zeroCuspDeck⁻¹ • (J • τ) := by
  change J • ((zeroCuspDeck : PSL(2, ℝ)) • τ) =
    ((zeroCuspDeck⁻¹ : gammaTwoProjective) : PSL(2, ℝ)) • (J • τ)
  rw [J_smul_smul, pslConjJ_zeroCuspDeck]

theorem J_oneCuspDeck (τ : ℍ) :
    J • (oneCuspDeck • τ) = oneCuspDeck⁻¹ • (J • τ) := by
  change J • ((oneCuspDeck : PSL(2, ℝ)) • τ) =
    ((oneCuspDeck⁻¹ : gammaTwoProjective) : PSL(2, ℝ)) • (J • τ)
  rw [J_smul_smul, pslConjJ_oneCuspDeck]

/-- Reversing a loop inverts its deck label at the same initial lift. -/
theorem monodromy_inverse_label {b : ({0,1}ᶜ : Set ℂ)} (α : Path b b)
    (e : lambdaPunctured ⁻¹' {b}) (d : gammaTwoProjective)
    (hα : lambdaPunctured_isCoveringMap.monodromy (.mk α) e =
      lambdaPunctured_quotientCovering.toPermFiber b d e) :
    lambdaPunctured_isCoveringMap.monodromy (.mk α.symm) e =
      lambdaPunctured_quotientCovering.toPermFiber b d⁻¹ e := by
  let hc := lambdaPunctured_isCoveringMap
  let hp := lambdaPunctured_quotientCovering
  have hcancel : hc.monodromy (.mk α.symm) (hc.monodromy (.mk α) e) = e := by
    rw [Path.Homotopic.Quotient.mk_symm, ← hc.monodromy_trans_apply,
      Path.Homotopic.Quotient.trans_symm, hc.monodromy_refl]
    rfl
  rw [hα, hp.monodromy_toPermFiber] at hcancel
  have hh := congrArg (hp.toPermFiber b d⁻¹) hcancel
  have hleft : hp.toPermFiber b d⁻¹
      (hp.toPermFiber b d (hc.monodromy (.mk α.symm) e)) = hc.monodromy (.mk α.symm) e := by
    change ((hp.toPermFiber b d⁻¹) * (hp.toPermFiber b d)) _ = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  exact hleft.symm.trans hh

/-- Anti-equivariance of a known deck map turns pointwise reflection of the
actual loop into its conjugated inverse label. -/
theorem reflected_label_of_anti_equiv {b : ({0,1}ᶜ : Set ℂ)}
    (α β : Path b b) (e : lambdaPunctured ⁻¹' {b}) (g d : gammaTwoProjective)
    (hfix : deckReflection g (e : ℍ) = (e : ℍ))
    (hanti : ∀ τ : ℍ, J • (d • τ) = d⁻¹ • (J • τ))
    (hβ : ∀ u, (β u : ℂ) = (starRingEnd ℂ) (α u : ℂ))
    (hα : lambdaPunctured_isCoveringMap.monodromy (.mk α) e =
      lambdaPunctured_quotientCovering.toPermFiber b d e) :
    lambdaPunctured_isCoveringMap.monodromy (.mk β) e =
      lambdaPunctured_quotientCovering.toPermFiber b (g * d⁻¹ * g⁻¹) e := by
  apply Subtype.ext
  have hmono := reflected_loop_monodromy α β e g hfix hβ
  have hval : (lambdaPunctured_isCoveringMap.monodromy (.mk α) e : ℍ) = d • (e : ℍ) :=
    congrArg Subtype.val hα
  rw [hmono, hval]
  change g • (J • (d • (e : ℍ))) = (g * d⁻¹ * g⁻¹) • (e : ℍ)
  rw [hanti]
  calc
    g • (d⁻¹ • (J • (e : ℍ))) =
        (g * d⁻¹ * g⁻¹) • (g • (J • (e : ℍ))) := by
      simp only [mul_smul, inv_smul_smul]
    _ = (g * d⁻¹ * g⁻¹) • (e : ℍ) := congrArg (fun z => (g * d⁻¹ * g⁻¹) • z) hfix

/-- The zero-loop reflection relation forces the correcting deck map to
centralize the normalized zero-cusp generator. -/
theorem correction_commutes_zero {b : ({0,1}ᶜ : Set ℂ)}
    (α β : Path b b) (e : lambdaPunctured ⁻¹' {b}) (g : gammaTwoProjective)
    (hfix : deckReflection g (e : ℍ) = (e : ℍ))
    (hβ : ∀ u, (β u : ℂ) = (starRingEnd ℂ) (α u : ℂ))
    (hinverse : β.Homotopic α.symm)
    (hα : lambdaPunctured_isCoveringMap.monodromy (.mk α) e =
      lambdaPunctured_quotientCovering.toPermFiber b zeroCuspDeck e) :
    Commute g zeroCuspDeck := by
  have href := reflected_label_of_anti_equiv α β e g zeroCuspDeck hfix J_zeroCuspDeck hβ hα
  rw [Path.Homotopic.Quotient.eq.mpr hinverse] at href
  have hinv := monodromy_inverse_label α e zeroCuspDeck hα
  have hlabels := lambdaPunctured_quotientCovering.toPermFiber_ext b e (href.symm.trans hinv)
  have hh := congrArg (fun d => d * g) hlabels
  have hcomm : Commute g zeroCuspDeck⁻¹ := by
    change g * zeroCuspDeck⁻¹ = zeroCuspDeck⁻¹ * g
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  simpa only [inv_inv] using hcomm.inv_right

/-- The reflected plus-loop determines the third marked label. The real
competitor's reflection and the source loop homotopy remain explicit inputs;
the desired third label is a conclusion, not an assumption. -/
theorem third_label_of_reflection {b : ({0,1}ᶜ : Set ℂ)}
    (α β δ : Path b b) (e : lambdaPunctured ⁻¹' {b}) (g : gammaTwoProjective)
    (hfix : deckReflection g (e : ℍ) = (e : ℍ))
    (hβ : ∀ u, (β u : ℂ) = (starRingEnd ℂ) (α u : ℂ))
    (hinverse : β.Homotopic δ.symm)
    (hα : lambdaPunctured_isCoveringMap.monodromy (.mk α) e =
      lambdaPunctured_quotientCovering.toPermFiber b oneCuspDeck e) :
    lambdaPunctured_isCoveringMap.monodromy (.mk δ) e =
      lambdaPunctured_quotientCovering.toPermFiber b (g * oneCuspDeck * g⁻¹) e := by
  have href := reflected_label_of_anti_equiv α β e g oneCuspDeck hfix J_oneCuspDeck hβ hα
  rw [Path.Homotopic.Quotient.eq.mpr hinverse] at href
  have hinv := monodromy_inverse_label δ.symm e (g * oneCuspDeck⁻¹ * g⁻¹) href
  simpa only [Path.symm_symm, mul_inv_rev, inv_inv, mul_assoc] using hinv

#print axioms correction_commutes_zero
#print axioms third_label_of_reflection
end BelgianChocolate.SecondAnnulusReflection
