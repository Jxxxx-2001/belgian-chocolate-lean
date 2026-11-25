import ModularLambdaCovering
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Real reflection of the fixed Siegel lambda coordinate. -/
namespace BelgianChocolate.ModularLambdaReflection

open Complex UpperHalfPlane TauCeti.ModularForm
open BelgianChocolate.ModularLambdaRatio
open scoped MatrixGroups ComplexConjugate

private theorem conj_tprod (f : ℕ → ℂ) :
    (starRingEnd ℂ) (∏' n, f n) = ∏' n, (starRingEnd ℂ) (f n) :=
  Function.LeftInverse.map_tprod (g := starRingEnd ℂ) f continuous_conj continuous_conj
    (fun z => by simp)

private theorem qParam_reflection (h : ℝ) (τ : ℍ) :
    Function.Periodic.qParam h (↑(J • τ) : ℂ) =
      (starRingEnd ℂ) (Function.Periodic.qParam h (τ : ℂ)) := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, coe_J_smul, ← Complex.exp_conj]
  congr 1
  simp [map_ofNat]

private theorem zero_half_pow_four_reflection (τ : ℍ) :
    siegelFunction ![0, 1 / 2] (↑(J • τ) : ℂ) ^ 4 =
      (starRingEnd ℂ) (siegelFunction ![0, 1 / 2] (τ : ℂ) ^ 4) := by
  rw [siegelFunction_zero_half_pow_four (J • τ).im_pos,
    siegelFunction_zero_half_pow_four τ.im_pos, map_div₀, map_mul, map_ofNat,
    map_pow, conj_tprod]
  simp only [qParam_reflection, map_sub, map_one, map_pow]

private theorem half_half_pow_four_reflection (τ : ℍ) :
    siegelFunction ![1 / 2, 1 / 2] (↑(J • τ) : ℂ) ^ 4 =
      (starRingEnd ℂ) (siegelFunction ![1 / 2, 1 / 2] (τ : ℂ) ^ 4) := by
  have he : Complex.exp (-(Real.pi * Complex.I * (↑(J • τ) : ℂ) / 3)) =
      (starRingEnd ℂ) (Complex.exp (-(Real.pi * Complex.I * (τ : ℂ) / 3))) := by
    rw [coe_J_smul, ← Complex.exp_conj]
    congr 1
    simp [map_ofNat]
  rw [siegelFunction_half_half_pow_four (J • τ).im_pos,
    siegelFunction_half_half_pow_four τ.im_pos, map_neg, map_mul, map_pow, conj_tprod]
  simp only [he, qParam_reflection, map_sub, map_one, map_pow, map_neg]

/-- The standard reflection `τ ↦ -conj τ` covers complex conjugation
for the actual lambda ratio, with no branch or real-coefficient premise. -/
theorem lambdaRatio_J (τ : ℍ) :
    lambdaRatio (J • τ) = (starRingEnd ℂ) (lambdaRatio τ) := by
  rw [lambdaRatio, lambdaRatio, zero_half_pow_four_reflection,
    half_half_pow_four_reflection, map_div₀, map_neg]

#print axioms lambdaRatio_J
end BelgianChocolate.ModularLambdaReflection

