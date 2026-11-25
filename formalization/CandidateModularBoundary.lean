import SecondAnnulusSigns
import ModularLambdaCuspMarked

/-! Exact modular signs on the two marked boundary curves of the candidate. -/
namespace BelgianChocolate.CandidateModularBoundary
open Complex Set UpperHalfPlane
open scoped ComplexConjugate MatrixGroups
open BelgianChocolate.ModularLambdaRatio

theorem lambdaRatio_real_of_re_zero (τ : ℍ) (hτ : τ.re = 0) :
    (lambdaRatio τ).im = 0 := by
  have hJ : J • τ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_J_smul]
    apply Complex.ext
    · change -τ.re = τ.re
      rw [hτ, neg_zero]
    · simp
  have h := BelgianChocolate.ModularLambdaReflection.lambdaRatio_J τ
  rw [hJ] at h
  have hi := congrArg Complex.im h
  simp only [conj_im] at hi
  linarith

theorem lambdaRatio_between_of_re_zero (τ : ℍ) (hτ : τ.re = 0) :
    (lambdaRatio τ).im = 0 ∧ 0 < (lambdaRatio τ).re ∧ (lambdaRatio τ).re < 1 := by
  refine ⟨lambdaRatio_real_of_re_zero τ hτ,
    BelgianChocolate.SecondAnnulus.lambda_imaginaryAxis_between ?_ τ hτ⟩
  intro z hz
  exact (Complex.conj_eq_iff_im.mpr (lambdaRatio_real_of_re_zero z hz)).symm

theorem lambdaRatio_negative_of_re_one (τ : ℍ) (hτ : τ.re = 1) :
    (lambdaRatio τ).im = 0 ∧ (lambdaRatio τ).re < 0 := by
  let σ : ℍ := ⟨⟨0, τ.im⟩, τ.im_pos⟩
  have hσ : σ.re = 0 := rfl
  have hT : ModularGroup.T • σ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_T_smul]
    apply Complex.ext
    · simpa [σ] using hτ.symm
    · simp [σ]
  obtain ⟨him, hpos, hlt⟩ := lambdaRatio_between_of_re_zero σ hσ
  have he : lambdaRatio σ = ((lambdaRatio σ).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  rw [← hT, lambdaRatio_T, he]
  have hcast : ((lambdaRatio σ).re : ℂ) / (((lambdaRatio σ).re : ℂ) - 1) =
      (((lambdaRatio σ).re / ((lambdaRatio σ).re - 1) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  exact ⟨rfl, div_neg_of_pos_of_neg hpos (by linarith)⟩

theorem cuspU_marked_zero_axis (τ : ℍ) (hτ : τ.re = 0) :
    (cuspU (BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ))).im = 0 ∧
      0 < (cuspU (BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ))).re ∧
      (cuspU (BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ))).re < 1 := by
  rw [cuspU_markedCusp]
  exact lambdaRatio_between_of_re_zero τ hτ

theorem cuspU_marked_one_axis (τ : ℍ) (hτ : τ.re = 1) :
    (cuspU (BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ))).im = 0 ∧
      (cuspU (BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ))).re < 0 := by
  rw [cuspU_markedCusp]
  exact lambdaRatio_negative_of_re_one τ hτ

end BelgianChocolate.CandidateModularBoundary
