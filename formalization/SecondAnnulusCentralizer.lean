import SecondAnnulusMatrix
import ModularLambdaCovering

namespace BelgianChocolate.SecondAnnulus

open Matrix Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open BelgianChocolate.FirstAnnulus BelgianChocolate.ModularLambdaRatio
open scoped MatrixGroups

theorem reps_eq_or_neg {M N : SL(2, ℤ)} (h : sl2zToPSL2R M = sl2zToPSL2R N) :
    M = N ∨ M = -N := by
  let D := M * N⁻¹
  have hker : D ∈ sl2zToPSL2R.ker := by
    rw [MonoidHom.mem_ker]
    change sl2zToPSL2R (M * N⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [sl2zToPSL2R_ker, Matrix.SpecialLinearGroup.mem_center_iff] at hker
  obtain ⟨s, hs, hD⟩ := hker
  have hs' : s^2 = 1 := by simpa using hs
  have he : s = 1 ∨ s = -1 := by
    have hz : (s - 1) * (s + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · left; omega
    · right; omega
  have hprod : D * N = M := by simp [D, mul_assoc]
  rcases he with rfl | rfl
  · left
    have h : D = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [← hD]
      simp
    simpa [h] using hprod.symm
  · right
    have h : D = -1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [← hD, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      by_cases hi : i = j <;> simp [hi]
    simpa [h] using hprod.symm

/-- The projective centralizer of the positive zero-cusp generator in
the effective level-two group consists of even translations. -/
theorem projective_centralizer_zero {M : SL(2, ℤ)}
    (hM : M ∈ CongruenceSubgroup.Gamma 2)
    (hc : Commute (sl2zToPSL2R M) (sl2zToPSL2R zeroGenerator)) :
    ∃ n : ℤ, sl2zToPSL2R M = sl2zToPSL2R (translate n) := by
  have he : sl2zToPSL2R (M * zeroGenerator) =
      sl2zToPSL2R (zeroGenerator * M) := by simpa only [map_mul] using hc.eq
  obtain ⟨_, h02, _, _⟩ := CongruenceSubgroup.Gamma_mem.mp hM
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h02
  rcases reps_eq_or_neg he with h | h
  · have hc₀ : M 1 0 = 0 := by
      have hh := congrArg (fun g : SL(2, ℤ) ↦ g 0 0) h
      change ((↑(M * zeroGenerator) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) =
        ((↑(zeroGenerator * M) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) at hh
      simp only [Matrix.SpecialLinearGroup.coe_mul] at hh
      simp [zeroGenerator, Matrix.mul_apply, Fin.sum_univ_two] at hh
      linarith
    have hdiag : M 0 0 = M 1 1 := by
      have hh := congrArg (fun g : SL(2, ℤ) ↦ g 0 1) h
      change ((↑(M * zeroGenerator) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) =
        ((↑(zeroGenerator * M) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) at hh
      simp only [Matrix.SpecialLinearGroup.coe_mul] at hh
      simp [zeroGenerator, Matrix.mul_apply, Fin.sum_univ_two] at hh
      linarith
    have hdet := M.det_coe
    rw [Matrix.det_fin_two] at hdet
    change M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 at hdet
    rw [hc₀, mul_zero, sub_zero, ← hdiag] at hdet
    have hs : M 0 0 = 1 ∨ M 0 0 = -1 := by
      have hz : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with h | h
      · left; omega
      · right; omega
    rcases hs with hs | hs
    · refine ⟨k, congrArg sl2zToPSL2R ?_⟩
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [translate, hc₀, hs, ← hdiag, hk]
    · refine ⟨-k, ?_⟩
      have he : M = -(translate (-k)) := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        rw [Matrix.SpecialLinearGroup.coe_neg]
        fin_cases i <;> fin_cases j <;> simp [translate, hc₀, hs, ← hdiag, hk]
      rw [he, sl2zToPSL2R_neg]
  · have hc₀ : M 1 0 = 0 := by
      have hh := congrArg (fun g : SL(2, ℤ) ↦ g 1 0) h
      change ((↑(M * zeroGenerator) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) =
        ((↑(-(zeroGenerator * M)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) at hh
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_mul, Matrix.neg_apply] at hh
      simp [zeroGenerator, Matrix.mul_apply, Fin.sum_univ_two] at hh
      linarith
    have hz : M 0 0 = 0 := by
      have hh := congrArg (fun g : SL(2, ℤ) ↦ g 0 0) h
      change ((↑(M * zeroGenerator) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) =
        ((↑(-(zeroGenerator * M)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) at hh
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_mul, Matrix.neg_apply] at hh
      simp [zeroGenerator, Matrix.mul_apply, Fin.sum_univ_two, hc₀] at hh
      linarith
    have hd := M.det_coe
    rw [Matrix.det_fin_two] at hd
    change M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 at hd
    simp [hz, hc₀] at hd

theorem translate_coe_smul (n : ℤ) (z : ℍ) :
    ((translate n • z : ℍ) : ℂ) = (z : ℂ) + (2*n : ℤ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [translate]

end BelgianChocolate.SecondAnnulus

