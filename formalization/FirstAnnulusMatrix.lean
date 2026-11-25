import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import AnnulusLengthArithmetic
import Mathlib.Tactic

/-! The integer matrix calculation after the first annulus trace bound. -/

namespace BelgianChocolate.FirstAnnulus

open Matrix
open scoped MatrixGroups

def zeroGenerator : SL(2, ℤ) :=
  ⟨!![1, 2; 0, 1], by norm_num [Matrix.det_fin_two_of]⟩

def oneGenerator : SL(2, ℤ) :=
  ⟨!![1, 0; -2, 1], by norm_num [Matrix.det_fin_two_of]⟩

def translate (k : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 2 * k; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem trace_zero_mul_conjugate_one (M : SL(2, ℤ)) :
    Matrix.trace (↑(zeroGenerator * M * oneGenerator * M⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) =
      2 - 4 * (M 1 1) ^ 2 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe M
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.trace_fin_two, Matrix.adjugate_fin_two]
  simp [zeroGenerator, oneGenerator, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]
  linear_combination 2 * hdet

theorem bottomRight_eq_neg_one_or_one_of_trace_bound {d : ℤ} (hodd : Odd d)
    (htrace : |2 - 4 * d ^ 2| < 34) : d = -1 ∨ d = 1 := by
  have hpos := (abs_lt.mp htrace).1
  have hsq : d ^ 2 < 9 := by linarith
  have hlo : -3 < d := by
    by_contra! hd
    nlinarith [mul_nonneg (show 0 ≤ -3 - d by omega) (show 0 ≤ 3 - d by omega)]
  have hhi : d < 3 := by
    by_contra! hd
    nlinarith [mul_nonneg (show 0 ≤ d - 3 by omega) (show 0 ≤ d + 3 by omega)]
  obtain ⟨k, hk⟩ := hodd
  omega

/-- An absolute first-annulus trace bound below 34 forces the lower-right
entry of the odd-diagonal conjugating matrix to have square one. -/
theorem bottomRight_sq_eq_one_of_trace_bound (M : SL(2, ℤ)) (hodd : Odd (M 1 1))
    (htrace : |Matrix.trace (↑(zeroGenerator * M * oneGenerator * M⁻¹) :
      Matrix (Fin 2) (Fin 2) ℤ)| < 34) : (M 1 1) ^ 2 = 1 := by
  rw [trace_zero_mul_conjugate_one] at htrace
  rcases bottomRight_eq_neg_one_or_one_of_trace_bound hodd htrace with h | h <;> simp [h]

private theorem translate_commutes_zero (k : ℤ) : Commute (translate k) zeroGenerator := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [translate, zeroGenerator, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem commute_one_of_entries (N : SL(2, ℤ))
    (hupper : N 0 1 = 0) (hdiag : N 0 0 = N 1 1) : Commute N oneGenerator := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [oneGenerator, Matrix.mul_apply, Fin.sum_univ_two, hupper, hdiag, add_comm, mul_comm]

/-- With the stated parity conditions, the first trace bound permits a single
even translation which fixes the zero generator and conjugates the other
monodromy to the one generator. -/
theorem exists_normalization_of_trace_bound (M : SL(2, ℤ))
    (hodd : Odd (M 1 1)) (heven : Even (M 0 1))
    (htrace : |Matrix.trace (↑(zeroGenerator * M * oneGenerator * M⁻¹) :
      Matrix (Fin 2) (Fin 2) ℤ)| < 34) :
    ∃ k : ℤ,
      translate k * zeroGenerator * (translate k)⁻¹ = zeroGenerator ∧
      translate k * (M * oneGenerator * M⁻¹) * (translate k)⁻¹ = oneGenerator := by
  have htrace' := htrace
  rw [trace_zero_mul_conjugate_one] at htrace'
  have hsign := bottomRight_eq_neg_one_or_one_of_trace_bound hodd htrace'
  obtain ⟨j, hj⟩ := heven
  let k : ℤ := -(j * M 1 1)
  let N : SL(2, ℤ) := translate k * M
  have hupper : N 0 1 = 0 := by
    change ((↑(translate k * M) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) = 0
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [translate, Matrix.mul_apply, Fin.sum_univ_two, k]
    rw [hj]
    rcases hsign with hd | hd <;> rw [hd] <;> ring
  have hbr : N 1 1 = M 1 1 := by
    change ((↑(translate k * M) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = _
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [translate, Matrix.mul_apply, Fin.sum_univ_two]
  have hdiag : N 0 0 = N 1 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe N
    rw [Matrix.det_fin_two] at hdet
    change N 0 0 * N 1 1 - N 0 1 * N 1 0 = 1 at hdet
    rw [hupper, zero_mul, sub_zero, hbr] at hdet
    rw [hbr]
    rcases hsign with hd | hd <;> rw [hd] at hdet ⊢ <;> omega
  refine ⟨k, ?_, ?_⟩
  · rw [(translate_commutes_zero k).eq]
    simp [mul_assoc]
  · calc
      translate k * (M * oneGenerator * M⁻¹) * (translate k)⁻¹ =
          N * oneGenerator * N⁻¹ := by simp [N, mul_assoc]
      _ = oneGenerator * N * N⁻¹ := by rw [(commute_one_of_entries N hupper hdiag).eq]
      _ = oneGenerator := by simp [mul_assoc]

/-- Conditional final arithmetic step for the first concrete annulus.
The input is the length inequality for the trace of the identified product. -/
theorem exists_normalization_of_length_bound (M : SL(2, ℤ))
    (hodd : Odd (M 1 1)) (heven : Even (M 0 1))
    (hlen : let trace : ℝ := (Matrix.trace (↑(zeroGenerator * M * oneGenerator * M⁻¹) :
      Matrix (Fin 2) (Fin 2) ℤ) : ℤ)
      2 * Real.arcosh (|trace| / 2) ≤ 2 * Real.pi ^ 2 / Real.log 17) :
    ∃ k : ℤ,
      translate k * zeroGenerator * (translate k)⁻¹ = zeroGenerator ∧
      translate k * (M * oneGenerator * M⁻¹) * (translate k)⁻¹ = oneGenerator := by
  have htrace := BelgianChocolate.AnnulusLengthArithmetic.abs_trace_lt_thirty_four hlen
  apply exists_normalization_of_trace_bound M hodd heven
  exact_mod_cast htrace

end BelgianChocolate.FirstAnnulus
