import FirstAnnulusModularGenerators

/-! Trace calculation and integer exclusion for the second annulus.
The word is read from left to right, starting at the prescribed basepoint. -/

namespace BelgianChocolate.SecondAnnulus

open Matrix
open BelgianChocolate.FirstAnnulus
open scoped MatrixGroups

/-- The first, reflected letter of the three-puncture peripheral word. -/
def reflectedGenerator (n : ℤ) : SL(2, ℤ) :=
  translate n * oneGenerator * (translate n)⁻¹

/-- Lower puncture, zero, upper puncture, in path execution order. -/
def tripleMatrix (n : ℤ) : SL(2, ℤ) :=
  reflectedGenerator n * zeroGenerator * oneGenerator

theorem reflectedGenerator_entries (n : ℤ) :
    ((reflectedGenerator n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1 - 4*n, 8*n^2; -2, 1 + 4*n] := by
  simp only [reflectedGenerator, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  change !![1, 2*n; 0, 1] * !![1, 0; -2, 1] * Matrix.adjugate !![1, 2*n; 0, 1] = _
  rw [Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem tripleMatrix_trace (n : ℤ) :
    Matrix.trace (↑(tripleMatrix n) : Matrix (Fin 2) (Fin 2) ℤ) =
      -(16*n*(n-1)+6) := by
  simp only [tripleMatrix, Matrix.SpecialLinearGroup.coe_mul, reflectedGenerator_entries,
    Matrix.trace_fin_two]
  change ((!![1 - 4*n, 8*n^2; -2, 1 + 4*n] * !![1, 2; 0, 1] * !![1, 0; -2, 1] :
    Matrix (Fin 2) (Fin 2) ℤ) 0 0) + _ = _
  simp [zeroGenerator, oneGenerator, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

theorem one_of_odd_and_trace_lt_thirty_eight {n : ℤ} (hodd : Odd n)
    (htrace : |Matrix.trace (↑(tripleMatrix n) : Matrix (Fin 2) (Fin 2) ℤ)| < 38) :
    n = 1 := by
  rw [tripleMatrix_trace] at htrace
  have hsmall : n * (n - 1) < 2 := by linarith [(abs_lt.mp htrace).1]
  have hlo : 0 ≤ n := by
    by_contra! hn
    have h : 0 ≤ (-1-n)*(-n) := mul_nonneg (by omega) (by omega)
    nlinarith
  have hhi : n < 2 := by
    by_contra! hn
    have h : 0 ≤ (n-2)*(n+1) := mul_nonneg (by omega) (by omega)
    nlinarith
  obtain ⟨k, hk⟩ := hodd
  omega

theorem one_of_odd_and_length_bound {n : ℤ} (hodd : Odd n)
    (hlen : let tr : ℝ := (Matrix.trace (↑(tripleMatrix n) :
      Matrix (Fin 2) (Fin 2) ℤ) : ℤ)
      2 * Real.arcosh (|tr| / 2) ≤ 2 * Real.pi ^ 2 / Real.log 19) :
    n = 1 := by
  apply one_of_odd_and_trace_lt_thirty_eight hodd
  have h := BelgianChocolate.AnnulusLengthArithmetic.abs_trace_lt_thirty_eight hlen
  exact_mod_cast h

theorem translate_mem_gammaTwo (n : ℤ) : translate n ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  change ((1 : ℤ) : ZMod 2) = 1 ∧ ((2*n : ℤ) : ZMod 2) = 0 ∧
    ((0 : ℤ) : ZMod 2) = 0 ∧ ((1 : ℤ) : ZMod 2) = 1
  push_cast
  simp [show (2 : ZMod 2) = 0 by decide]

theorem reflectedGenerator_mem_gammaTwo (n : ℤ) :
    reflectedGenerator n ∈ CongruenceSubgroup.Gamma 2 :=
  (CongruenceSubgroup.Gamma 2).mul_mem
    ((CongruenceSubgroup.Gamma 2).mul_mem (translate_mem_gammaTwo n) oneGenerator_mem_gammaTwo)
    ((CongruenceSubgroup.Gamma 2).inv_mem (translate_mem_gammaTwo n))

end BelgianChocolate.SecondAnnulus

