import ControllerCayley
import ControllerWitnessX
import ControllerWitnessY
import ControllerWitnessZ
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace BelgianChocolate.ControlWitness

open Polynomial

noncomputable def coeffPoly : List ℤ → ℚ[X]
  | [] => 0
  | a::as => C (a:ℚ) + X * coeffPoly as

@[simp] theorem coeffPoly_aeval (a : List ℤ) (s : ℂ) :
    aeval s (coeffPoly a) = evalCoeffs a s := by
  induction a with
  | nil => simp [coeffPoly,evalCoeffs]
  | cons a as ih => simp [coeffPoly,evalCoeffs,ih]

@[simp] theorem coeffPoly_add (a b : List ℤ) :
    coeffPoly (addCoeffs a b) = coeffPoly a + coeffPoly b := by
  induction a generalizing b with
  | nil => simp [addCoeffs,coeffPoly]
  | cons a as ih =>
    cases b with
    | nil => simp [addCoeffs,coeffPoly]
    | cons b bs => simp [addCoeffs,coeffPoly,ih]; ring

@[simp] theorem coeffPoly_scale (c : ℤ) (a : List ℤ) :
    coeffPoly (scaleCoeffs c a) = C (c:ℚ) * coeffPoly a := by
  induction a with
  | nil => simp [scaleCoeffs,coeffPoly]
  | cons a as ih =>
    change C ((c*a:ℤ):ℚ) + X * coeffPoly (scaleCoeffs c as) = _
    simp [coeffPoly,ih]
    ring

theorem coeffPoly_closedLoop (x y : List ℤ) :
    coeffPoly (closedLoopNums x y) =
      (C (deltaDen:ℚ)*(X^2+1) - C ((2*deltaNum:ℤ):ℚ)*X)*coeffPoly x +
        C (deltaDen:ℚ)*(X^2-1)*coeffPoly y := by
  simp [closedLoopNums,coeffPoly]
  ring

theorem coeffPoly_coeff (a : List ℤ) (n : ℕ) :
    (coeffPoly a).coeff n = ((a[n]?.getD 0 : ℤ):ℚ) := by
  induction a generalizing n with
  | nil => simp [coeffPoly]
  | cons a as ih =>
    cases n with
    | zero => simp [coeffPoly]
    | succ n =>
      rw [coeffPoly,Polynomial.coeff_add,Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero n),
        Polynomial.coeff_X_mul,zero_add,ih]
      rfl

theorem coeffPoly_degree (a : List ℤ) (n : ℕ) (hl : a.length=n+1)
    (hn : a[n]?.getD 0 ≠ 0) : (coeffPoly a).natDegree = n := by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [coeffPoly_coeff,List.getElem?_eq_none (by omega : a.length ≤ m)]
    simp
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [coeffPoly_coeff]
    exact_mod_cast hn

def witnessDelta : ℚ := deltaNum / (deltaDen:ℚ)
noncomputable def controllerX : ℚ[X] := C (1/(coefficientDenominator:ℚ)) * coeffPoly xNums
noncomputable def controllerY : ℚ[X] := C (1/(coefficientDenominator:ℚ)) * coeffPoly yNums
noncomputable def controllerZ : ℚ[X] :=
  C (1/((deltaDen:ℚ)*coefficientDenominator)) * coeffPoly zNums

theorem controllerZ_relation : controllerZ =
    (X^2-C (2*witnessDelta)*X+1)*controllerX + (X^2-1)*controllerY := by
  rw [controllerZ,zNums,coeffPoly_closedLoop,controllerX,controllerY]
  apply Polynomial.funext
  intro t
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  norm_num [witnessDelta,deltaNum,deltaDen,coefficientDenominator]
  ring

theorem controller_degrees : controllerX.natDegree=28 ∧ controllerY.natDegree=28 ∧
    controllerZ.natDegree=30 := by
  have hx := coeffPoly_degree xNums 28 x_exact_check.2.2.1 (by decide +kernel)
  have hy := coeffPoly_degree yNums 28 y_exact_check.2.2.1 (by decide +kernel)
  have hz := coeffPoly_degree zNums 30 z_exact_check.2.2.1 (by decide +kernel)
  unfold controllerX controllerY controllerZ
  rw [Polynomial.natDegree_C_mul (by norm_num [coefficientDenominator]),
    Polynomial.natDegree_C_mul (by norm_num [coefficientDenominator]),
    Polynomial.natDegree_C_mul (by norm_num [deltaDen,coefficientDenominator])]
  exact ⟨hx,hy,hz⟩

theorem controller_root_margin {s : ℂ} (hs : -(1/1000000000:ℝ) ≤ s.re) :
    aeval s controllerX ≠ 0 ∧ aeval s controllerY ≠ 0 ∧ aeval s controllerZ ≠ 0 := by
  have hx := closed_halfPlane_nonzero xNums _ x_exact_check.1 x_exact_check.2.1 hs
  have hy := closed_halfPlane_nonzero yNums _ y_exact_check.1 y_exact_check.2.1 hs
  have hz := closed_halfPlane_nonzero zNums _ z_exact_check.1 z_exact_check.2.1 hs
  simpa [controllerX,controllerY,controllerZ,coefficientDenominator,deltaDen]
    using And.intro hx (And.intro hy hz)

end BelgianChocolate.ControlWitness

