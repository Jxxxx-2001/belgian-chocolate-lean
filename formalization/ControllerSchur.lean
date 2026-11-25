import ControllerArithmetic
import Mathlib.Analysis.Complex.Basic

namespace BelgianChocolate.ControlWitness

open Complex

noncomputable def evalCoeffs : List ℤ → ℂ → ℂ
  | [], _ => 0
  | a::as, z => (a:ℂ) + z * evalCoeffs as z

@[simp] theorem eval_addCoeffs (a b : List ℤ) (z : ℂ) :
    evalCoeffs (addCoeffs a b) z = evalCoeffs a z + evalCoeffs b z := by
  induction a generalizing b with
  | nil => simp [addCoeffs,evalCoeffs]
  | cons a as ih =>
    cases b with
    | nil => simp [addCoeffs,evalCoeffs]
    | cons b bs => simp only [addCoeffs,evalCoeffs,Int.cast_add,ih]; ring

@[simp] theorem eval_scaleCoeffs (k : ℤ) (a : List ℤ) (z : ℂ) :
    evalCoeffs (scaleCoeffs k a) z = (k:ℂ)*evalCoeffs a z := by
  induction a with
  | nil => simp [scaleCoeffs,evalCoeffs]
  | cons a as ih =>
    change ↑(k*a) + z*evalCoeffs (scaleCoeffs k as) z = (k:ℂ)*(_ + _)
    rw [ih,Int.cast_mul]
    ring

@[simp] theorem eval_append_zero (a : List ℤ) (z : ℂ) :
    evalCoeffs (a++[0]) z = evalCoeffs a z := by
  induction a with
  | nil => simp [evalCoeffs]
  | cons a as ih => simp [evalCoeffs,ih]

@[simp] theorem eval_linMul (c d : ℤ) (a : List ℤ) (z : ℂ) :
    evalCoeffs (linMul c d a) z = ((c:ℂ)+(d:ℂ)*z)*evalCoeffs a z := by
  simp [linMul,evalCoeffs]
  ring

private theorem schur_norm_identity (l h : ℝ) (a b : ℂ) :
    Complex.normSq ((l:ℂ)*a-(h:ℂ)*b) - Complex.normSq ((l:ℂ)*b-(h:ℂ)*a) =
      (l^2-h^2)*(Complex.normSq a - Complex.normSq b) := by
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

/-- The certified reduction proves absence of roots on or outside the unit circle.
The induction also retains the modulus domination of the reversed polynomial. -/
theorem verifiedSchur_sound (ds a : List ℤ) (hc : verifiedSchur ds a = true)
    (z : ℂ) (hz : 1 ≤ ‖z‖) :
    evalCoeffs a z ≠ 0 ∧ ‖evalCoeffs a.reverse z‖ ≤ ‖evalCoeffs a z‖ := by
  induction ds generalizing a with
  | nil =>
    have h : a.length = 1 ∧ a.headD 0 ≠ 0 := of_decide_eq_true hc
    obtain ⟨v,rfl⟩ := List.length_eq_one_iff.mp h.1
    simpa [evalCoeffs] using h.2
  | cons d ds ih =>
    let L := a.getLastD 0
    let H := a.headD 0
    let b := (schurNumerator a).map (fun v => v/d)
    have hh := Bool.and_eq_true_iff.mp hc
    have hs : a.length = ds.length+2 ∧ H^2 < L^2 ∧ d ≠ 0 ∧
        addCoeffs (scaleCoeffs L a) (scaleCoeffs (-H) a.reverse) = 0 :: scaleCoeffs d b ∧
        addCoeffs (scaleCoeffs L a.reverse) (scaleCoeffs (-H) a) = scaleCoeffs d b.reverse ++ [0] :=
      of_decide_eq_true hh.1
    obtain ⟨hb0,hrev⟩ := ih b hh.2
    let A := evalCoeffs a z
    let B := evalCoeffs a.reverse z
    have hU : (L:ℂ)*A-(H:ℂ)*B = z*(d:ℂ)*evalCoeffs b z := by
      have he := congrArg (fun v => evalCoeffs v z) hs.2.2.2.1
      simpa [A,B,evalCoeffs,sub_eq_add_neg,mul_assoc] using he
    have hV : (L:ℂ)*B-(H:ℂ)*A = (d:ℂ)*evalCoeffs b.reverse z := by
      have he := congrArg (fun v => evalCoeffs v z) hs.2.2.2.2
      simpa [A,B,sub_eq_add_neg] using he
    have hd : (d:ℂ) ≠ 0 := by exact_mod_cast hs.2.2.1
    have hz₀ : z ≠ 0 := by intro he; norm_num [he] at hz
    have hU₀ : (L:ℂ)*A-(H:ℂ)*B ≠ 0 := hU ▸ mul_ne_zero (mul_ne_zero hz₀ hd) hb0
    have hn : ‖(L:ℂ)*B-(H:ℂ)*A‖ ≤ ‖(L:ℂ)*A-(H:ℂ)*B‖ := by
      rw [hU,hV,norm_mul,norm_mul,norm_mul]
      calc
        ‖(d:ℂ)‖*‖evalCoeffs b.reverse z‖ ≤ ‖(d:ℂ)‖*‖evalCoeffs b z‖ := by gcongr
        _ ≤ ‖z‖*‖(d:ℂ)‖*‖evalCoeffs b z‖ := by
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (norm_nonneg _) hz) (norm_nonneg _)
    have hn' := pow_le_pow_left₀ (norm_nonneg _) hn 2
    rw [Complex.sq_norm,Complex.sq_norm] at hn'
    have hr : (0:ℝ) < (L:ℝ)^2-(H:ℝ)^2 := by exact sub_pos.mpr (by exact_mod_cast hs.2.1)
    have he := schur_norm_identity (L:ℝ) (H:ℝ) A B
    push_cast at he
    have hpos : 0 ≤ ((L:ℝ)^2-(H:ℝ)^2)*(Complex.normSq A-Complex.normSq B) := by linarith
    have hnorm := nonneg_of_mul_nonneg_right hpos hr
    rw [← Complex.sq_norm,← Complex.sq_norm] at hnorm
    have hBA : ‖B‖ ≤ ‖A‖ := by nlinarith [norm_nonneg A,norm_nonneg B]
    refine ⟨?_, hBA⟩
    change A ≠ 0
    intro hA
    have hB : B = 0 := norm_le_zero_iff.mp (by simpa [hA] using hBA)
    exact hU₀ (by simp [hA,hB])

end BelgianChocolate.ControlWitness

