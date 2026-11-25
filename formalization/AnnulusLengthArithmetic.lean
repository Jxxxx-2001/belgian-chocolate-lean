import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace BelgianChocolate.AnnulusLengthArithmetic

/-- The first nonnegative term of the logarithm series. -/
private theorem log_ratio_lower {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
  have h := Real.sum_range_le_log_div hx₀ hx₁ 1
  simp only [Finset.sum_range_one, Nat.mul_zero, Nat.zero_add, pow_one] at h
  linarith

private theorem log_seventeen_lower : (283 / 100 : ℝ) < Real.log 17 := by
  have h := log_ratio_lower (x := 1 / 33) (by norm_num) (by norm_num)
  have hratio : (1 + 1 / 33) / (1 - 1 / 33) = (17 / 16 : ℝ) := by norm_num
  rw [hratio] at h
  have hsplit : Real.log 17 = 4 * Real.log 2 + Real.log (17 / 16) := by
    rw [show (17 : ℝ) = (2 : ℝ)^4 * (17 / 16) by norm_num, Real.log_mul (by positivity)
      (by norm_num), Real.log_pow]
    norm_num
  linarith [Real.log_two_gt_d9]

private theorem arcosh_seventeen_lower : (349 / 100 : ℝ) < Real.arcosh 17 := by
  have h := log_ratio_lower (x := 1 / 65) (by norm_num) (by norm_num)
  have hratio : (1 + 1 / 65) / (1 - 1 / 65) = (33 / 32 : ℝ) := by norm_num
  rw [hratio] at h
  have hsplit : Real.log 33 = 5 * Real.log 2 + Real.log (33 / 32) := by
    rw [show (33 : ℝ) = (2 : ℝ)^5 * (33 / 32) by norm_num, Real.log_mul (by positivity)
      (by norm_num), Real.log_pow]
    norm_num
  have hsqrt : (16 : ℝ) < Real.sqrt ((17 : ℝ)^2 - 1) := by
    exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hlog : Real.log 33 < Real.arcosh 17 := by
    unfold Real.arcosh
    apply Real.log_lt_log (by norm_num)
    linarith
  linarith [Real.log_two_gt_d9]

/-- The strict margin in the length estimate for the annulus of radius ratio 17. -/
theorem pi_sq_lt_log_mul_arcosh_seventeen :
    Real.pi ^ 2 < Real.log 17 * Real.arcosh 17 := by
  calc
    Real.pi ^ 2 < (3.1416 : ℝ)^2 :=
      pow_lt_pow_left₀ Real.pi_lt_d4 Real.pi_pos.le (by decide)
    _ < (283 / 100 : ℝ) * (349 / 100 : ℝ) := by norm_num
    _ < Real.log 17 * Real.arcosh 17 :=
      mul_lt_mul_of_pos' log_seventeen_lower arcosh_seventeen_lower
        (by norm_num) (by linarith [log_seventeen_lower])

theorem pi_sq_lt_log_mul_arcosh_of_seventeen_le {R : ℝ} (hR : 17 ≤ R) :
    Real.pi ^ 2 < Real.log R * Real.arcosh R := by
  have hR' : 1 < R := by linarith
  exact pi_sq_lt_log_mul_arcosh_seventeen.trans_le
    (mul_le_mul (Real.log_le_log (by norm_num) hR)
      ((Real.arcosh_le_arcosh (by norm_num) (by linarith)).2 hR)
      (Real.arcosh_nonneg (by norm_num)) (Real.log_pos hR').le)

/-- A strict annulus-length margin turns a weak translation-length bound into a strict trace bound. -/
theorem abs_trace_lt_twice_of_length_bound {R trace : ℝ} (hR : 1 < R)
    (hmargin : Real.pi ^ 2 < Real.log R * Real.arcosh R)
    (hlen : 2 * Real.arcosh (|trace| / 2) ≤ 2 * Real.pi ^ 2 / Real.log R) :
    |trace| < 2 * R := by
  have hlog := Real.log_pos hR
  have hquot : Real.pi ^ 2 / Real.log R < Real.arcosh R :=
    (div_lt_iff₀ hlog).2 (by simpa only [mul_comm (Real.log R)] using hmargin)
  have hlen' : Real.arcosh (|trace| / 2) < Real.arcosh R := by
    linarith [show 2 * Real.pi ^ 2 / Real.log R =
      2 * (Real.pi ^ 2 / Real.log R) by ring]
  by_contra! htrace
  have habs : 0 < |trace| / 2 := by linarith
  have hmono : Real.arcosh R ≤ Real.arcosh (|trace| / 2) :=
    (Real.arcosh_le_arcosh (by linarith) habs).2 (by linarith)
  exact (not_lt_of_ge hmono) hlen'

theorem abs_trace_lt_thirty_four {trace : ℝ}
    (hlen : 2 * Real.arcosh (|trace| / 2) ≤ 2 * Real.pi ^ 2 / Real.log 17) :
    |trace| < 34 := by
  have h := abs_trace_lt_twice_of_length_bound (R := 17) (by norm_num)
    pi_sq_lt_log_mul_arcosh_seventeen hlen
  norm_num at h
  exact h

theorem abs_trace_lt_thirty_eight {trace : ℝ}
    (hlen : 2 * Real.arcosh (|trace| / 2) ≤ 2 * Real.pi ^ 2 / Real.log 19) :
    |trace| < 38 := by
  have h := abs_trace_lt_twice_of_length_bound (R := 19) (by norm_num)
    (pi_sq_lt_log_mul_arcosh_of_seventeen_le (by norm_num)) hlen
  norm_num at h
  exact h

end BelgianChocolate.AnnulusLengthArithmetic

