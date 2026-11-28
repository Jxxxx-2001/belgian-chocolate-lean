import Conjecture3
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

open Polynomial Polynomial.Chebyshev
namespace BelgianChocolate.Conjectures

/-- The review's fₙ represented by its numerator and denominator polynomials. -/
noncomputable def fₙ (n : ℕ) : ℝ[X] × ℝ[X] :=
  (-T ℝ ((n:ℤ)+1), T ℝ n)

theorem fₙ_zero : fₙ 0 = (-X,1) := by
  simp [fₙ]

/-- Multiplying the continued-fraction update by the new denominator. -/
theorem fₙ_succ (n : ℕ) :
    fₙ (n+1) =
      ((fₙ n).2 + 2*X*(fₙ n).1,
        -(fₙ n).1) := by
  simp only [fₙ, Nat.cast_add, Nat.cast_one, neg_neg, Prod.mk.injEq]
  constructor
  · rw [show (n:ℤ)+1+1 = (n:ℤ)+2 by ring, T_add_two]
    ring
  · trivial

private theorem not_common_root (n : ℕ) (δ : ℝ) :
    ¬ ((fₙ n).1.IsRoot δ ∧ (fₙ n).2.IsRoot δ) := by
  induction n with
  | zero => simp [fₙ_zero, IsRoot]
  | succ n ih =>
    rw [fₙ_succ]
    intro ⟨hN,hD⟩
    simp only [IsRoot, eval_add, eval_mul, eval_neg, eval_X, neg_eq_zero] at hN hD ⊢
    exact ih ⟨hD, by simpa [hD] using hN⟩

/-- The positive root in Conjecture 3 is the largest real root of the reduced numerator. -/
theorem continuedFraction_largest_positive_root {n : ℕ} (hn : 0 < n) :
    IsGreatest {δ : ℝ | 0 < δ ∧ (fₙ n).1.IsRoot δ ∧
        ¬ (fₙ n).2.IsRoot δ} (δₙ n) := by
  unfold δₙ
  let a := Real.pi/(2*((n:ℝ)+1))
  have ha : 0 < a := by positivity
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have ha' : a < Real.pi/2 := by
    dsimp [a]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hr : (fₙ n).1.IsRoot (Real.cos a) := by
    simp only [fₙ, IsRoot, eval_neg, neg_eq_zero, T_real_cos,
      Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [show ((n:ℝ)+1)*a = Real.pi/2 by dsimp [a]; field_simp, Real.cos_pi_div_two]
  refine ⟨⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],ha'⟩,hr,
    fun hd => not_common_root n _ ⟨hr,hd⟩⟩,?_⟩
  rintro δ ⟨_,hδ,_⟩
  have hδ' : (T ℝ (↑(n+1) : ℤ)).IsRoot δ := by
    simpa [fₙ,IsRoot] using hδ
  have hm := (mem_roots (T_ne_zero ℝ _)).mpr hδ'
  rw [roots_T_real] at hm
  change δ ∈ (Finset.range (n+1)).image _ at hm
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hm
  have hk' : (k:ℝ) ≤ n := by exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hkr : (0:ℝ) ≤ k := by positivity
  push_cast
  apply Real.strictAntiOn_cos.antitoneOn
  · exact ⟨ha.le,by linarith [Real.pi_pos]⟩
  · constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hk') Real.pi_pos.le, Real.pi_pos]
  · apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg hkr Real.pi_pos.le]

/-- Conjecture 3 in the review's notation δₙ*, δₙ and fₙ. -/
theorem conjecture3_continued_fraction {n : ℕ} (hn : 0 < n) :
    IsGreatest {δ : ℝ | 0 < δ ∧ (fₙ n).1.IsRoot δ ∧ ¬ (fₙ n).2.IsRoot δ} (δₙ n) ∧
      δₙ_star n ≤ δₙ n ∧
      δₙ n = Real.sin (((n:ℝ)+2)*Real.pi/(2*((n:ℝ)+1))) :=
  ⟨continuedFraction_largest_positive_root hn, conjecture3_sup hn, δₙ_eq_sin n⟩

#print axioms continuedFraction_largest_positive_root
#print axioms conjecture3_continued_fraction
end BelgianChocolate.Conjectures

