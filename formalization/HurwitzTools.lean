import ControllerFeasible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open Polynomial
open scoped BigOperators
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)

theorem strictStable_iff_no_roots (p : ℝ[X]) :
    StrictlyStable p ↔ ∀ s : ℂ, 0 ≤ s.re → aeval s p ≠ 0 := by
  constructor
  · intro h s hs hz
    exact (not_lt_of_ge hs) (h.2 s hz)
  · intro h
    refine ⟨?_, fun s hs => lt_of_not_ge (fun hsr => h s hsr hs)⟩
    intro hp
    exact h 0 (by simp) (by simp [hp])

theorem stable_of_mul_left {p q : ℝ[X]} (h : StrictlyStable (p * q)) :
    StrictlyStable q := by
  rw [strictStable_iff_no_roots] at h ⊢
  intro s hs hq
  exact h s hs (by simp [hq])

theorem stable_linear (a : ℝ) (ha : 0 < a) :
    StrictlyStable (X + C a) := by
  rw [strictStable_iff_no_roots]
  intro s hs hz
  simp only [map_add, aeval_X, aeval_C] at hz
  have hh := congrArg Complex.re hz
  simp at hh
  linarith

theorem stable_quadratic (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    StrictlyStable (X ^ 2 + C a * X + C b) := by
  rw [strictStable_iff_no_roots]
  intro s hs hz
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C] at hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [pow_two, Complex.mul_re] at hr
  simp [pow_two, Complex.mul_im] at hi
  have hsIm : s.im = 0 := by
    have hh : s.im * (2 * s.re + a) = 0 := by nlinarith only [hi]
    exact (mul_eq_zero.mp hh).resolve_right (by linarith)
  rw [hsIm] at hr
  nlinarith only [hr, hs, ha, hb, sq_nonneg s.re, mul_nonneg hs ha.le]

/-- Induction on monic Hurwitz polynomials by peeling off positive linear or quadratic factors. -/
theorem stable_induction {P : ℝ[X] → Prop}
    (hone : P 1)
    (linear : ∀ a p, 0 < a → p.Monic → StrictlyStable p → P p → P ((X + C a) * p))
    (quadratic : ∀ a b p, 0 < a → 0 < b → p.Monic → StrictlyStable p → P p →
      P ((X ^ 2 + C a * X + C b) * p))
    (p : ℝ[X]) (hm : p.Monic) (hs : StrictlyStable p) : P p := by
  generalize hn : p.natDegree = n
  induction n using Nat.strong_induction_on generalizing p with
  | ind n ih =>
    by_cases h0 : n = 0
    · have hp : p = 1 := hm.natDegree_eq_zero.mp (hn.trans h0)
      simpa [hp] using hone
    · have hdeg : p.degree ≠ 0 := by
        intro hh
        apply h0
        rw [← hn]
        rw [degree_eq_natDegree hs.1] at hh
        exact_mod_cast hh
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p hdeg
      have hzre := hs.2 z hz
      by_cases hi : z.im = 0
      · let a := -z.re
        have ha : 0 < a := neg_pos.mpr hzre
        have hzr : (z.re : ℂ) = z := Complex.ext rfl (by simpa using hi.symm)
        have hh : p.eval z.re = 0 := by
          have hw : ((aeval z.re p : ℝ) : ℂ) = 0 := by
            change (IsScalarTower.toAlgHom ℝ ℝ ℂ) (aeval z.re p) = 0
            rw [← aeval_algHom_apply]
            change aeval ((z.re : ℂ)) p = 0
            simpa only [hzr] using hz
          simpa [aeval_def] using (Complex.ofReal_eq_zero.mp hw)
        have hdiv : X + C a ∣ p := by
          simpa [a, sub_eq_add_neg] using (dvd_iff_isRoot.mpr hh : X - C z.re ∣ p)
        obtain ⟨q, hq⟩ := hdiv
        have hf : (X + C a).Monic := monic_X_add_C a
        have hqm : q.Monic := by
          unfold Polynomial.Monic
          have hhm := hm
          rw [hq, Polynomial.Monic, leadingCoeff_mul, hf, one_mul] at hhm
          exact hhm
        have hqs := stable_of_mul_left (hq ▸ hs)
        have hqn : q.natDegree < n := by
          have he := congrArg natDegree hq
          rw [hn, natDegree_mul hf.ne_zero hqm.ne_zero, natDegree_X_add_C] at he
          omega
        rw [hq]
        exact linear a q ha hqm hqs (ih _ hqn q hqm hqs rfl)
      · let a := -(2 * z.re)
        let b := ‖z‖ ^ 2
        have ha : 0 < a := by dsimp [a]; linarith
        have hb : 0 < b := by
          apply sq_pos_of_pos
          apply norm_pos_iff.mpr
          intro hz0
          apply hi
          simp [hz0]
        have hdiv : X ^ 2 + C a * X + C b ∣ p := by
          simpa [a, b, sub_eq_add_neg, neg_mul] using
            p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hi
        obtain ⟨q, hq⟩ := hdiv
        have hfd : (X ^ 2 + C a * X + C b).natDegree = 2 := by
          compute_degree <;> norm_num
        have hf : (X ^ 2 + C a * X + C b).Monic := by
          unfold Monic leadingCoeff
          rw [hfd]
          simp [coeff_add, coeff_X_pow]
        have hqm : q.Monic := by
          unfold Polynomial.Monic
          have hhm := hm
          rw [hq, Polynomial.Monic, leadingCoeff_mul, hf, one_mul] at hhm
          exact hhm
        have hqs := stable_of_mul_left (hq ▸ hs)
        have hqn : q.natDegree < n := by
          have he := congrArg natDegree hq
          rw [hn, natDegree_mul hf.ne_zero hqm.ne_zero, hfd] at he
          omega
        rw [hq]
        exact quadratic a b q ha hb hqm hqs (ih _ hqn q hqm hqs rfl)

theorem coeff_pos_mul {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hp' : ∀ k ≤ p.natDegree, 0 < p.coeff k)
    (hq' : ∀ k ≤ q.natDegree, 0 < q.coeff k) :
    ∀ k ≤ (p*q).natDegree, 0 < (p*q).coeff k := by
  intro k hk
  rw [natDegree_mul hp hq] at hk
  have hnn (r : ℝ[X]) (hr : ∀ j ≤ r.natDegree, 0 < r.coeff j) (j : ℕ) : 0 ≤ r.coeff j := by
    by_cases hj : j ≤ r.natDegree
    · exact (hr j hj).le
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
  rw [coeff_mul]
  let a := min k p.natDegree
  let b := k-a
  have hab : a + b = k := by dsimp [a,b]; omega
  refine Finset.sum_pos' (fun ij _ => mul_nonneg (hnn p hp' _) (hnn q hq' _)) ?_
  refine ⟨(a,b), Finset.mem_antidiagonal.mpr hab, mul_pos (hp' a (min_le_right ..)) (hq' b ?_)⟩
  dsimp [a,b]
  omega

theorem coeff_pos_of_monic_stable {p : ℝ[X]} (hp : p.Monic) (hs : StrictlyStable p) :
    ∀ k ≤ p.natDegree, 0 < p.coeff k := by
  apply stable_induction (P := fun r => ∀ k ≤ r.natDegree, 0 < r.coeff k) ?_ ?_ ?_ p hp hs
  · intro k hk
    have : k = 0 := by simpa using hk
    simp [this]
  · intro a q ha hm _ ih
    refine coeff_pos_mul (monic_X_add_C a).ne_zero hm.ne_zero ?_ ih
    intro k hk
    rw [natDegree_X_add_C] at hk
    interval_cases k <;> simp [ha]
  · intro a b q ha hb hm _ ih
    have hd : (X^2+C a*X+C b).natDegree = 2 := by
      compute_degree <;> norm_num
    have h : (X^2+C a*X+C b).Monic := by
      unfold Monic leadingCoeff
      rw [hd]
      simp [coeff_add, coeff_X_pow]
    refine coeff_pos_mul h.ne_zero hm.ne_zero ?_ ih
    intro k hk
    rw [hd] at hk
    interval_cases k <;> simp [coeff_add, coeff_X_pow, coeff_X, ha, hb]

end BelgianChocolate.Conjectures

