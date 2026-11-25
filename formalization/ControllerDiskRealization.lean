import ControllerFeasible
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Operations

namespace BelgianChocolate.ControlWitness

open Complex Polynomial Finset

/-- Clearing the denominator of `a((s-1)/(s+1))` to order `n`. -/
noncomputable def controlPullback (a : ℝ[X]) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (n+1), C (a.coeff k) * (X-1)^k * (X+1)^(n-k)

theorem controlPullback_degree (a : ℝ[X]) (n : ℕ) : (controlPullback a n).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have h : k ≤ n := by simpa using hk
  have hminus : (X-1 : ℝ[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1:ℝ)
  have hplus : (X+1 : ℝ[X]).natDegree = 1 := by simp
  calc
    _ ≤ (C (a.coeff k)*(X-1)^k).natDegree + ((X+1)^(n-k) : ℝ[X]).natDegree := natDegree_mul_le
    _ ≤ (C (a.coeff k)).natDegree + ((X-1)^k : ℝ[X]).natDegree +
          ((X+1)^(n-k) : ℝ[X]).natDegree := Nat.add_le_add_right natDegree_mul_le _
    _ = n := by simp [natDegree_pow,hminus,hplus]; omega

theorem controlPullback_eval (a : ℝ[X]) (n : ℕ) (hn : a.natDegree ≤ n)
    (s : ℂ) (hs : s+1 ≠ 0) :
    aeval s (controlPullback a n) = (s+1)^n * aeval ((s-1)/(s+1)) a := by
  rw [aeval_eq_sum_range' (show a.natDegree<n+1 by omega) ((s-1)/(s+1)),mul_sum]
  simp only [controlPullback,map_sum,map_mul,aeval_C,map_pow,map_sub,map_add,aeval_X,map_one]
  apply sum_congr rfl
  intro k hk
  have h : k ≤ n := by simpa using hk
  have hp : (s+1)^n = (s+1)^(n-k)*(s+1)^k := by rw [← pow_add,Nat.sub_add_cancel h]
  rw [Algebra.smul_def,div_pow,hp]
  field_simp

private theorem closed_half_plane_to_disk {s : ℂ} (hs : 0 ≤ s.re) :
    s+1 ≠ 0 ∧ ‖(s-1)/(s+1)‖ ≤ 1 := by
  have hd : s+1 ≠ 0 := by
    intro e
    have er := congrArg Complex.re e
    simp at er
    linarith
  refine ⟨hd,?_⟩
  rw [norm_div,div_le_one (norm_pos_iff.mpr hd)]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),Complex.sq_norm,Complex.sq_norm]
  simp [Complex.normSq_apply]
  linarith

private theorem strictlyStable_of_nonzero (p : ℝ[X])
    (h : ∀ s : ℂ, 0 ≤ s.re → aeval s p ≠ 0) : StrictlyStable p := by
  refine ⟨?_,fun s hs => lt_of_not_ge (fun h' => h s h' hs)⟩
  intro hp
  simpa [hp] using h 0 (by simp)

/-- A zero-free polynomial approximation on the closed disk gives a finite controller.
Both unit conditions are imposed only on the closed disk. -/
theorem feasible_of_disk_polynomial {δ : ℝ} (hδ : δ < 1) (a : ℝ[X])
    (ha : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z a ≠ 0)
    (hd : ∀ z : ℂ, ‖z‖ ≤ 1 →
      1 + z^2 * (1+(δ:ℂ))/(1-(δ:ℂ)) + z * aeval z a ≠ 0) :
    Feasible δ := by
  let n := a.natDegree
  let x : ℝ[X] := C (2/(1-δ))*(X+1)^n
  let y := controlPullback a n
  have hδn : 1-δ ≠ 0 := by linarith
  have hδc : 1-(δ:ℂ) ≠ 0 := by exact_mod_cast hδn
  have hxdeg : x.natDegree = n := by
    have hh : (X+1:ℝ[X]).natDegree = 1 := by simp
    have hn : (2/(1-δ):ℝ) ≠ 0 := div_ne_zero two_ne_zero hδn
    rw [show x = _ from rfl,natDegree_C_mul hn,natDegree_pow,hh,mul_one]
  have hxe (s : ℂ) : aeval s x = (2/(1-(δ:ℂ)))*(s+1)^n := by simp [x]
  refine ⟨x,y,strictlyStable_of_nonzero _ ?_,strictlyStable_of_nonzero _ ?_,
    hxdeg ▸ controlPullback_degree a n,strictlyStable_of_nonzero _ ?_⟩
  · intro s hs
    rw [hxe]
    exact mul_ne_zero (div_ne_zero (by norm_num) hδc) (pow_ne_zero _ (closed_half_plane_to_disk hs).1)
  · intro s hs
    obtain ⟨hne,hball⟩ := closed_half_plane_to_disk hs
    exact (controlPullback_eval a n le_rfl s hne) ▸ mul_ne_zero (pow_ne_zero _ hne) (ha _ hball)
  · intro s hs
    obtain ⟨hne,hball⟩ := closed_half_plane_to_disk hs
    let z := (s-1)/(s+1)
    have he : aeval s y = (s+1)^n * aeval z a := controlPullback_eval a n le_rfl s hne
    have hB : 1+z^2*(1+(δ:ℂ))/(1-(δ:ℂ))+z*aeval z a ≠ 0 := hd z hball
    have hq : aeval s ((X^2-C (2*δ)*X+1)*x + (X^2-1)*y) =
        (s+1)^(n+2)*(1+z^2*(1+(δ:ℂ))/(1-(δ:ℂ))+z*aeval z a) := by
      simp only [map_add,map_sub,map_mul,map_pow,aeval_X,aeval_C,map_one,hxe,he]
      push_cast
      rw [pow_add]
      dsimp [z]
      field_simp [hne,hδc]
      ring
    rw [hq]
    exact mul_ne_zero (pow_ne_zero _ hne) hB

end BelgianChocolate.ControlWitness

