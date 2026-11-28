import SexticOddSign
import Degree6Witness

open Polynomial
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)
set_option maxHeartbeats 1800000

/-- The coefficient of z_j in the cosine balance. -/
def weight (d : ℝ) : ℕ → ℝ
  | 0 => d | 1 => 1 | 2 => d | 3 => 2*d^2-1
  | 4 => 4*d^3-3*d | 5 => 8*d^4-8*d^2+1
  | 6 => 16*d^5-20*d^3+5*d | 7 => 32*d^6-48*d^4+18*d^2-1
  | 8 => 64*d^7-112*d^5+56*d^3-7*d | _ => 0

def oddCoeff (d : ℝ) : ℕ → ℕ → ℝ
  | 1, 3 => 1 | 1, 4 => 2*d | 1, 5 => 4*d^2-1
  | 1, 6 => 8*d^3-4*d | 1, 7 => 16*d^4-12*d^2+1
  | 1, 8 => 32*d^5-32*d^3+6*d
  | 3, 5 => 1 | 3, 6 => 2*d | 3, 7 => 4*d^2-1 | 3, 8 => 8*d^3-4*d
  | 5, 7 => 1 | 5, 8 => 2*d | _, _ => 0

def oddWeight (d t : ℝ) (j : ℕ) : ℝ :=
  oddCoeff d 1 j - t * oddCoeff d 3 j + t^2 * oddCoeff d 5 j

private theorem theta_lt_tenth {d : ℝ} (hlo : 11/12 ≤ d^2) (hd : 0 < d) (hd' : d < 1) :
    0 < Real.arccos d ∧ Real.arccos d < Real.pi/10 := by
  let θ := Real.arccos d
  have h0 : 0 < θ := Real.arccos_pos.2 hd'
  have h1 : θ < Real.pi/2 := Real.arccos_lt_pi_div_two.2 hd
  have hcos : Real.cos θ = d := Real.cos_arccos (by linarith) hd'.le
  have hs : Real.sqrt 5 < 7/3 := by
    have hs2 : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
    by_contra! hb
    nlinarith only [hs2, mul_nonneg (sub_nonneg.mpr hb)
      (show 0 ≤ Real.sqrt 5+(7/3:ℝ) by positivity)]
  have hlt : Real.cos (Real.pi/5) < Real.cos (2*θ) := by
    rw [Real.cos_pi_div_five,Real.cos_two_mul,hcos]
    linarith
  refine ⟨h0,?_⟩
  by_contra! hn
  have hh := Real.strictAntiOn_cos.antitoneOn
    (show Real.pi/5 ∈ Set.Icc 0 Real.pi from ⟨by positivity,by linarith [Real.pi_pos]⟩)
    (show 2*θ ∈ Set.Icc 0 Real.pi from ⟨by positivity,by linarith⟩)
    (show Real.pi/5 ≤ 2*θ by linarith)
  exact hlt.not_ge hh

private theorem cosine_recurrence (a θ : ℝ) :
    Real.cos (a+θ) = 2*Real.cos θ*Real.cos a - Real.cos (a-θ) := by
  rw [Real.cos_add,Real.cos_sub]
  ring

private theorem weight_cos (θ : ℝ) {j : ℕ} (hj : j < 9) :
    weight (Real.cos θ) j = Real.cos (((j:ℝ)-1)*θ) := by
  have hrec (k : ℕ) : Real.cos (((k:ℝ)+2)*θ) =
      2*Real.cos θ*Real.cos (((k:ℝ)+1)*θ) - Real.cos ((k:ℝ)*θ) := by
    rw [show ((k:ℝ)+2)*θ = ((k:ℝ)+1)*θ+θ by ring,
      cosine_recurrence, show ((k:ℝ)+1)*θ-θ = (k:ℝ)*θ by ring]
  have h2 := hrec 0
  have h3 := hrec 1
  have h4 := hrec 2
  have h5 := hrec 3
  have h6 := hrec 4
  have h7 := hrec 5
  norm_num at h2 h3 h4 h5 h6 h7
  have c2 : Real.cos (2*θ) = 2*Real.cos θ^2-1 := by nlinarith only [h2]
  have c3 : Real.cos (3*θ) = 4*Real.cos θ^3-3*Real.cos θ := by rw [h3,c2]; ring
  have c4 : Real.cos (4*θ) = 8*Real.cos θ^4-8*Real.cos θ^2+1 := by rw [h4,c3,c2]; ring
  have c5 : Real.cos (5*θ) = 16*Real.cos θ^5-20*Real.cos θ^3+5*Real.cos θ := by
    rw [h5,c4,c3]; ring
  have c6 : Real.cos (6*θ) = 32*Real.cos θ^6-48*Real.cos θ^4+18*Real.cos θ^2-1 := by
    rw [h6,c5,c4]; ring
  have c7 : Real.cos (7*θ) = 64*Real.cos θ^7-112*Real.cos θ^5+56*Real.cos θ^3-7*Real.cos θ := by
    rw [h7,c6,c5]; ring
  interval_cases j <;> norm_num [weight,Real.cos_neg,c2,c3,c4,c5,c6,c7]

private theorem weight_first_pos (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi/10)
    {j : ℕ} (hj : j ≤ 6) : 0 < weight (Real.cos θ) j := by
  rw [weight_cos θ (by omega)]
  apply Real.cos_pos_of_mem_Ioo
  have hjr : (j:ℝ) ≤ 6 := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ j := by positivity
  constructor
  · nlinarith [mul_nonneg hj0 hθ.le, Real.pi_pos]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hjr) hθ.le]

private theorem quad_nonneg {a b c t : ℝ} (hc : 0 < c) (h : 0 ≤ 4*a*c-b^2) :
    0 ≤ a-t*b+t^2*c := by
  apply nonneg_of_mul_nonneg_left _ (show 0 < 4*c by positivity)
  nlinarith only [h, sq_nonneg (2*c*t-b)]

private theorem pure_nonneg {d t : ℝ} (hd : 0 < d) (hd' : d < 1)
    (hu : 11/12 ≤ d^2) {j : ℕ} (hj : j=7 ∨ j=8) : 0 ≤ oddWeight d t j := by
  have hu' : d^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hd'.le) (show 0 ≤ 1+d by positivity)]
  rcases hj with rfl|rfl
  · unfold oddWeight
    apply quad_nonneg (by norm_num [oddCoeff])
    have he : 4 * oddCoeff d 1 7 * oddCoeff d 5 7 - oddCoeff d 3 7 ^ 2 =
        8*d^2*(6*d^2-5)+3 := by simp [oddCoeff]; ring
    rw [he]
    have h : 0 ≤ 6*d^2-5 := by linarith
    positivity
  · unfold oddWeight
    apply quad_nonneg (by simp [oddCoeff,hd])
    have he : 4 * oddCoeff d 1 8 * oddCoeff d 5 8 - oddCoeff d 3 8 ^ 2 =
        32*d^2*(1-6*d^2*(1-d^2)) := by simp [oddCoeff]; ring
    rw [he]
    have hr : 0 ≤ 1-6*d^2*(1-d^2) := by
      nlinarith only [hu,hu',mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr hu')]
    positivity

def rScale (d : ℝ) : ℕ → ℝ
  | 0 => 1 | 1 => 2*d | 2 => 4*d^2-1 | _ => 8*d^3-4*d

def truncCorrection (d : ℝ) : ℕ → ℝ
  | 4 => 2*d | 5 => 1 | _ => 0

private theorem ray_identities (d : ℝ) {i j : ℕ} (hi : 4 ≤ i) (hij : i < j)
    (hj : j=7 ∨ j=8) :
    let L := rScale d (j-i-1)
    weight d i * oddCoeff d 1 j - weight d j * oddCoeff d 1 i = L*d ∧
    weight d i * oddCoeff d 3 j - weight d j * oddCoeff d 3 i = L*weight d 4 ∧
    weight d i * oddCoeff d 5 j - weight d j * oddCoeff d 5 i =
      L*weight d 6 - weight d j * truncCorrection d i := by
  rcases hj with rfl|rfl <;>
    interval_cases i <;> refine ⟨?_,?_,?_⟩ <;>
    norm_num [weight,oddCoeff,rScale,truncCorrection] <;> ring

private theorem ray_nonneg {d t : ℝ} (hd : 0 < d) (hd' : d < 1) (hu : 11/12 ≤ d^2)
    (hfive : 0 < weight d 6) {i j : ℕ} (hi : 0 < weight d i)
    (hjneg : weight d j < 0) (hij : i < j) (hj : j=7 ∨ j=8) :
    0 ≤ (-weight d j)*oddWeight d t i + weight d i*oddWeight d t j := by
  by_cases hit : i ≤ 3
  · have ho : 0 ≤ oddWeight d t i := by
      interval_cases i <;> norm_num [oddWeight,oddCoeff]
    exact add_nonneg (mul_nonneg (neg_nonneg.mpr hjneg.le) ho)
      (mul_nonneg hi.le (pure_nonneg hd hd' hu hj))
  · have hid : 4 ≤ i := by omega
    let L := rScale d (j-i-1)
    obtain ⟨h1,h3,h5⟩ := ray_identities d hid hij hj
    have hl : 0 < L := by
      have ht : j-i-1 ≤ 3 := by rcases hj with rfl|rfl <;> omega
      dsimp only [L]
      interval_cases j-i-1 <;> simp only [rScale]
      · norm_num
      · positivity
      · nlinarith only [hu]
      · have hp : 0 < d*(8*d^2-4) := mul_pos hd (by linarith)
        nlinarith only [hp]
    have hcorr : 0 ≤ truncCorrection d i := by
      unfold truncCorrection
      split <;> positivity
    have hid2 : 4*d*weight d 6 - (weight d 4)^2 =
        d^2*(12*d^2-11)*(4*d^2-1) := by simp [weight]; ring
    have hbase : 0 ≤ d-t*weight d 4+t^2*weight d 6 := by
      apply quad_nonneg hfive
      rw [hid2]
      exact mul_nonneg (mul_nonneg (sq_nonneg d) (by linarith)) (by linarith)
    have he : (-weight d j)*oddWeight d t i + weight d i*oddWeight d t j =
        L*(d-t*weight d 4+t^2*weight d 6) +
          t^2*((-weight d j)*truncCorrection d i) := by
      dsimp only [oddWeight]
      change _ = rScale d (j-i-1) * _ + _
      linear_combination h1-t*h3+t^2*h5
    rw [he]
    exact add_nonneg (mul_nonneg hl.le hbase)
      (mul_nonneg (sq_nonneg t) (mul_nonneg (neg_nonneg.mpr hjneg.le) hcorr))

private theorem sum_nonneg_of_pairs (C q z : ℕ → ℝ)
    (hz : ∀ j < 9, 0 < z j) (hC : 0 < C 0)
    (hzero : ∑ j ∈ Finset.range 9, C j*z j=0)
    (hneutral : ∀ j < 9, C j=0 → 0 ≤ q j)
    (hpair : ∀ i j, i < 9 → j < 9 → 0 < C i → C j < 0 →
      0 ≤ (-C j)*q i+C i*q j) :
    0 ≤ ∑ j ∈ Finset.range 9, z j*q j := by
  classical
  let ss := (Finset.range 9).filter (fun j => C j < 0)
  have hn : ss.Nonempty := by
    by_contra! h
    have hnn : ∀ j ∈ Finset.range 9, 0 ≤ C j := by
      intro j hj
      by_contra! hj'
      have hm : j ∈ ss := Finset.mem_filter.mpr ⟨hj,hj'⟩
      rw [h] at hm
      exact Finset.notMem_empty j hm
    have hs : 0 < ∑ j ∈ Finset.range 9, C j*z j := by
      refine Finset.sum_pos' (fun j hj => mul_nonneg (hnn j hj)
        (hz j (Finset.mem_range.mp hj)).le) ?_
      exact ⟨0, by decide, mul_pos hC (hz 0 (by decide))⟩
    linarith
  let f := fun j => q j/(-C j)
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image ss f hn
  have hj' : j < 9 ∧ C j < 0 := by
    simpa [ss] using hj
  have hQ : ∀ i < 9, 0 ≤ q i+f j*C i := by
    intro i hi
    rcases lt_trichotomy (C i) 0 with hneg|h0|hpos
    · have h := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hneg⟩)
      dsimp [f] at h ⊢
      have hh := (le_div_iff₀ (show 0 < -C i by linarith)).mp h
      linarith
    · rw [h0,mul_zero,add_zero]
      exact hneutral i hi h0
    · dsimp [f]
      have hp := hpair i j hi hj'.1 hpos hj'.2
      have hden : 0 < -C j := by linarith
      apply nonneg_of_mul_nonneg_left _ hden
      calc
        (q i + q j/(-C j)*C i)*(-C j) = (-C j)*q i+C i*q j := by
          rw [add_mul, mul_right_comm _ (C i), div_mul_cancel₀ _ hden.ne']
          ring
        _ ≥ 0 := hp
  have hs := Finset.sum_nonneg (s:=Finset.range 9) fun i hi =>
    mul_nonneg (hz i (Finset.mem_range.mp hi)).le (hQ i (Finset.mem_range.mp hi))
  have hev : (∑ i ∈ Finset.range 9, z i*(q i+f j*C i)) =
      (∑ i ∈ Finset.range 9, z i*q i)+f j*(∑ i ∈ Finset.range 9, C i*z i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [hev,hzero,mul_zero,add_zero] at hs

private theorem loop_coeff_succ (d y : ℝ) (x : ℝ[X]) (k : ℕ) :
    (loop d x y).coeff (k+3) =
      x.coeff (k+1)-2*d*x.coeff (k+2)+x.coeff (k+3) := by
  rw [show loop d x y = X*(X*x) - C (2*d)*(X*x)+x+(X^2-1)*C y by
    unfold loop plant; ring]
  simp only [coeff_add,coeff_sub,coeff_X_mul,coeff_C_mul,sub_mul,coeff_mul_C,coeff_X_pow,
    coeff_one,show k+3≠2 by omega,show k+3≠0 by omega, ite_false, zero_mul, sub_zero, add_zero]

private theorem odd_linear (d y : ℝ) (x : ℝ[X]) (hd : x.natDegree=6) (t : ℝ) :
    x.coeff 1-t*x.coeff 3+t^2*x.coeff 5 =
      ∑ j ∈ Finset.range 9, (loop d x y).coeff j * oddWeight d t j := by
  have hx7 : x.coeff 7=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hx8 : x.coeff 8=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h0 := loop_coeff_succ d y x 0
  have h1 := loop_coeff_succ d y x 1
  have h2 := loop_coeff_succ d y x 2
  have h3 := loop_coeff_succ d y x 3
  have h4 := loop_coeff_succ d y x 4
  have h5 := loop_coeff_succ d y x 5
  norm_num [hx7,hx8] at h0 h1 h2 h3 h4 h5
  norm_num [Finset.sum_range_succ, oddWeight, oddCoeff]
  linear_combination -h0-2*d*h1-(4*d^2-1-t)*h2-(8*d^3-4*d-2*d*t)*h3-
    (16*d^4-12*d^2+1-(4*d^2-1)*t+t^2)*h4-
    (32*d^5-32*d^3+6*d-(8*d^3-4*d)*t+2*d*t^2)*h5

/-- The upper bound for strictly feasible constant-numerator sextics. -/
theorem degree6_constant_upper {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1)
    (hf : ConstantFeasible 6 δ) : δ < Real.sqrt (11/12) := by
  by_contra! hb
  have hsq : Real.sqrt (11/12)^2 = (11/12:ℝ) := Real.sq_sqrt (by norm_num)
  have hu : (11/12:ℝ) ≤ δ^2 := by
    nlinarith only [hsq,mul_nonneg (sub_nonneg.mpr hb)
      (show 0 ≤ δ+Real.sqrt (11/12) by positivity)]
  obtain ⟨x,y,hm,hd,_,hx,hz⟩ := monic_constant_witness hf
  let Z := loop δ x y
  have hmd := loop_monic_degree (δ:=δ) (y:=y) hm (by omega)
  have hZd : Z.natDegree=8 := by dsimp [Z]; simpa [hd] using hmd.2
  have hcoeff := coeff_pos_of_monic_stable hmd.1 hz
  obtain ⟨t,_,ht⟩ := sextic_odd_sign hm hx hd
  let θ := Real.arccos δ
  have hcos : Real.cos θ = δ := Real.cos_arccos (by linarith) hδ'.le
  obtain ⟨hθ,hθ'⟩ := theta_lt_tenth hu hδ hδ'
  have hfpos (j : ℕ) (hj : j ≤ 6) : 0 < weight δ j := by
    rw [← hcos]
    exact weight_first_pos θ hθ hθ' hj
  have hw76 : weight δ 8 < weight δ 7 := by
    rw [← hcos,weight_cos θ (by decide),weight_cos θ (by decide)]
    norm_num
    apply Real.strictAntiOn_cos
    · exact ⟨by positivity,by linarith [Real.pi_pos]⟩
    · exact ⟨by positivity,by linarith [Real.pi_pos]⟩
    · linarith
  have hbala : ∑ j ∈ Finset.range 9, weight δ j*Z.coeff j=0 := by
    have he := loop_rotated_re_zero θ y x
    rw [hcos,rotate_eval_re] at he
    change (∑ k ∈ Finset.range (Z.natDegree+1), Z.coeff k * _) = 0 at he
    rw [hZd] at he
    rw [← he]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← hcos,weight_cos θ (Finset.mem_range.mp hj)]
    ring
  have hs := sum_nonneg_of_pairs (weight δ) (oddWeight δ t) Z.coeff
      (fun j hj => hcoeff j (by change j ≤ Z.natDegree; omega))
      (hfpos 0 (by decide)) hbala ?_ ?_
  · rw [odd_linear δ y x hd t] at ht
    exact ht.not_ge hs
  · intro j hj hj0
    have ha : 6 < j := by
      by_contra! ha
      exact (hfpos j ha).ne' hj0
    exact pure_nonneg hδ hδ' hu (by omega)
  · intro i j hi hj hip hjn
    have hja : 6 < j := by
      by_contra! ha
      exact (hfpos j ha).not_gt hjn
    have hij : i < j := by
      by_contra! hh
      have he : i=j ∨ (i=8 ∧ j=7) := by omega
      rcases he with rfl|⟨rfl,rfl⟩
      · linarith
      · linarith
    exact ray_nonneg hδ hδ' hu (hfpos 6 (by decide)) hip hjn hij (by omega)

private theorem witness_parameter_gt_constant_bound :
    Real.sqrt (11/12) < (96295/100000:ℝ) := by
  have hs : (Real.sqrt (11/12))^2 = (11/12:ℝ) := Real.sq_sqrt (by norm_num)
  by_contra! h
  nlinarith only [hs, mul_nonneg (sub_nonneg.mpr h) (show 0 ≤
    Real.sqrt (11/12)+(96295/100000:ℝ) by positivity)]

/-- An explicit feasible parameter at degree six which no constant numerator can realize. -/
theorem conjecture2_counterexample :
    ∃ δ : ℝ, (96295/100000 : ℝ) < δ ∧ δ < 1 ∧
      (∃ x y : ℝ[X], x.natDegree = 6 ∧ y.natDegree = 6 ∧
        StrictlyStable x ∧ StrictlyStable y ∧
        StrictlyStable ((X^2-C (2*δ)*X+1)*x + (X^2-1)*y)) ∧
      ¬ ConstantFeasible 6 δ := by
  obtain ⟨δ,hd,hd',hw⟩ := degree6_witness
  have hD := witness_parameter_gt_constant_bound
  exact ⟨δ,hd,hd',hw,fun hf => (hD.trans hd).not_gt
    (degree6_constant_upper (by linarith) hd' hf)⟩

/-- A parameter with x ∈ MH⁶ and y ∈ H⁶ that is infeasible with y ∈ H⁰. -/
theorem conjecture2_monic_counterexample :
    ∃ δ : ℝ, (96295/100000 : ℝ) < δ ∧ δ < 1 ∧
      Bistable 6 6 δ ∧ ¬ Bistable 6 0 δ := by
  obtain ⟨δ,hd,hd',⟨x,y,hx,hy,hsx,hsy,hsz⟩,hn⟩ := conjecture2_counterexample
  let c := x.leadingCoeff⁻¹
  have hc : c ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hsx.1)
  have hmx : (x*C c).Monic := by
    unfold Monic
    rw [leadingCoeff_mul,leadingCoeff_C]
    exact mul_inv_cancel₀ (leadingCoeff_ne_zero.mpr hsx.1)
  have hdx : (x*C c).natDegree = 6 := by
    rw [natDegree_mul hsx.1 (C_ne_zero.mpr hc),natDegree_C,add_zero,hx]
  have hdy : (y*C c).natDegree = 6 := by
    rw [natDegree_mul hsy.1 (C_ne_zero.mpr hc),natDegree_C,add_zero,hy]
  refine ⟨δ,hd,hd',⟨x*C c,y*C c,⟨hmx,hdx,stable_mul_C hsx hc⟩,
    ⟨hdy,stable_mul_C hsy hc⟩,?_⟩,fun h => hn (bistable_zero_iff.mp h)⟩
  rw [show plant δ*(x*C c)+(X^2-1)*(y*C c) =
    (plant δ*x+(X^2-1)*y)*C c by ring]
  exact stable_mul_C hsz hc

/-- The review's bound δ_b^n in the counterexample n = 6. -/
noncomputable def δ_b₆ : ℝ := Real.sqrt (11/12)

/-- Conjecture 2 fails with δ_b^6 as an upper bound for H⁰ and y ∈ H⁶ as the witness. -/
theorem conjecture2_upper_bound_counterexample :
    δ_b₆ ∈ upperBounds (bistableParameters 6 0) ∧
      δ_b₆ ∉ upperBounds (bistableParameters 6 6) := by
  constructor
  · rintro δ ⟨hd,hf⟩
    exact (degree6_constant_upper hd (bistable_lt_one hf) (bistable_zero_iff.mp hf)).le
  · intro h
    obtain ⟨δ,hd,_,hB,_⟩ := conjecture2_monic_counterexample
    exact (witness_parameter_gt_constant_bound.trans hd).not_ge
      (h ⟨by linarith,hB⟩)

/-- The threshold gap already holds for numerators of exactly degree six. -/
theorem conjecture2_threshold_gap :
    δₙ_star 6 ≤ δ_b₆ ∧ δ_b₆ < (96295/100000 : ℝ) ∧
      (96295/100000 : ℝ) < sSup (bistableParameters 6 6) := by
  obtain ⟨δ,hδ,_,hB,_⟩ := conjecture2_monic_counterexample
  have hadm : δ ∈ bistableParameters 6 6 := ⟨by linarith,hB⟩
  have hbdd : BddAbove (bistableParameters 6 6) := ⟨1, fun _ h => (bistable_lt_one h.2).le⟩
  refine ⟨?_,witness_parameter_gt_constant_bound,hδ.trans_le (le_csSup hbdd hadm)⟩
  unfold δₙ_star
  by_cases h : (bistableParameters 6 0).Nonempty
  · exact csSup_le h (fun _ hd => conjecture2_upper_bound_counterexample.1 hd)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty, δ_b₆]
    positivity

/-- Negation of the upper-bound transfer stated in Conjecture 2. -/
theorem conjecture2_false :
    ¬ ∀ (n : ℕ) (δ_b : ℝ), 0 < n → δ_b ∈ upperBounds (bistableParameters n 0) →
      ∀ i : ℕ, 1 ≤ i → i ≤ n → δ_b ∈ upperBounds (bistableParameters n i) := by
  intro h
  exact conjecture2_upper_bound_counterexample.2
    (h 6 δ_b₆ (by decide) conjecture2_upper_bound_counterexample.1 6 (by decide) (by decide))

#print axioms degree6_constant_upper
#print axioms conjecture2_monic_counterexample
#print axioms conjecture2_threshold_gap
#print axioms conjecture2_false
#print axioms conjecture2_upper_bound_counterexample
end BelgianChocolate.Conjectures

