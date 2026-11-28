import HurwitzTools

set_option maxHeartbeats 1600000

open Polynomial
open scoped BigOperators
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)

noncomputable def plant (δ : ℝ) : ℝ[X] := X^2 - C (2*δ)*X + 1
noncomputable def loop (δ : ℝ) (x : ℝ[X]) (y : ℝ) : ℝ[X] :=
  plant δ * x + (X^2 - 1) * C y

def ConstantFeasible (n : ℕ) (δ : ℝ) : Prop :=
  ∃ x : ℝ[X], ∃ y : ℝ, x.natDegree = n ∧ y ≠ 0 ∧
    StrictlyStable x ∧ StrictlyStable (loop δ x y)

theorem plant_degree (δ : ℝ) : (plant δ).natDegree = 2 := by
  unfold plant
  compute_degree <;> norm_num

theorem plant_monic (δ : ℝ) : (plant δ).Monic := by
  unfold Monic leadingCoeff
  rw [plant_degree]
  simp [plant, coeff_add, coeff_sub, coeff_X_pow, coeff_one]

theorem loop_monic_degree {δ y : ℝ} {x : ℝ[X]} (hm : x.Monic)
    (hx : 0 < x.natDegree) :
    (loop δ x y).Monic ∧ (loop δ x y).natDegree = x.natDegree + 2 := by
  have hmon := (plant_monic δ).mul hm
  have hdeg : (plant δ * x).natDegree = x.natDegree + 2 := by
    rw [natDegree_mul (plant_monic δ).ne_zero hm.ne_zero, plant_degree, add_comm]
  have hy : ((X^2-1)*C y : ℝ[X]).natDegree ≤ 2 := by compute_degree
  have hlt : ((X^2-1)*C y : ℝ[X]).natDegree < (plant δ*x).natDegree := by omega
  constructor
  · apply hmon.add_of_left
    rw [degree_eq_natDegree hmon.ne_zero]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hlt)
  · unfold loop
    rwa [natDegree_add_eq_left_of_natDegree_lt hlt]

theorem stable_mul_C {x : ℝ[X]} {c : ℝ} (hx : StrictlyStable x) (hc : c ≠ 0) :
    StrictlyStable (x * C c) := by
  rw [strictStable_iff_no_roots] at hx ⊢
  intro s hs
  simpa using mul_ne_zero (hx s hs) (Complex.ofReal_ne_zero.mpr hc)

theorem monic_constant_witness {δ : ℝ} {n : ℕ} (h : ConstantFeasible n δ) :
    ∃ x : ℝ[X], ∃ y : ℝ, x.Monic ∧ x.natDegree = n ∧ y ≠ 0 ∧
      StrictlyStable x ∧ StrictlyStable (loop δ x y) := by
  obtain ⟨x,y,hd,hy,hx,hz⟩ := h
  have hl : x.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hx.1
  let c := x.leadingCoeff⁻¹
  have hc : c ≠ 0 := inv_ne_zero hl
  refine ⟨x*C c, y*c, ?_, ?_, mul_ne_zero hy hc, stable_mul_C hx hc, ?_⟩
  · unfold Polynomial.Monic
    rw [leadingCoeff_mul, leadingCoeff_C]
    exact mul_inv_cancel₀ hl
  · rw [natDegree_mul hx.1 (C_ne_zero.mpr hc), natDegree_C, add_zero, hd]
  · convert stable_mul_C hz hc using 1
    unfold loop
    rw [map_mul]
    ring

noncomputable def phase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

@[simp] theorem phase_re (θ : ℝ) : (phase θ).re = Real.cos θ := by
  simp [phase, Complex.exp_re, Complex.mul_re, Complex.mul_im]

@[simp] theorem phase_im (θ : ℝ) : (phase θ).im = Real.sin θ := by
  simp [phase, Complex.exp_im, Complex.mul_re, Complex.mul_im]

theorem phase_add (a b : ℝ) : phase (a+b) = phase a * phase b := by
  unfold phase
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_pow (a : ℝ) (k : ℕ) : (phase a)^k = phase ((k : ℝ)*a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, phase_add]

theorem phase_pair (θ : ℝ) : phase θ * phase (-θ) = 1 := by
  rw [← phase_add, add_neg_cancel, phase_zero]

theorem phase_sum (θ : ℝ) :
    phase θ + phase (-θ) = ((2*Real.cos θ : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, phase_re, Real.cos_neg, Complex.ofReal_re]; ring
  · simp only [Complex.add_im, phase_im, Real.sin_neg, Complex.ofReal_im, add_neg_cancel]

theorem plant_phase (θ : ℝ) : aeval (phase θ) (plant (Real.cos θ)) = 0 := by
  simp only [plant, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one]
  rw [← map_mul (algebraMap ℝ ℂ)]
  change (phase θ)^2 - ((2*Real.cos θ : ℝ) : ℂ)*phase θ + 1 = 0
  rw [← phase_sum]
  linear_combination -(phase_pair θ)

theorem loop_rotated_re_zero (θ y : ℝ) (x : ℝ[X]) :
    (phase (-θ) * aeval (phase θ) (loop (Real.cos θ) x y)).re = 0 := by
  simp only [loop, map_add, map_mul, plant_phase, zero_mul, zero_add, map_sub,
    map_pow, aeval_X, map_one, aeval_C]
  change (phase (-θ) * (((phase θ)^2-1) * (y:ℂ))).re = 0
  have hp : phase (-θ) * phase θ = 1 := by rw [mul_comm]; exact phase_pair θ
  have hh : phase (-θ) * ((phase θ)^2-1) * (y:ℂ) =
      (phase θ - phase (-θ)) * (y:ℂ) := by
    linear_combination (phase θ)*(y:ℂ)*hp
  rw [← mul_assoc, hh]
  simp [Complex.mul_re, Real.cos_neg]

theorem rotate_eval_re (θ : ℝ) (p : ℝ[X]) :
    (phase (-θ) * aeval (phase θ) p).re =
      ∑ k ∈ Finset.range (p.natDegree+1), p.coeff k * Real.cos (((k:ℝ)-1)*θ) := by
  rw [aeval_def, eval₂_eq_sum_range, Finset.mul_sum]
  change Complex.reAddGroupHom _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (phase (-θ) * ((p.coeff k : ℂ) * (phase θ)^k)).re = _
  rw [phase_pow]
  rw [show phase (-θ) * ((p.coeff k : ℂ) * phase ((k : ℝ)*θ)) =
    (p.coeff k : ℂ) * phase (((k:ℝ)-1)*θ) by
      rw [show phase (-θ) * ((p.coeff k : ℂ) * phase ((k : ℝ)*θ)) =
        (p.coeff k : ℂ) * (phase (-θ) * phase ((k:ℝ)*θ)) by ring, ← phase_add]
      rw [show -θ + (k:ℝ)*θ = ((k:ℝ)-1)*θ by ring]]
  simp [Complex.mul_re]

private theorem eval_one_pos {p : ℝ[X]} (hm : p.Monic) (hs : StrictlyStable p) :
    0 < p.eval 1 := by
  have hc := coeff_pos_of_monic_stable hm hs
  rw [eval_eq_sum_range]
  simp only [one_pow,mul_one]
  exact Finset.sum_pos' (fun i hi => (hc i (by simpa using hi)).le)
    ⟨0, Finset.mem_range.mpr (by omega),hc 0 (Nat.zero_le _)⟩

/-- For a positive denominator degree, feasibility itself forces the parameter below one. -/
theorem constant_feasible_lt_one {n : ℕ} {δ : ℝ} (hn : 0 < n)
    (h : ConstantFeasible n δ) : δ < 1 := by
  obtain ⟨x,y,hm,hd,_,hx,hz⟩ := monic_constant_witness h
  have hx' := eval_one_pos hm hx
  have hz' := eval_one_pos (loop_monic_degree hm (by omega)).1 hz
  have hEq : (loop δ x y).eval 1 = (2-2*δ)*x.eval 1 := by
    simp only [loop,plant,eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_one]
    ring
  rw [hEq] at hz'
  have hp := pos_of_mul_pos_left hz' hx'.le
  linarith

/-- The review's Hⁱ, the real strictly Hurwitz polynomials of degree i. -/
def H (i : ℕ) : Set ℝ[X] := {p | p.natDegree = i ∧ StrictlyStable p}

/-- The review's MHⁿ, the monic members of Hⁿ. -/
def MH (n : ℕ) : Set ℝ[X] := {p | p.Monic ∧ p ∈ H n}

/-- Bistability with x ∈ MHⁿ and y ∈ Hⁱ at parameter δ. -/
def Bistable (n i : ℕ) (δ : ℝ) : Prop :=
  ∃ x y : ℝ[X], x ∈ MH n ∧ y ∈ H i ∧
    StrictlyStable (plant δ * x + (X^2 - 1) * y)

theorem bistable_zero_iff {n : ℕ} {δ : ℝ} :
    Bistable n 0 δ ↔ ConstantFeasible n δ := by
  constructor
  · rintro ⟨x,y,⟨_,hx,hxs⟩,⟨hy,hys⟩,hz⟩
    have he := eq_C_of_natDegree_eq_zero hy
    have h0 : y.coeff 0 ≠ 0 := by
      intro h
      exact hys.1 (by rw [he,h,map_zero])
    refine ⟨x,y.coeff 0,hx,h0,hxs,?_⟩
    change StrictlyStable (plant δ*x + (X^2-1)*C (y.coeff 0))
    rwa [← he]
  · intro h
    obtain ⟨x,y,hm,hx,hy,hxs,hz⟩ := monic_constant_witness h
    refine ⟨x,C y,⟨hm,hx,hxs⟩,⟨natDegree_C y,?_⟩,hz⟩
    apply (strictStable_iff_no_roots (C y)).mpr
    intro s _
    simpa using Complex.ofReal_ne_zero.mpr hy

private theorem stable_eval_ne_zero {p : ℝ[X]} (hp : StrictlyStable p)
    {s : ℝ} (hs : 0 ≤ s) : p.eval s ≠ 0 := by
  intro h
  have hroot : aeval (algebraMap ℝ ℂ s) p = 0 := by
    rw [aeval_algebraMap_apply_eq_algebraMap_eval,h,map_zero]
  have hh := hp.2 _ hroot
  exact (not_lt_of_ge hs) (by simpa using hh)

/-- Bistability at a real parameter forces δ < 1. -/
theorem bistable_lt_one {n i : ℕ} {δ : ℝ} (h : Bistable n i δ) : δ < 1 := by
  obtain ⟨x,y,_,⟨_,hy⟩,hz⟩ := h
  let Z := plant δ*x + (X^2-1)*y
  let a := fun s : ℝ => s^2-2*δ*s+1
  let g := fun s : ℝ => Z.eval s * y.eval s
  have ha (s : ℝ) : (plant δ).eval s = a s := by simp [plant,a]
  have hZ (s : ℝ) : Z.eval s = a s * x.eval s + (s^2-1)*y.eval s := by
    simp only [Z,eval_add,eval_mul,ha,eval_sub,eval_pow,eval_X,eval_one]
  have hg (s : ℝ) (hs : 0 ≤ s) : g s ≠ 0 :=
    mul_ne_zero (stable_eval_ne_zero hz hs) (stable_eval_ne_zero hy hs)
  by_contra! hδ
  have hδ' : 1 < δ := by
    refine lt_of_le_of_ne hδ (fun he => ?_)
    apply stable_eval_ne_zero hz (show (0:ℝ) ≤ 1 by norm_num)
    rw [hZ]
    dsimp only [a]
    rw [← he]
    norm_num [a]
  have ha0 : 0 < a 0 := by norm_num [a]
  have ha1 : a 1 < 0 := by dsimp [a]; nlinarith
  have ha2 : 0 < a (2*δ) := by dsimp [a]; nlinarith
  have hac : Continuous a := by dsimp [a]; fun_prop
  obtain ⟨r,hr,hr0⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num)
    hac.continuousOn (show 0 ∈ Set.Icc (a 1) (a 0) from ⟨ha1.le,ha0.le⟩)
  obtain ⟨s,hs,hs0⟩ := intermediate_value_Icc (show (1:ℝ) ≤ 2*δ by linarith)
    hac.continuousOn (show 0 ∈ Set.Icc (a 1) (a (2*δ)) from ⟨ha1.le,ha2.le⟩)
  have hr1 : r < 1 := lt_of_le_of_ne hr.2 (fun he => ha1.ne (he ▸ hr0))
  have hs1 : 1 < s := lt_of_le_of_ne hs.1 (fun he => ha1.ne (he.symm ▸ hs0))
  have hsg : g s ≥ 0 := by
    dsimp [g]
    rw [hZ,hs0,zero_mul,zero_add,mul_assoc]
    exact mul_nonneg (by nlinarith [mul_nonneg (sub_nonneg.mpr hs1.le) (show 0 ≤ s+1 by linarith)])
      (mul_self_nonneg _)
  have hrg : g r ≤ 0 := by
    dsimp [g]
    rw [hZ,hr0,zero_mul,zero_add,mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (show 0 ≤ 1+r by linarith [hr.1])])
      (mul_self_nonneg _)
  have hgc : Continuous g := Z.continuous.mul y.continuous
  obtain ⟨t,ht,ht0⟩ := intermediate_value_Icc (hr1.le.trans hs1.le) hgc.continuousOn
    (show 0 ∈ Set.Icc (g r) (g s) from ⟨hrg,hsg⟩)
  exact hg t (hr.1.trans ht.1) ht0

/-- Sₙ,ᵢ, the positive parameters with x ∈ MHⁿ and y ∈ Hⁱ. -/
def bistableParameters (n i : ℕ) : Set ℝ := {δ | 0 < δ ∧ Bistable n i δ}

/-- The least upper bound δₙ* for y ∈ H⁰. -/
noncomputable def δₙ_star (n : ℕ) : ℝ := sSup (bistableParameters n 0)

/-- The continued-fraction bound δₙ, in cosine form. -/
noncomputable def δₙ (n : ℕ) : ℝ :=
  Real.cos (Real.pi/(2*((n:ℝ)+1)))

theorem δₙ_eq_sin (n : ℕ) : δₙ n = Real.sin (((n:ℝ)+2)*Real.pi/(2*((n:ℝ)+1))) := by
  have h : ((n:ℝ)+2)*Real.pi/(2*((n:ℝ)+1)) =
      Real.pi/2+Real.pi/(2*((n:ℝ)+1)) := by
    field_simp
    ring
  rw [δₙ,h,Real.sin_add,Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul,zero_mul,add_zero]

/-- Every strictly feasible constant-numerator controller is strictly below the
continued-fraction bound in Conjecture 3. -/
theorem conjecture3 {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (hδ₀ : 0 < δ) (h : ConstantFeasible n δ) :
    δ < δₙ n := by
  unfold δₙ
  have hδ₁ := constant_feasible_lt_one hn h
  obtain ⟨x,y,hm,hd,_,_,hz⟩ := monic_constant_witness h
  let θ := Real.arccos δ
  have hcos : Real.cos θ = δ := Real.cos_arccos (by linarith) hδ₁.le
  have hθ₀ : 0 ≤ θ := Real.arccos_nonneg _
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi _
  by_contra! hbad
  let a := Real.pi/(2*((n:ℝ)+1))
  have hna : (1:ℝ) ≤ n := by exact_mod_cast hn
  have ha : a ∈ Set.Icc 0 Real.pi := by
    constructor
    · dsimp [a]; positivity
    · dsimp [a]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
  have hθ : θ ≤ a := by
    by_contra! hgt
    have hb : Real.cos a ≤ Real.cos θ := by rw [hcos]; exact hbad
    exact (not_lt_of_ge hb) (Real.strictAntiOn_cos ha ⟨hθ₀,hθπ⟩ hgt)
  have hhalf : a ≤ Real.pi/2 := by
    dsimp [a]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hstrict : θ < Real.pi/2 := by
    apply lt_of_le_of_ne (hθ.trans hhalf)
    intro he
    rw [he, Real.cos_pi_div_two] at hcos
    linarith
  have hprod : ((n:ℝ)+1)*θ ≤ Real.pi/2 := by
    have hmul := mul_le_mul_of_nonneg_left hθ (by positivity : 0 ≤ (n:ℝ)+1)
    dsimp [a] at hmul
    rwa [show ((n:ℝ)+1)*(Real.pi/(2*((n:ℝ)+1))) = Real.pi/2 by field_simp] at hmul
  have hmd := loop_monic_degree (δ:=δ) (y:=y) hm (by omega)
  have hc := coeff_pos_of_monic_stable hmd.1 hz
  have hzero := loop_rotated_re_zero θ y x
  rw [hcos, rotate_eval_re] at hzero
  have hsum :
      0 < ∑ k ∈ Finset.range ((loop δ x y).natDegree+1),
          (loop δ x y).coeff k * Real.cos (((k:ℝ)-1)*θ) := by
    refine Finset.sum_pos' ?_ ?_
    · intro k hk
      have hkle : k ≤ n+2 := by rw [Finset.mem_range, hmd.2, hd] at hk; omega
      have hkl : (k:ℝ) ≤ (n:ℝ)+2 := by exact_mod_cast hkle
      have hk0 : 0 ≤ (k:ℝ) := by positivity
      apply mul_nonneg (hc k (by rw [hmd.2,hd]; exact hkle)).le
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · nlinarith [mul_nonneg hk0 hθ₀]
      · nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)+2-k by linarith) hθ₀]
    · refine ⟨0, Finset.mem_range.mpr (by omega), mul_pos (hc 0 (Nat.zero_le _)) ?_⟩
      simp only [Nat.cast_zero, zero_sub, neg_one_mul, Real.cos_neg]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hstrict⟩
  linarith

/-- Pointwise strict inequality in the review's MHⁿ and H⁰ notation. -/
theorem conjecture3_bistable {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (hδ : δ ∈ bistableParameters n 0) : δ < δₙ n :=
  conjecture3 hn hδ.1 (bistable_zero_iff.mp hδ.2)

/-- Conjecture 3, with δₙ* interpreted as the least upper bound. -/
theorem conjecture3_sup {n : ℕ} (hn : 0 < n) : δₙ_star n ≤ δₙ n := by
  unfold δₙ_star
  by_cases h : (bistableParameters n 0).Nonempty
  · exact csSup_le h (fun _ hδ => (conjecture3_bistable hn hδ).le)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty, δₙ]
    apply Real.cos_nonneg_of_mem_Icc
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    constructor
    · have ha : 0 ≤ Real.pi/(2*((n:ℝ)+1)) := by positivity
      linarith [Real.pi_pos]
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]

#print axioms conjecture3
#print axioms conjecture3_sup
end BelgianChocolate.Conjectures

