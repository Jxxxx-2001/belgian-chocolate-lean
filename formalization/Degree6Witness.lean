import HurwitzTools

open Polynomial
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)

theorem stable_mul {p q : ℝ[X]} (hp : StrictlyStable p) (hq : StrictlyStable q) :
    StrictlyStable (p*q) := by
  rw [strictStable_iff_no_roots] at hp hq ⊢
  intro s hs
  simpa using mul_ne_zero (hp s hs) (hq s hs)

theorem stable_pow {p : ℝ[X]} (hp : StrictlyStable p) (n : ℕ) : StrictlyStable (p^n) := by
  rw [strictStable_iff_no_roots] at hp ⊢
  intro s hs
  simpa using pow_ne_zero n (hp s hs)

theorem stable_C {c : ℝ} (hc : c ≠ 0) : StrictlyStable (C c) := by
  rw [strictStable_iff_no_roots]
  intro s _
  simpa using Complex.ofReal_ne_zero.mpr hc

theorem stable_positive_quadratic (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    StrictlyStable (C a * X^2 + C b * X + C c) := by
  rw [strictStable_iff_no_roots]
  intro s hs hz
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C] at hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
  have hi0 : s.im = 0 := by
    have hh : s.im * (2*a*s.re+b) = 0 := by nlinarith only [hi]
    exact (mul_eq_zero.mp hh).resolve_right
      (ne_of_gt (by nlinarith [mul_nonneg ha.le hs]))
  rw [hi0] at hr
  nlinarith only [hr, hc, mul_nonneg ha.le (sq_nonneg s.re), mul_nonneg hb.le hs]

noncomputable def num (h : ℝ) : ℝ[X] := X + C h
noncomputable def den (h : ℝ) : ℝ[X] := 1 + C h * X
noncomputable def homog (h a b : ℝ) : ℝ[X] :=
  num h ^ 2 + C a * num h * den h + C b * den h ^ 2

theorem den_stable {h : ℝ} (hh : 0 < h) : StrictlyStable (den h) := by
  rw [strictStable_iff_no_roots]
  intro s hs hz
  have hr := congrArg Complex.re hz
  simp [den, Complex.mul_re] at hr
  nlinarith [mul_nonneg hh.le hs]

theorem den_degree {h : ℝ} (hh : 0 < h) : (den h).natDegree = 1 := by
  unfold den
  compute_degree; norm_num [ne_of_gt hh]

theorem homog_expand (h a b : ℝ) :
    homog h a b = C (1+a*h+b*h^2)*X^2 + C (2*h+a*(1+h^2)+2*b*h)*X +
      C (h^2+a*h+b) := by
  simp only [homog, num, den, map_add, map_mul, map_pow, map_one, map_ofNat]
  ring

theorem homog_stable_degree {h a b : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hb : 0 < b) :
    StrictlyStable (homog h a b) ∧ (homog h a b).natDegree = 2 := by
  rw [homog_expand]
  have h₁ : 0 < 1+a*h+b*h^2 := by positivity
  have h₂ : 0 < 2*h+a*(1+h^2)+2*b*h := by positivity
  have h₃ : 0 < h^2+a*h+b := by positivity
  refine ⟨stable_positive_quadratic _ _ _ h₁ h₂ h₃, ?_⟩
  compute_degree <;> norm_num [ne_of_gt h₁]

noncomputable def witnessCubic (a : ℝ) : ℝ := 1+2*a-2*a^2-2*a^3

theorem exists_witness_cubic :
    ∃ a : ℝ, 854637/1000000 ≤ a ∧ a ≤ 854638/1000000 ∧ witnessCubic a = 0 := by
  have hcont : Continuous witnessCubic := by unfold witnessCubic; fun_prop
  have hmem : (0:ℝ) ∈ Set.Icc (witnessCubic (854638/1000000))
      (witnessCubic (854637/1000000)) := by norm_num [witnessCubic]
  have himg := intermediate_value_Icc' (f:=witnessCubic)
    (show (854637/1000000:ℝ) ≤ 854638/1000000 by norm_num) hcont.continuousOn hmem
  obtain ⟨a, ha, he⟩ := himg
  exact ⟨a,ha.1,ha.2,he⟩

theorem transformed_identities (h d δ K : ℝ) (hK : K=1+h^2-2*d*h)
    (hd : δ*K=d*(1+h^2)-2*h) :
    C K * (X^2-C (2*δ)*X+1) =
      num h^2 - C (2*d)*num h*den h + den h^2 ∧
    C (1-h^2)*(X^2-1) = num h^2-den h^2 := by
  have hk : C K = (1:ℝ[X])+(C h)^2-2*C d*C h := by
    simp only [hK, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  have hc : C δ * C K = C d*(1+(C h)^2)-2*C h := by
    simpa only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat] using congrArg C hd
  constructor
  · simp only [num,den,map_mul,map_ofNat]
    linear_combination (X^2+1)*hk - 2*X*hc
  · simp only [num,den,map_sub,map_one,map_pow]
    ring

theorem algebraic_witness_identity (p q : ℝ[X]) (d a k b : ℝ)
    (hd : 2*d^2=1+a) (hk : k=3*a^2-1) (hb : k*b=a^2) (ha : witnessCubic a = 0) :
    (p^2-C (2*d)*p*q+q^2)*(p^2+C (2*d)*p*q+q^2)*(p^2+C a*q^2)^2 +
      (p^2-q^2)*C k*q^4*(p^2+C b*q^2) = p^8 := by
  have hd' : 2*(C d)^2=1+C a := by
    simpa only [map_add,map_mul,map_pow,map_one,map_ofNat] using congrArg C hd
  have hk' : C k=3*(C a)^2-1 := by
    simpa only [map_sub,map_mul,map_pow,map_one,map_ofNat] using congrArg C hk
  have hb' : C k*C b=(C a)^2 := by
    simpa only [map_mul,map_pow] using congrArg C hb
  have ha' : (1:ℝ[X])+2*C a-2*(C a)^2-2*(C a)^3=0 := by
    simpa only [witnessCubic,map_sub,map_add,map_mul,map_pow,map_one,map_ofNat,map_zero]
      using congrArg C ha
  simp only [map_mul,map_ofNat]
  linear_combination
    -2*p^2*q^2*(p^2+C a*q^2)^2*hd' + p^2*q^4*(p^2-q^2)*hk' +
    q^6*(p^2-q^2)*hb' + p^2*q^6*ha'

/-- A strictly stable degree-six controller above the stated rational threshold. -/
theorem degree6_witness :
    ∃ δ : ℝ, (96295/100000 : ℝ) < δ ∧ δ < 1 ∧
      ∃ x y : ℝ[X], x.natDegree = 6 ∧ y.natDegree = 6 ∧
        StrictlyStable x ∧ StrictlyStable y ∧
        StrictlyStable ((X^2-C (2*δ)*X+1)*x + (X^2-1)*y) := by
  obtain ⟨a, ha₁, ha₂, ha⟩ := exists_witness_cubic
  let d := Real.sqrt ((1+a)/2)
  let k := 3*a^2-1
  let b := a^2/k
  let h : ℝ := 1/10000
  let K := 1+h^2-2*d*h
  let δ := (d*(1+h^2)-2*h)/K
  have ha₀ : 0 < a := by linarith
  have hd2 : d^2 = (1+a)/2 := Real.sq_sqrt (by positivity)
  have hd₀ : 0 ≤ d := Real.sqrt_nonneg _
  have hd_low : (962973/1000000:ℝ) < d := by
    by_contra! hs
    have hsq := mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ (962973/1000000:ℝ)+d by positivity)
    nlinarith only [hd2, ha₁, hsq]
  have hd_high : d < 1 := by
    by_contra! hs
    nlinarith only [hd2,ha₂,mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ d+1 by positivity)]
  have hh : 0 < h := by norm_num [h]
  have hk : 0 < k := by
    dsimp [k]
    nlinarith only [ha₁, mul_nonneg (sub_nonneg.mpr ha₁) (show 0 ≤ a+854637/1000000 by positivity)]
  have hb : 0 < b := by dsimp [b]; positivity
  have hK : 0 < K := by
    dsimp [K,h]
    linarith
  have hδK : δ*K = d*(1+h^2)-2*h := div_mul_cancel₀ _ (ne_of_gt hK)
  have hδ_low : (96295/100000:ℝ)<δ := by
    dsimp [δ]
    rw [lt_div_iff₀ hK]
    dsimp [K,h]
    linarith
  have hδ_high : δ < 1 := by
    dsimp [δ]
    rw [div_lt_iff₀ hK]
    dsimp [K,h]
    linarith
  let x := C K * homog h (2*d) 1 * (homog h 0 a)^2
  let y := C ((1-h^2)*k) * (den h)^4 * homog h 0 b
  have hsX := homog_stable_degree hh (show 0 ≤ 2*d by positivity) (show (0:ℝ)<1 by norm_num)
  have hsA := homog_stable_degree hh (le_refl (0:ℝ)) ha₀
  have hsB := homog_stable_degree hh (le_refl (0:ℝ)) hb
  have hyc : (1-h^2)*k ≠ 0 := mul_ne_zero (by norm_num [h]) (ne_of_gt hk)
  refine ⟨δ,hδ_low,hδ_high,x,y,?_,?_,?_,?_,?_⟩
  · dsimp [x]
    rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr (ne_of_gt hK)) hsX.1.1)
      (pow_ne_zero _ hsA.1.1), natDegree_mul (C_ne_zero.mpr (ne_of_gt hK)) hsX.1.1,
      natDegree_C,hsX.2,natDegree_pow,hsA.2]
  · dsimp [y]
    rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr hyc) (pow_ne_zero _ (den_stable hh).1))
      hsB.1.1, natDegree_mul (C_ne_zero.mpr hyc) (pow_ne_zero _ (den_stable hh).1),
      natDegree_C,natDegree_pow,den_degree hh,hsB.2]
  · exact stable_mul (stable_mul (stable_C hK.ne') hsX.1) (stable_pow hsA.1 2)
  · exact stable_mul (stable_mul (stable_C hyc) (stable_pow (den_stable hh) 4)) hsB.1
  · have ht := transformed_identities h d δ K rfl hδK
    have hm := algebraic_witness_identity (num h) (den h) d a k b
      (by linarith only [hd2]) rfl (by dsimp [b]; field_simp [hk.ne']) ha
    have he : (X^2-C (2*δ)*X+1)*x+(X^2-1)*y = num h ^ 8 := by
      dsimp only [x,y]
      rw [show (X^2-C (2*δ)*X+1)*(C K*homog h (2*d) 1*(homog h 0 a)^2) =
        (C K*(X^2-C (2*δ)*X+1))*homog h (2*d) 1*(homog h 0 a)^2 by ring]
      rw [show (X^2-1)*(C ((1-h^2)*k)*(den h)^4*homog h 0 b) =
        (C (1-h^2)*(X^2-1))*C k*(den h)^4*homog h 0 b by rw [map_mul]; ring]
      rw [ht.1,ht.2]
      simpa [homog] using hm
    rw [he]
    exact stable_pow (stable_linear h hh) 8

#print axioms degree6_witness
end BelgianChocolate.Conjectures

