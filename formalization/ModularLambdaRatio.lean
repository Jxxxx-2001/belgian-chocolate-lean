module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Asymptotics
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Transform
import TauCeti.NumberTheory.ModularForms.SiegelFunction.GammaTwo
import TauCeti.LinearAlgebra.Matrix.RationalVector
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The level-two Siegel ratio and its local analytic behavior at the cusp at infinity. -/

public section

open Complex Filter TauCeti.ModularForm
open UpperHalfPlane hiding I
open scoped Topology Manifold MatrixGroups

namespace BelgianChocolate.ModularLambdaRatio

/-- The level-two ratio of Siegel functions on the upper half-plane. -/
noncomputable def lambdaRatio (τ : ℍ) : ℂ :=
  -(siegelFunction ![0, (1 / 2 : ℝ)] τ ^ 4) /
    siegelFunction ![(1 / 2 : ℝ), 1 / 2] τ ^ 4

private theorem half_ne_intCast (k : ℤ) : (1 / 2 : ℝ) ≠ k := by
  intro h
  have heq : ((2 * k : ℤ) : ℝ) = 1 := by push_cast; linarith
  have : 2 * k = (1 : ℤ) := by exact_mod_cast heq
  omega

private theorem denominator_ne_zero (τ : ℍ) :
    siegelFunction ![(1 / 2 : ℝ), 1 / 2] τ ≠ 0 := by
  apply siegelFunction_ne_zero _ τ.im_pos
  intro k hk
  exact half_ne_intCast (k 0) (by simpa using congrFun hk 0)

private theorem numerator_ne_zero (τ : ℍ) :
    siegelFunction ![0, (1 / 2 : ℝ)] τ ≠ 0 := by
  apply siegelFunction_ne_zero _ τ.im_pos
  intro k hk
  exact half_ne_intCast (k 1) (by simpa using congrFun hk 1)

theorem lambdaRatio_ne_zero (τ : ℍ) : lambdaRatio τ ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (numerator_ne_zero τ)))
    (pow_ne_zero _ (denominator_ne_zero τ))

theorem lambdaRatio_mdifferentiable : MDiff lambdaRatio :=
  (((mdifferentiable_siegelFunction _).pow 4).neg.div
    ((mdifferentiable_siegelFunction _).pow 4) fun τ => pow_ne_zero _ (denominator_ne_zero τ))

/-- Leading term of the numerator after removing its exponential. -/
private theorem numerator_limit :
    Tendsto (fun τ : ℍ => siegelFunction ![0, (1 / 2 : ℝ)] τ *
      Complex.exp (-(Real.pi * I * (τ : ℂ) / 6))) atImInfty (𝓝 (2 * I)) := by
  have h := tendsto_siegelFunction_mul_exp_neg (r := ![0, (1 / 2 : ℝ)]) (by norm_num) (by norm_num)
  have h₀ : bernoulliFun 2 (0 : ℝ) = 1 / 6 := by norm_num [bernoulliFun_two]
  have hπ : (Real.pi : ℂ) * I * (↑(1/2 : ℝ) : ℂ) * (↑(0 : ℝ) - 1) = -(Real.pi : ℂ) / 2 * I := by
    push_cast; ring
  have h₂π : (2 : ℂ) * Real.pi * I * (↑(1/2 : ℝ) : ℂ) = Real.pi * I := by
    push_cast; ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, h₀, ite_true, hπ,
    h₂π, Complex.exp_neg_pi_div_two_mul_I, Complex.exp_pi_mul_I, neg_neg] at h
  convert h using 1
  · ext τ; congr 2; push_cast; ring_nf
  · ring_nf

/-- Leading term of the denominator after removing its exponential. -/
private theorem denominator_limit :
    Tendsto (fun τ : ℍ => siegelFunction ![(1 / 2 : ℝ), 1 / 2] τ *
      Complex.exp (Real.pi * I * (τ : ℂ) / 12)) atImInfty
        (𝓝 (-Complex.exp (-(Real.pi * I / 4)))) := by
  have h := tendsto_siegelFunction_mul_exp_neg (r := ![(1 / 2 : ℝ), 1 / 2]) (by norm_num) (by norm_num)
  have h₁ : bernoulliFun 2 (1 / 2 : ℝ) = -(1 / 12) := by norm_num [bernoulliFun_two]
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, h₁, div_ne_zero,
    one_ne_zero, OfNat.ofNat_ne_zero, ite_false, mul_one] at h
  convert h using 1
  · ext τ; congr 2; push_cast; ring_nf
  · congr 2; push_cast; ring_nf

/-- The normalized ratio has first coefficient 16 at the level-two cusp. -/
theorem lambdaRatio_div_q_tendsto :
    Tendsto (fun τ : ℍ => lambdaRatio τ / Complex.exp (Real.pi * I * (τ : ℂ)))
      atImInfty (𝓝 (16 : ℂ)) := by
  have hd : (-Complex.exp (-(Real.pi * I / 4))) ^ 4 = (-1 : ℂ) := by
    rw [neg_pow, show (-1 : ℂ) ^ 4 = 1 by norm_num, one_mul, ← Complex.exp_nat_mul]
    rw [show (↑(4 : ℕ) : ℂ) * -(Real.pi * I / 4) = -(Real.pi * I) by push_cast; ring,
      Complex.exp_neg_pi_mul_I]
  have hn : -((2 * I) ^ 4) = (-16 : ℂ) := by rw [mul_pow, Complex.I_pow_four]; norm_num
  have hp := (denominator_limit.pow 4)
  rw [hd] at hp
  have hm := (numerator_limit.pow 4).neg
  rw [hn] at hm
  have h := hm.div hp (by norm_num)
  norm_num at h
  refine h.congr fun τ => ?_
  let a := Real.pi * I * (τ : ℂ)
  change -((siegelFunction ![0, (1 / 2 : ℝ)] τ * Complex.exp (-(a / 6))) ^ 4) /
    (siegelFunction ![(1 / 2 : ℝ), 1 / 2] τ * Complex.exp (a / 12)) ^ 4 =
      lambdaRatio τ / Complex.exp a
  rw [lambdaRatio, div_div, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  rw [show Complex.exp ((↑(4 : ℕ) : ℂ) * (a / 12)) =
    Complex.exp ((↑(4 : ℕ) : ℂ) * -(a / 6)) * Complex.exp a by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
  field_simp [Complex.exp_ne_zero, denominator_ne_zero]

private theorem qParam_eq_exp (τ : ℍ) :
    Function.Periodic.qParam 2 (τ : ℂ) = Complex.exp (Real.pi * I * (τ : ℂ)) := by
  unfold Function.Periodic.qParam
  congr 1
  push_cast
  ring

theorem lambdaRatio_tendsto_zero : Tendsto lambdaRatio atImInfty (𝓝 0) := by
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty (h := 2) (by norm_num)
  have hr := lambdaRatio_div_q_tendsto
  simp only [← qParam_eq_exp] at hr
  simpa using (hr.mul hq).congr fun τ =>
    div_mul_cancel₀ _ (by rw [qParam_eq_exp]; exact Complex.exp_ne_zero _)

/-- Periodicity lets the cusp function inherit the simple zero and derivative 16. -/
theorem lambdaCusp_simple_zero
    (hper : Function.Periodic (lambdaRatio ∘ UpperHalfPlane.ofComplex) (2 : ℝ)) :
    UpperHalfPlane.cuspFunction 2 lambdaRatio 0 = 0 ∧
      HasDerivAt (UpperHalfPlane.cuspFunction 2 lambdaRatio) (16 : ℂ) 0 := by
  let Λ := UpperHalfPlane.cuspFunction 2 lambdaRatio
  have hpos : (0 : ℝ) < 2 := by norm_num
  have han : AnalyticAt ℂ Λ 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero hpos hper lambdaRatio_mdifferentiable
      (lambdaRatio_tendsto_zero.isBigO_one ℝ)
  have hz : Λ 0 = 0 := by
    dsimp only [Λ]
    rw [UpperHalfPlane.cuspFunction_apply_zero hpos han hper]
    exact lambdaRatio_tendsto_zero.limUnder_eq
  have hd := han.differentiableAt.hasDerivAt
  have hq := (Function.Periodic.qParam_tendsto (h := 2) hpos).comp
    UpperHalfPlane.tendsto_coe_atImInfty
  have hs := hd.tendsto_slope.comp hq
  have hr : Tendsto (fun τ : ℍ => slope Λ 0 (Function.Periodic.qParam 2 (τ : ℂ)))
      atImInfty (𝓝 (16 : ℂ)) := by
    refine lambdaRatio_div_q_tendsto.congr fun τ => ?_
    rw [slope_def_field, hz, sub_zero, sub_zero]
    dsimp only [Λ]
    rw [UpperHalfPlane.eq_cuspFunction τ (ne_of_gt hpos) hper, qParam_eq_exp]
  exact ⟨hz, (tendsto_nhds_unique hs hr) ▸ hd⟩

/-- The fourth powers of the two shift multipliers agree, yielding period two for the ratio. -/
theorem lambdaRatio_periodic :
    Function.Periodic (lambdaRatio ∘ UpperHalfPlane.ofComplex) (2 : ℝ) := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro τ
  let z := (τ : ℂ)
  let a := (Real.pi : ℂ) * I
  have hphase : (Complex.exp (a / 3)) ^ 4 = (Complex.exp (-(a / 6))) ^ 4 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    rw [show (↑(4 : ℕ) : ℂ) * (a / 3) = (↑(4 : ℕ) : ℂ) * -(a / 6) + 2 * a by push_cast; ring,
      Complex.exp_add]
    change _ * Complex.exp (2 * ((Real.pi : ℂ) * I)) = _
    rw [← mul_assoc, Complex.exp_two_pi_mul_I, mul_one]
  have htranslate : z + (↑(2 : ℝ) : ℂ) = z + 1 + 1 := by push_cast; ring
  have hnum : siegelFunction ![0, (1 / 2 : ℝ)] (z + (↑(2 : ℝ) : ℂ)) ^ 4 =
      (Complex.exp (a / 3)) ^ 4 * siegelFunction ![0, (1 / 2 : ℝ)] z ^ 4 := by
    rw [htranslate, siegelFunction_zero_half_apply_add_one, siegelFunction_zero_half_apply_add_one,
      ← mul_assoc, ← Complex.exp_add, mul_pow]
    congr 2
    dsimp only [a]
    ring_nf
  have hden : siegelFunction ![(1 / 2 : ℝ), 1 / 2] (z + (↑(2 : ℝ) : ℂ)) ^ 4 =
      (Complex.exp (a / 3)) ^ 4 * siegelFunction ![(1 / 2 : ℝ), 1 / 2] z ^ 4 := by
    rw [htranslate, siegelFunction_half_half_apply_add_one, siegelFunction_half_zero_apply_add_one,
      ← mul_assoc, ← Complex.exp_add, mul_pow, hphase]
    congr 2
    dsimp only [a]
    ring_nf
  rw [lambdaRatio, UpperHalfPlane.coe_vadd, add_comm _ (τ : ℂ)]
  change -(siegelFunction ![0, (1 / 2 : ℝ)] (z + (↑(2 : ℝ) : ℂ)) ^ 4) /
    siegelFunction ![(1 / 2 : ℝ), 1 / 2] (z + (↑(2 : ℝ) : ℂ)) ^ 4 = lambdaRatio τ
  rw [hnum, hden, lambdaRatio, neg_mul_eq_mul_neg,
    mul_div_mul_left _ _ (pow_ne_zero _ (Complex.exp_ne_zero _))]

theorem lambdaCusp_zero_and_deriv : UpperHalfPlane.cuspFunction 2 lambdaRatio 0 = 0 ∧
    HasDerivAt (UpperHalfPlane.cuspFunction 2 lambdaRatio) (16 : ℂ) 0 :=
  lambdaCusp_simple_zero lambdaRatio_periodic

/-- The cusp function agrees with the upper-half-plane ratio in its q-coordinate. -/
theorem lambdaCusp_eq_on_q (τ : ℍ) :
    UpperHalfPlane.cuspFunction 2 lambdaRatio (Complex.exp (Real.pi * I * (τ : ℂ))) =
      lambdaRatio τ := by
  rw [← qParam_eq_exp]
  exact UpperHalfPlane.eq_cuspFunction τ (by norm_num) lambdaRatio_periodic

/-- The cusp function is differentiable throughout the open unit disc. -/
theorem lambdaCusp_differentiableAt {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (UpperHalfPlane.cuspFunction 2 lambdaRatio) q :=
  UpperHalfPlane.differentiableAt_cuspFunction (by norm_num) lambdaRatio_periodic
    lambdaRatio_mdifferentiable (lambdaRatio_tendsto_zero.isBigO_one ℝ) hq

#print axioms lambdaCusp_eq_on_q
#print axioms lambdaCusp_differentiableAt
#print axioms lambdaRatio_tendsto_zero
#print axioms lambdaRatio_periodic
#print axioms lambdaCusp_zero_and_deriv
#print axioms lambdaCusp_simple_zero
#print axioms lambdaRatio_ne_zero
#print axioms lambdaRatio_mdifferentiable
#print axioms lambdaRatio_div_q_tendsto

private noncomputable def halfGrid (a : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => (a i : ℝ) / 2

/-- Integral shifts of a half-integral Siegel parameter have fourth-power multiplier one. -/
private theorem halfGrid_shift_pow_four (a s : Fin 2 → ℤ) (τ : ℍ) :
    siegelFunction (halfGrid a + fun i => (s i : ℝ)) τ ^ 4 =
      siegelFunction (halfGrid a) τ ^ 4 := by
  let n := s 0 * s 1 + s 0 + s 1
  let m := s 1 * a 0 - s 0 * a 1
  have hsign : ((-1 : ℂ) ^ n) ^ 4 = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    exact Even.neg_one_zpow ⟨2 * n, by ring⟩
  have hexponent : (↑(4 : ℕ) : ℂ) *
      (-(Real.pi * I * (s 0 * halfGrid a 1 - s 1 * halfGrid a 0))) =
      (m : ℂ) * (2 * Real.pi * I) := by
    simp only [m, halfGrid]
    push_cast
    ring
  have hphase : (Complex.exp
      (-(Real.pi * I * (s 0 * halfGrid a 1 - s 1 * halfGrid a 0)))) ^ 4 = 1 := by
    rw [← Complex.exp_nat_mul, hexponent, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  rw [siegelFunction_add_intCast _ _ τ.im_pos, mul_pow, mul_pow]
  change (((-1 : ℂ) ^ n) ^ 4 * _) * _ = _
  rw [hsign, hphase, one_mul, one_mul]

/-- The Siegel ratio is invariant under the principal level-two congruence subgroup. -/
theorem lambdaRatio_gammaTwo {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma 2)
    (τ : ℍ) : lambdaRatio (γ • τ) = lambdaRatio τ := by
  have hmod : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod 2)) = 1 := by
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_one,
      RingHom.mapMatrix_apply] using congrArg Subtype.val (CongruenceSubgroup.Gamma_mem'.mp hγ)
  obtain ⟨ε, hε, htransform⟩ := exists_siegelFunction_smul_eq_mul γ
  have hε₄ : ε ^ 4 ≠ 0 := pow_ne_zero _ (by intro h; simp [h] at hε)
  have hpow (a : Fin 2 → ℤ) :
      siegelFunction (halfGrid a) (↑(γ • τ) : ℂ) ^ 4 = ε ^ 4 * siegelFunction (halfGrid a) τ ^ 4 := by
    obtain ⟨s, hs⟩ := (γ : Matrix (Fin 2) (Fin 2) ℤ).exists_vecMul_div_eq_add_intCast
      (K := ℝ) hmod a
    norm_num at hs
    rw [htransform]
    erw [hs]
    rw [mul_pow]
    change ε ^ 4 * siegelFunction (halfGrid a + fun i => (s i : ℝ)) τ ^ 4 = _
    rw [halfGrid_shift_pow_four]
  have hnum : halfGrid ![0, 1] = ![0, (1 / 2 : ℝ)] := by ext i; fin_cases i <;> norm_num [halfGrid]
  have hden : halfGrid ![1, 1] = ![(1 / 2 : ℝ), 1 / 2] := by ext i; fin_cases i <;> norm_num [halfGrid]
  rw [lambdaRatio, lambdaRatio, ← hnum, ← hden, hpow, hpow, neg_mul_eq_mul_neg,
    mul_div_mul_left _ _ hε₄]

#print axioms lambdaRatio_gammaTwo




/-- Weber's identity expresses the complement of the ratio using the remaining Siegel function. -/
theorem one_sub_lambdaRatio (τ : ℍ) : 1 - lambdaRatio τ =
    -(siegelFunction ![(1 / 2 : ℝ), 0] τ ^ 4) /
      siegelFunction ![(1 / 2 : ℝ), 1 / 2] τ ^ 4 := by
  have h := siegelFunction_pow_four_add_add τ
  let d := siegelFunction ![(1 / 2 : ℝ), 1 / 2] τ ^ 4
  let n := siegelFunction ![0, (1 / 2 : ℝ)] τ ^ 4
  let m := siegelFunction ![(1 / 2 : ℝ), 0] τ ^ 4
  change 1 - (-n / d) = -m / d
  calc
    1 - (-n / d) = (d - (-n)) / d := by
      rw [sub_div, div_self (pow_ne_zero 4 (denominator_ne_zero τ))]
    _ = -m / d := by
      congr 1
      dsimp only [d, n, m]
      linear_combination h

/-- The level-two ratio omits one as well as zero. -/
theorem lambdaRatio_ne_one (τ : ℍ) : lambdaRatio τ ≠ 1 := by
  have hnum : siegelFunction ![(1 / 2 : ℝ), 0] τ ≠ 0 := by
    apply siegelFunction_ne_zero _ τ.im_pos
    intro k hk
    exact half_ne_intCast (k 0) (by simpa using congrFun hk 0)
  intro h
  have hn := div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 4 hnum))
    (pow_ne_zero 4 (denominator_ne_zero τ))
  apply hn
  rw [← one_sub_lambdaRatio τ, h, sub_self]

#print axioms one_sub_lambdaRatio
#print axioms lambdaRatio_ne_one
end BelgianChocolate.ModularLambdaRatio

