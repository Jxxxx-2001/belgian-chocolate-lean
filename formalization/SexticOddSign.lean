import Conjecture3
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Polynomial
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)
open scoped Topology
set_option maxHeartbeats 1200000

noncomputable def imagPoint (t : ℝ) := ((t/(1-t) : ℝ):ℂ)*Complex.I

def HasContinuousPhase (p : ℝ[X]) : Prop :=
  ∃ α : ℝ → ℝ, ContinuousOn α (Set.Icc 0 1) ∧ α 0 = 0 ∧
    α 1 = (p.natDegree:ℝ)*Real.pi/2 ∧
    ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ r : ℝ, 0 < r ∧
      aeval (imagPoint t) p = (r:ℂ)*phase (α t)

private theorem continuous_angle {w : ℝ → ℂ} (hc : Continuous w)
    (hnz : ∀ t ∈ Set.Icc (0:ℝ) 1, w t ≠ 0) :
    ContinuousOn (fun t => Real.arccos ((w t).re / ‖w t‖)) (Set.Icc 0 1) := by
  apply Real.continuous_arccos.comp_continuousOn
  exact (Complex.continuous_re.comp hc).continuousOn.div hc.norm.continuousOn
    (fun t ht => norm_ne_zero_iff.mpr (hnz t ht))

private theorem angle_representation (z : ℂ) (hn : z ≠ 0) (hi : 0 ≤ z.im) :
    (‖z‖:ℂ) * phase (Real.arccos (z.re/‖z‖)) = z := by
  rw [← Complex.arg_of_im_nonneg_of_ne_zero hi hn]
  exact Complex.norm_mul_exp_arg_mul_I z

private theorem hasPhase_linear (a : ℝ) (ha : 0 < a) : HasContinuousPhase (X+C a) := by
  let w : ℝ → ℂ := fun t => ((a*(1-t):ℝ):ℂ)+(t:ℂ)*Complex.I
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hre (t : ℝ) : (w t).re = a*(1-t) := by simp [w,Complex.mul_re]
  have him (t : ℝ) : (w t).im = t := by simp [w,Complex.mul_im]
  have hnz : ∀ t ∈ Set.Icc (0:ℝ) 1, w t ≠ 0 := by
    intro t ht hz
    have h0 := congrArg Complex.im hz
    simp only [him,Complex.zero_im] at h0
    have h1 := congrArg Complex.re hz
    simp only [hre,Complex.zero_re,h0,sub_zero,mul_one] at h1
    linarith
  refine ⟨fun t => Real.arccos ((w t).re/‖w t‖), continuous_angle hw hnz, ?_, ?_, ?_⟩
  · have hw0 : w 0 = (a:ℂ) := by simp [w]
    dsimp only
    rw [hw0,Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,div_self ha.ne']
    exact Real.arccos_one
  · have hw1 : w 1 = Complex.I := by simp [w]
    simp [hw1,Real.arccos_zero]
  · intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have hden : 0 < 1-t := sub_pos.mpr ht.2
    have hd : (1-(t:ℂ)) ≠ 0 := by exact_mod_cast hden.ne'
    refine ⟨‖w t‖/(1-t),div_pos (norm_pos_iff.mpr (hnz t ht')) hden,?_⟩
    push_cast
    rw [div_mul_eq_mul_div, angle_representation (w t) (hnz t ht') (by rw [him]; exact ht.1.le)]
    simp only [imagPoint,w, map_add, aeval_X, aeval_C, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_mul]
    change ((t:ℂ)/(1-(t:ℂ)))*Complex.I + (a:ℂ) =
      ((a:ℂ)*(1-(t:ℂ))+(t:ℂ)*Complex.I)/(1-(t:ℂ))
    field_simp
    ring

private theorem hasPhase_quadratic (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasContinuousPhase (X^2+C a*X+C b) := by
  have hdeg : (X^2+C a*X+C b).natDegree = 2 := by compute_degree <;> norm_num
  let w : ℝ → ℂ := fun t =>
    ((b*(1-t)^2-t^2:ℝ):ℂ)+((a*t*(1-t):ℝ):ℂ)*Complex.I
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hre (t : ℝ) : (w t).re = b*(1-t)^2-t^2 := by
    change (((b*(1-t)^2-t^2:ℝ):ℂ)+((a*t*(1-t):ℝ):ℂ)*Complex.I).re = _
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him (t : ℝ) : (w t).im = a*t*(1-t) := by
    change (((b*(1-t)^2-t^2:ℝ):ℂ)+((a*t*(1-t):ℝ):ℂ)*Complex.I).im = _
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hw0 : w 0 = (b:ℂ) := by simp [w]
  have hw1 : w 1 = -1 := by simp [w]
  have hnz : ∀ t ∈ Set.Icc (0:ℝ) 1, w t ≠ 0 := by
    intro t ht hz
    by_cases h0 : t = 0
    · rw [h0,hw0] at hz
      exact hb.ne' (Complex.ofReal_eq_zero.mp hz)
    by_cases h1 : t = 1
    · simp [h1,hw1] at hz
    have hp : 0 < (w t).im := by
      rw [him]
      exact mul_pos (mul_pos ha (lt_of_le_of_ne ht.1 (Ne.symm h0))) (sub_pos.mpr
        (lt_of_le_of_ne ht.2 h1))
    simp [hz] at hp
  refine ⟨fun t => Real.arccos ((w t).re/‖w t‖),continuous_angle hw hnz,?_,?_,?_⟩
  · dsimp only
    rw [hw0,Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb,div_self hb.ne']
    exact Real.arccos_one
  · simp [hw1,hdeg,Real.arccos_neg_one]
  · intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have hden : 0 < 1-t := sub_pos.mpr ht.2
    have hd : (1-(t:ℂ)) ≠ 0 := by exact_mod_cast hden.ne'
    refine ⟨‖w t‖/(1-t)^2,div_pos (norm_pos_iff.mpr (hnz t ht')) (pow_pos hden _),?_⟩
    push_cast
    rw [div_mul_eq_mul_div, angle_representation (w t) (hnz t ht') (by
      rw [him]; exact mul_nonneg (mul_nonneg ha.le ht.1.le) hden.le)]
    simp only [imagPoint,w,map_add,map_pow,map_mul,aeval_X,aeval_C,Complex.ofReal_div,
      Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_pow]
    change (((t:ℂ)/(1-(t:ℂ)))*Complex.I)^2 +
      (a:ℂ)*(((t:ℂ)/(1-(t:ℂ)))*Complex.I)+(b:ℂ) =
        ((b:ℂ)*(1-(t:ℂ))^2-(t:ℂ)^2+(a:ℂ)*(t:ℂ)*(1-(t:ℂ))*Complex.I)/(1-(t:ℂ))^2
    field_simp
    linear_combination (t:ℂ)^2 * Complex.I_sq

private theorem hasPhase_mul {p q : ℝ[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : HasContinuousPhase p) (hq : HasContinuousPhase q) : HasContinuousPhase (p*q) := by
  obtain ⟨α,hα,hα0,hα1,hαv⟩ := hp
  obtain ⟨β,hβ,hβ0,hβ1,hβv⟩ := hq
  refine ⟨fun t => α t+β t,hα.add hβ,by dsimp only; rw [hα0,hβ0,zero_add],?_,?_⟩
  · dsimp only
    rw [hα1,hβ1,natDegree_mul hp0 hq0,Nat.cast_add]
    ring
  · intro t ht
    obtain ⟨x,hx,hxv⟩ := hαv t ht
    obtain ⟨y,hy,hyv⟩ := hβv t ht
    refine ⟨x*y,mul_pos hx hy,?_⟩
    rw [map_mul,hxv,hyv,phase_add,Complex.ofReal_mul]
    ring

theorem stable_hasPhase {p : ℝ[X]} (hm : p.Monic) (hs : StrictlyStable p) :
    HasContinuousPhase p := by
  refine stable_induction (P := HasContinuousPhase) ?_ ?_ ?_ p hm hs
  · exact ⟨fun _ => 0,continuousOn_const, rfl, by simp,fun _ _ => ⟨1,by norm_num,by simp⟩⟩
  · intro a q ha hq _ ih
    exact hasPhase_mul (monic_X_add_C a).ne_zero hq.ne_zero (hasPhase_linear a ha) ih
  · intro a b q ha hb hq _ ih
    exact hasPhase_mul (stable_quadratic a b ha hb).1 hq.ne_zero (hasPhase_quadratic a b ha hb) ih

/-- The odd part of a strictly Hurwitz sextic is negative somewhere on the positive imaginary axis. -/
theorem sextic_odd_sign {p : ℝ[X]} (hm : p.Monic) (hs : StrictlyStable p)
    (hd : p.natDegree = 6) :
    ∃ u : ℝ, 0 < u ∧ p.coeff 1-u*p.coeff 3+u^2*p.coeff 5 < 0 := by
  obtain ⟨α,hc,hα0,hα1,hF⟩ := stable_hasPhase hm hs
  have hgoal : (3*Real.pi/2) ∈ Set.Icc (α 0) (α 1) := by
    rw [hα0,hα1,hd]
    constructor <;> nlinarith [Real.pi_pos]
  obtain ⟨t,ht,heq⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hc hgoal
  have ht' : t ∈ Set.Ioo (0:ℝ) 1 := by
    constructor
    · by_contra! h
      have ht0 : t=0 := le_antisymm h ht.1
      rw [ht0,hα0] at heq
      linarith [Real.pi_pos]
    · by_contra! h
      have ht1 : t=1 := le_antisymm ht.2 h
      rw [ht1,hα1,hd] at heq
      norm_num at heq
  obtain ⟨r,hr,hval⟩ := hF t ht'
  rw [heq] at hval
  have hneg : (aeval (imagPoint t) p).im < 0 := by
    rw [hval,Complex.mul_im]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,phase_im]
    rw [show (3:ℝ)*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.sin_add]
    simp [hr]
  let w := t/(1-t)
  have hw : 0 < w := div_pos ht'.1 (sub_pos.mpr ht'.2)
  have hEval : (aeval (imagPoint t) p).im =
      w*(p.coeff 1-w^2*p.coeff 3+(w^2)^2*p.coeff 5) := by
    rw [aeval_def,eval₂_eq_sum_range,hd]
    change (∑ k ∈ Finset.range 7, ((p.coeff k:ℝ):ℂ)*((w:ℂ)*Complex.I)^k).im = _
    have hI3 : Complex.I^3 = -Complex.I := by
      calc
        Complex.I^3 = Complex.I^2*Complex.I := by ring
        _ = -Complex.I := by rw [Complex.I_sq,neg_one_mul]
    have hI4 : Complex.I^4 = 1 := by
      calc
        Complex.I^4 = (Complex.I^2)^2 := by ring
        _ = 1 := by rw [Complex.I_sq]; norm_num
    have hI5 : Complex.I^5 = Complex.I := by
      calc
        Complex.I^5 = Complex.I^4*Complex.I := by ring
        _ = Complex.I := by rw [hI4,one_mul]
    have hI6 : Complex.I^6 = -1 := by
      calc
        Complex.I^6 = (Complex.I^2)^3 := by ring
        _ = -1 := by rw [Complex.I_sq]; norm_num
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_pow,
      pow_zero, pow_one, Complex.I_sq,hI3,hI4,hI5,hI6, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_pow,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.one_im,
      Complex.one_re]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hEval] at hneg
  exact ⟨w^2,pow_pos hw _,neg_of_mul_neg_right hneg hw.le⟩

end BelgianChocolate.Conjectures

