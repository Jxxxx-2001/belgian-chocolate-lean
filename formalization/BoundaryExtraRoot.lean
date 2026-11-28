import ContinuedFractionBound

open Polynomial
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)
set_option maxHeartbeats 1200000

private theorem sin_pos_between_two_pi_three_pi {t : ℝ}
    (hl : 2*Real.pi < t) (hr : t < 3*Real.pi) : 0 < Real.sin t := by
  rw [← Real.sin_sub_two_pi]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- A second right-half-plane root of the boundary numerator, beyond the plant's two roots. -/
theorem boundary_numerator_extra_root {m : ℕ} (hm : 7 ≤ m) {c : ℝ} (hc : 0 < c) :
    ∃ z : ℂ, 0 < z.re ∧ z^m = (c:ℂ)*(z^2-1) ∧
      aeval z (plant (δₙ (m-2))) ≠ 0 := by
  let L := 2*Real.pi/((m:ℝ)-2)
  let U := 3*Real.pi/(m:ℝ)
  have hmR : (7:ℝ) ≤ m := by exact_mod_cast hm
  have hm' : 0 < (m:ℝ)-2 := by linarith
  have hmR' : (0:ℝ) < m := by linarith
  have hLm : ((m:ℝ)-2)*L = 2*Real.pi := by
    dsimp [L]
    field_simp [hm'.ne']
  have hUm : (m:ℝ)*U = 3*Real.pi := by
    dsimp [U]
    field_simp
  have hL : 0 < L := div_pos (by positivity) hm'
  have hU : U < Real.pi/2 := by
    dsimp [U]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hLU : L < U := by
    dsimp [L,U]
    apply (div_lt_div_iff₀ hm' (by positivity)).mpr
    nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hmR) Real.pi_pos.le]
  have hLsin : 0 < Real.sin ((m:ℝ)*L) := by
    apply sin_pos_between_two_pi_three_pi
    · linarith
    · nlinarith only [hLm,hUm,mul_pos (show 0 < (m:ℝ) by positivity) (sub_pos.mpr hLU)]
  have hUsin : 0 < Real.sin (((m:ℝ)-2)*U) := by
    apply sin_pos_between_two_pi_three_pi
    · nlinarith only [hLm,mul_pos hm' (sub_pos.mpr hLU)]
    · linarith [hL.trans hLU]
  have hU2 : 0 < Real.sin (2*U) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hL.trans hLU]) (by linarith)
  let F := fun t : ℝ => Real.sin ((m:ℝ)*t)^m -
    c^2 * Real.sin (2*t)^2 * Real.sin (((m:ℝ)-2)*t)^(m-2)
  have hm0 : m ≠ 0 := by omega
  have hm2 : m-2 ≠ 0 := by omega
  have hFL : 0 < F L := by
    dsimp [F]
    rw [hLm, show Real.sin (2*Real.pi)=0 by rw [Real.sin_two_mul, Real.sin_pi]; ring, zero_pow hm2,
      mul_zero, sub_zero]
    exact pow_pos hLsin _
  have hFU : F U < 0 := by
    dsimp [F]
    rw [hUm, show 3*Real.pi = Real.pi+2*Real.pi by ring, Real.sin_add_two_pi,
      Real.sin_pi, zero_pow hm0, zero_sub]
    exact neg_lt_zero.mpr (by positivity)
  have hFc : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨φ,hφ,hFφ⟩ := intermediate_value_Icc' hLU.le hFc.continuousOn
    (show 0 ∈ Set.Icc (F U) (F L) from ⟨hFU.le,hFL.le⟩)
  have hφL : L < φ := lt_of_le_of_ne hφ.1 (fun e => hFL.ne' (e.symm ▸ hFφ))
  have hφU : φ < U := lt_of_le_of_ne hφ.2 (fun e => hFU.ne (e ▸ hFφ))
  have hφ0 : 0 < φ := hL.trans hφL
  have hφπ : φ < Real.pi/2 := hφU.trans hU
  let a := Real.sin ((m:ℝ)*φ)
  let b := Real.sin (((m:ℝ)-2)*φ)
  let t := Real.sin (2*φ)
  have ha : 0 < a := by
    apply sin_pos_between_two_pi_three_pi
    · nlinarith only [hLm, mul_pos (show 0 < (m:ℝ)-2 by linarith) (sub_pos.mpr hφL),hφ0]
    · nlinarith only [hUm,mul_pos (show 0 < (m:ℝ) by linarith) (sub_pos.mpr hφU)]
  have hb : 0 < b := by
    apply sin_pos_between_two_pi_three_pi
    · nlinarith only [hLm,mul_pos (show 0 < (m:ℝ)-2 by linarith) (sub_pos.mpr hφL)]
    · nlinarith only [hUm,mul_pos (show 0 < (m:ℝ) by linarith) (sub_pos.mpr hφU),hφ0]
  have ht : 0 < t := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  let r := Real.sqrt (a/b)
  have hr : 0 < r := Real.sqrt_pos.2 (div_pos ha hb)
  have hr2 : r^2 = a/b := Real.sq_sqrt (div_pos ha hb).le
  have hpow : a^m = c^2 * t^2 * b^(m-2) := sub_eq_zero.mp hFφ
  have hrbal : r^2*b = a := (eq_div_iff hb.ne').mp hr2
  have hmod : r^m*b = c*t := by
    have hs : (r^m*b)^2 = (c*t)^2 := by
      apply mul_right_cancel₀ (pow_ne_zero (m-2) hb.ne')
      have hbm : b^m = b^2*b^(m-2) := by rw [← pow_add,show 2+(m-2)=m by omega]
      calc
        (r^m*b)^2 * b^(m-2) = (r^2*b)^m := by
          rw [mul_pow,mul_pow,← pow_mul,show m*2=2*m by omega,pow_mul,hbm]
          ring
        _ = (c*t)^2 * b^(m-2) := by rw [hrbal,hpow,mul_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
    · exact he
    · linarith [show 0 < r^m*b by positivity, show 0 < c*t by positivity]
  let z : ℂ := (r:ℂ)*phase φ
  have hzre : 0 < z.re := by
    simp only [z,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,phase_re]
    exact mul_pos hr (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hφπ⟩)
  have hzpow : z^m = (c:ℂ)*(z^2-1) := by
    apply mul_left_cancel₀ (a := phase (-((m:ℝ)*φ))) (Complex.exp_ne_zero _)
    have hleft : phase (-((m:ℝ)*φ))*z^m = ((r^m:ℝ):ℂ) := by
      dsimp [z]
      rw [mul_pow,phase_pow,← Complex.ofReal_pow]
      rw [show phase (-((m:ℝ)*φ))*(((r^m:ℝ):ℂ)*phase ((m:ℝ)*φ)) =
        ((r^m:ℝ):ℂ)*(phase ((m:ℝ)*φ)*phase (-((m:ℝ)*φ))) by ring,phase_pair,mul_one]
    have hright : phase (-((m:ℝ)*φ))*((c:ℂ)*(z^2-1)) =
        (c:ℂ)*((r:ℂ)^2*phase (-(((m:ℝ)-2)*φ))-phase (-((m:ℝ)*φ))) := by
      dsimp [z]
      rw [mul_pow,phase_pow]
      norm_num
      rw [← show -((m:ℝ)*φ)+2*φ = -(((m:ℝ)-2)*φ) by ring, phase_add]
      ring
    rw [hleft,hright]
    have hsin : a*Real.cos (((m:ℝ)-2)*φ)-b*Real.cos ((m:ℝ)*φ) = t := by
      dsimp [a,b,t]
      calc
        _ = Real.sin ((m:ℝ)*φ-((m:ℝ)-2)*φ) := by rw [Real.sin_sub]; ring
        _ = _ := by congr 1; ring
    apply Complex.ext
    · simp only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero,
        Complex.sub_re,phase_re,Real.cos_neg,← Complex.ofReal_pow]
      apply mul_right_cancel₀ hb.ne'
      linear_combination hmod - c * hsin -
        c * Real.cos (((m:ℝ)-2)*φ) * hrbal
    · simp only [Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,zero_mul,add_zero,
        Complex.sub_im,phase_im,Real.sin_neg,← Complex.ofReal_pow]
      change 0 = c * (r^2 * (-b)-(-a))
      rw [← hrbal]
      ring
  have hzIm : 0 < z.im := by
    simp only [z,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,phase_im]
    exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos]))
  refine ⟨z,hzre,hzpow,?_⟩
  let θ := Real.pi/(2*((m:ℝ)-1))
  have hm1 : 0 < (m:ℝ)-1 := by linarith
  have hθ0 : 0 < θ := div_pos Real.pi_pos (mul_pos (by norm_num) hm1)
  have hθL : θ < L := by
    dsimp [θ,L]
    apply (div_lt_div_iff₀ (mul_pos (by norm_num) hm1) hm').mpr
    nlinarith [Real.pi_pos, mul_pos hmR' Real.pi_pos]
  have hθdef : δₙ (m-2) = Real.cos θ := by
    unfold δₙ
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num
    congr 2
    ring
  have hp : aeval z (plant (Real.cos θ)) = (z-phase θ)*(z-phase (-θ)) := by
    simp only [plant,map_add,map_sub,map_mul,map_pow,aeval_X,aeval_C,map_one]
    rw [← map_mul (algebraMap ℝ ℂ)]
    change z^2 - ((2*Real.cos θ:ℝ):ℂ)*z+1 = _
    rw [← phase_sum]
    linear_combination -(phase_pair θ)
  rw [hθdef,hp,mul_ne_zero_iff]
  constructor
  · intro h
    have he := congrArg (fun v : ℂ => v.im*Real.cos θ-v.re*Real.sin θ) (sub_eq_zero.mp h)
    have hpos : 0 < r*Real.sin (φ-θ) := mul_pos hr
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθL.trans hφL]) (by linarith [Real.pi_pos]))
    simp only [z,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero,sub_zero,phase_re,phase_im] at he
    rw [Real.sin_sub, mul_sub, ← mul_assoc, ← mul_assoc] at hpos
    linarith only [he,hpos]
  · intro h
    have hi := congrArg Complex.im (sub_eq_zero.mp h)
    rw [phase_im,Real.sin_neg] at hi
    linarith [Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθL.trans hφL,Real.pi_pos])]

#print axioms boundary_numerator_extra_root
end BelgianChocolate.Conjectures

