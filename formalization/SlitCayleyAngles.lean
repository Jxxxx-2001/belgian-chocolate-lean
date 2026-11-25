import JoukowskiHalfDisk
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

namespace BelgianChocolate.NormalizationCenter
open Complex Set

/-- Ordered angle of the boundary point on the circle corresponding to a
real prevertex under the inverse Cayley transform. -/
noncomputable def cayleyAngle (x : ℝ) := Real.pi + 2 * Real.arctan x

theorem cayleyAngle_mem (x : ℝ) : cayleyAngle x ∈ Ioo 0 (2*Real.pi) := by
  constructor <;> dsimp [cayleyAngle] <;> linarith [Real.arctan_lt_pi_div_two x,Real.neg_pi_div_two_lt_arctan x]

theorem cayleyAngle_strictMono : StrictMono cayleyAngle := by
  intro x y h
  dsimp [cayleyAngle]
  linarith [Real.arctan_strictMono h]

theorem cayleyAngle_surjOn : SurjOn cayleyAngle univ (Ioo 0 (2*Real.pi)) := by
  intro θ hθ
  refine ⟨Real.tan ((θ-Real.pi)/2),mem_univ _,?_⟩
  unfold cayleyAngle
  rw [Real.arctan_tan (by linarith [hθ.1]) (by linarith [hθ.2])]
  ring

theorem cayley_circle_at_angle (x : ℝ) :
    I*(1+circleMap 0 1 (cayleyAngle x))/(1-circleMap 0 1 (cayleyAngle x)) = (x : ℂ) := by
  let a := Real.arctan x
  let u : ℂ := exp ((a : ℂ)*I)
  have hu : u ≠ 0 := exp_ne_zero _
  have hs : Real.sin a = x * Real.cos a := by
    have h := Real.tan_arctan x
    rw [Real.tan_eq_sin_div_cos] at h
    exact (div_eq_iff (Real.cos_pos_of_mem_Ioo ⟨Real.neg_pi_div_two_lt_arctan _,Real.arctan_lt_pi_div_two _⟩).ne').mp h
  have hu1 : u = (Real.cos a : ℂ) + (Real.sin a : ℂ)*I := by
    simpa [u] using exp_mul_I (a : ℂ)
  have hu2 : u⁻¹ = (Real.cos a : ℂ) - (Real.sin a : ℂ)*I := by
    rw [show u⁻¹ = exp (((-a : ℝ) : ℂ)*I) by simp [u,exp_neg]]
    simpa [sub_eq_add_neg] using exp_mul_I ((-a : ℝ) : ℂ)
  have hθ : circleMap 0 1 (cayleyAngle x) = -u^2 := by
    simp only [cayleyAngle,circleMap_zero,Complex.ofReal_one,one_mul,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
    rw [add_mul,Complex.exp_add,Complex.exp_pi_mul_I,neg_one_mul]
    congr 1
    rw [show (2 * ↑(Real.arctan x) * I) = ↑(Real.arctan x)*I + ↑(Real.arctan x)*I by ring,
      Complex.exp_add,pow_two]
  have hc : (Real.cos a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.cos_pos_of_mem_Ioo ⟨Real.neg_pi_div_two_lt_arctan _,Real.arctan_lt_pi_div_two _⟩).ne'
  have hplus : u⁻¹ + u = 2*(Real.cos a : ℂ) := by rw [hu2,hu1]; ring
  have hminus : I*(u⁻¹-u) = 2*(Real.sin a : ℂ) := by
    rw [hu2,hu1]
    linear_combination -(2*(Real.sin a : ℂ))*Complex.I_sq
  have hne : 1+u^2 ≠ 0 := by
    intro h
    have hh : u*(u⁻¹+u) = 0 := by rw [mul_add,mul_inv_cancel₀ hu,← sq,h]
    rw [hplus] at hh
    exact (mul_ne_zero hu (mul_ne_zero (by norm_num) hc)) hh
  rw [hθ,sub_neg_eq_add,div_eq_iff hne]
  have he : I*(u⁻¹-u) = (x : ℂ)*(u⁻¹+u) := by
    rw [hplus,hminus,hs,Complex.ofReal_mul]
    ring
  have hh := congrArg (fun z : ℂ => z*u) he
  change (I*(u⁻¹-u))*u = ((x : ℂ)*(u⁻¹+u))*u at hh
  linear_combination (norm := (field_simp [hu]; ring)) hh

end BelgianChocolate.NormalizationCenter

