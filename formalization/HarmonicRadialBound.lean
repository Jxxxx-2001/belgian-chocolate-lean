import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith

open Complex Metric Set

namespace BelgianChocolate

private theorem norm_cayley_le_one {w : ℂ} {a : ℝ} (hw : 0 ≤ w.re) (ha : 0 < a) :
    ‖(w - (a : ℂ)) / (w + (a : ℂ))‖ ≤ 1 := by
  have hdenRe : 0 < (w + (a : ℂ)).re := by simpa using add_pos_of_nonneg_of_pos hw ha
  have hden : w + (a : ℂ) ≠ 0 := by
    intro he
    simp [he] at hdenRe
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hden), one_mul]
  have hsq : ‖w - (a : ℂ)‖ ^ 2 ≤ ‖w + (a : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, add_re, add_im,
      ofReal_re, ofReal_im, sub_zero, add_zero]
    nlinarith [mul_nonneg hw ha.le]
  nlinarith [norm_nonneg (w - (a : ℂ)), norm_nonneg (w + (a : ℂ))]

/-- A holomorphic map into the closed right half-plane with positive real value at zero
satisfies the lower Harnack bound for its real part. -/
theorem harnack_re_of_mapsTo_rightHalfPlane {A : ℂ → ℂ} {a : ℝ}
    (hA : DifferentiableOn ℂ A (ball 0 1))
    (hpos : ∀ z ∈ ball 0 1, 0 ≤ (A z).re)
    (hA0 : A 0 = (a : ℂ)) (ha : 0 < a) {z : ℂ} (hz : ‖z‖ < 1) :
    ((1 - ‖z‖) / (1 + ‖z‖)) * a ≤ (A z).re := by
  let T : ℂ → ℂ := fun w => (A w - (a : ℂ)) / (A w + (a : ℂ))
  have hden : ∀ w ∈ ball (0 : ℂ) 1, A w + (a : ℂ) ≠ 0 := by
    intro w hw he
    have h : 0 < (A w + (a : ℂ)).re := by
      simpa using add_pos_of_nonneg_of_pos (hpos w hw) ha
    simp [he] at h
  have hT : DifferentiableOn ℂ T (ball 0 1) :=
    (hA.sub (differentiableOn_const (a : ℂ))).div
      (hA.add (differentiableOn_const (a : ℂ))) hden
  have hTmaps : MapsTo T (ball 0 1) (closedBall 0 1) := by
    intro w hw
    exact mem_closedBall_zero_iff.mpr (norm_cayley_le_one (hpos w hw) ha)
  have hT0 : T 0 = 0 := by simp [T, hA0]
  have hTbound := Complex.norm_le_norm_of_mapsTo_ball hT hTmaps hT0 hz
  have hz' : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz
  change ‖(A z - (a : ℂ)) / (A z + (a : ℂ))‖ ≤ ‖z‖ at hTbound
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (hden z hz'))] at hTbound
  have hsq : ‖A z - (a : ℂ)‖ ^ 2 ≤ (‖z‖ * ‖A z + (a : ℂ)‖) ^ 2 := by
    gcongr
  rw [mul_pow] at hsq
  rw [Complex.sq_norm (A z - (a : ℂ)), Complex.sq_norm (A z + (a : ℂ))] at hsq
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im,
    ofReal_re, ofReal_im, sub_zero, add_zero] at hsq
  let x := (A z).re
  let y := (A z).im
  let r := ‖z‖
  change (x - a) * (x - a) + y * y ≤ r ^ 2 * ((x + a) * (x + a) + y * y) at hsq
  have hr : 0 ≤ r := norm_nonneg _
  have hr' : r ≤ 1 := hz.le
  have hx : 0 ≤ x := hpos z hz'
  have hy : r ^ 2 * (y * y) ≤ y * y := by
    have hr2 : r ^ 2 ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr')]
    simpa using mul_le_mul_of_nonneg_right hr2 (mul_self_nonneg y)
  have hsq' : (a - x) ^ 2 ≤ (r * (x + a)) ^ 2 := by nlinarith
  have hlin : a - x ≤ r * (x + a) := by
    by_contra! hlt
    have hnonneg : 0 ≤ r * (x + a) := mul_nonneg hr (add_nonneg hx ha.le)
    have hmul := mul_pos (sub_pos.mpr hlt) (show 0 < (a - x) + r * (x + a) by linarith)
    nlinarith
  change ((1 - r) / (1 + r)) * a ≤ x
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 + r)]
  linarith

/-- A strict drop from the normalized center to a lower bound for the imaginary
part yields the radial estimate used in the boundary minimum argument. -/
theorem im_sub_lowerBound_ge_harnack {F : ℂ → ℂ} {m : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hF0 : F 0 = 0) (hm : m < 0)
    (hlower : ∀ z ∈ ball 0 1, m ≤ (F z).im) {z : ℂ} (hz : ‖z‖ < 1) :
    ((1 - ‖z‖) / (1 + ‖z‖)) * (-m) ≤ (F z).im - m := by
  let A : ℂ → ℂ := fun z => -I * F z - (m : ℂ)
  have hA : DifferentiableOn ℂ A (ball 0 1) :=
    (hF.const_mul (-I)).sub (differentiableOn_const (m : ℂ))
  have hA0 : A 0 = ((-m : ℝ) : ℂ) := by simp [A, hF0]
  have hARe (w : ℂ) : (A w).re = (F w).im - m := by
    simp [A, Complex.mul_re]
  have hpos : ∀ w ∈ ball 0 1, 0 ≤ (A w).re := by
    intro w hw
    rw [hARe]
    exact sub_nonneg.mpr (hlower w hw)
  simpa only [hARe] using harnack_re_of_mapsTo_rightHalfPlane hA hpos hA0 (neg_pos.mpr hm) hz

end BelgianChocolate
