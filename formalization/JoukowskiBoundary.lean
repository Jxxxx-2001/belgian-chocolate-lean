import JoukowskiHalfDisk

/-! Images of the marked boundary arcs in the Joukowski coordinate. -/

namespace BelgianChocolate.NormalizationCenter

open Complex Metric Set
open UpperHalfDisk

/-- Negative part of the source diameter, excluding its two endpoints. -/
def negDiameter : Set ℂ := (Complex.ofReal : ℝ → ℂ) '' Ioo (-1 : ℝ) 0

/-- Positive part of the source diameter, excluding its two endpoints. -/
def posDiameter : Set ℂ := (Complex.ofReal : ℝ → ℂ) '' Ioo (0 : ℝ) 1

/-- Upper circular part of the source frontier, excluding its two endpoints. -/
def outerArc : Set ℂ := {z | ‖z‖ = 1 ∧ 0 < z.im}

theorem joukowski_ofReal (x : ℝ) : joukowski (x : ℂ) = ((x + x⁻¹ : ℝ) : ℂ) := by
  push_cast
  rfl

theorem joukowski_neg (z : ℂ) : joukowski (-z) = -joukowski z := by
  simp [joukowski, add_comm]

@[simp] theorem joukowski_one : joukowski 1 = 2 := by norm_num [joukowski]

@[simp] theorem joukowski_neg_one : joukowski (-1) = -2 := by
  rw [joukowski_neg, joukowski_one]

private theorem exists_real_preimage {w : ℝ} (hw : 2 < w) :
    ∃ x ∈ Ioo (0 : ℝ) 1, x + x⁻¹ = w := by
  let d := Real.sqrt (w ^ 2 - 4)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d ^ 2 = w ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have hp : 2 < w + d := by linarith
  have hp0 : 0 < w + d := by linarith
  refine ⟨2 / (w + d), ⟨by positivity, (div_lt_iff₀ hp0).2 (by simpa using hp)⟩, ?_⟩
  field_simp [hp0.ne']
  linear_combination hd2

private theorem two_lt_real_joukowski {x : ℝ} (h : x ∈ Ioo (0 : ℝ) 1) :
    2 < x + x⁻¹ := by
  rw [inv_eq_one_div]
  have he : x + 1 / x = (x * x + 1) / x := by field_simp
  rw [he, lt_div_iff₀ h.1]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h.2.ne)]

theorem image_joukowski_posDiameter :
    joukowski '' posDiameter = (Complex.ofReal : ℝ → ℂ) '' Ioi (2 : ℝ) := by
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x + x⁻¹, two_lt_real_joukowski hx, (joukowski_ofReal x).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, he⟩ := exists_real_preimage hw
    refine ⟨(x : ℂ), ⟨x, hx, rfl⟩, ?_⟩
    rw [joukowski_ofReal, he]

theorem image_joukowski_negDiameter :
    joukowski '' negDiameter = (Complex.ofReal : ℝ → ℂ) '' Iio (-2 : ℝ) := by
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : -x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := two_lt_real_joukowski hx'
    rw [inv_neg] at h
    exact ⟨x + x⁻¹, by change x + x⁻¹ < -2; linarith, (joukowski_ofReal x).symm⟩
  · rintro ⟨w, hw, rfl⟩
    have hw' : 2 < -w := by linarith [show w < -2 from hw]
    obtain ⟨x, hx, he⟩ := exists_real_preimage hw'
    refine ⟨((-x : ℝ) : ℂ), ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, rfl⟩, ?_⟩
    rw [joukowski_ofReal, inv_neg, ← neg_add, he, neg_neg]

theorem image_joukowski_outerArc :
    joukowski '' outerArc = (Complex.ofReal : ℝ → ℂ) '' Ioo (-2 : ℝ) 2 := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have he : ‖z‖ = 1 := hz.1
    have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, he, pow_two] using normSq_eq_norm_sq z
    have him : 0 < z.im := hz.2
    have hre : -1 < z.re ∧ z.re < 1 := by
      constructor <;> nlinarith [sq_pos_of_pos him]
    refine ⟨2 * z.re, ⟨by linarith [hre.1], by linarith [hre.2]⟩, Complex.ext ?_ ?_⟩
    · rw [ofReal_re, joukowski_re, he]
      norm_num
      ring
    · rw [ofReal_im, joukowski_im, he]
      norm_num
  · rintro ⟨w, hw, rfl⟩
    let x : ℝ := w/2
    let y : ℝ := Real.sqrt (1 - x ^ 2)
    let z : ℂ := ⟨x,y⟩
    have hx : x ^ 2 < 1 := by
      have ha : -1 < x := by dsimp [x]; linarith [hw.1]
      have hb : x < 1 := by dsimp [x]; linarith [hw.2]
      nlinarith [mul_pos (sub_pos.mpr hb) (by linarith : 0 < 1 + x)]
    have hy : 0 < y := Real.sqrt_pos.2 (sub_pos.mpr hx)
    have hy2 : y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hx.le)
    have hnorm : ‖z‖ = 1 := by
      have hh := normSq_eq_norm_sq z
      rw [Complex.normSq_apply] at hh
      change x * x + y * y = _ at hh
      nlinarith [norm_nonneg z]
    refine ⟨z, ⟨hnorm, hy⟩, Complex.ext ?_ ?_⟩
    · rw [joukowski_re, hnorm, ofReal_re]
      change x * (1 + ((1 : ℝ) ^ 2)⁻¹) = w
      dsimp [x]
      norm_num
    · rw [joukowski_im, hnorm, ofReal_im]
      norm_num

#print axioms image_joukowski_negDiameter
#print axioms image_joukowski_posDiameter
#print axioms image_joukowski_outerArc

end BelgianChocolate.NormalizationCenter
