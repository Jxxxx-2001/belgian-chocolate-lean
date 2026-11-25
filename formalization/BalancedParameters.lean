import JoukowskiHalfDisk
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! The half-plane Poisson weights and the exact balanced parameters. -/

namespace BelgianChocolate.NormalizationCenter

open Complex Set
open UpperHalfDisk

/-- Closed form of the lower half-plane Poisson mass of the ray ending at a. -/
noncomputable def rayCDF (a : ℝ) (w : ℂ) : ℝ :=
  1 / 2 + Real.arctan ((a - w.re) / (-w.im)) / Real.pi

noncomputable def leftWeight (p : ℂ) : ℝ := rayCDF (-2) (joukowski p)

noncomputable def rightWeight (p : ℂ) : ℝ := 1 - rayCDF 2 (joukowski p)

noncomputable def arcWeight (p : ℂ) : ℝ :=
  rayCDF 2 (joukowski p) - rayCDF (-2) (joukowski p)

theorem re_eq_zero_of_equal_rayWeights {p : ℂ} (hp : p ∈ domain)
    (h : leftWeight p = rightWeight p) : p.re = 0 := by
  let w := joukowski p
  have hw : w.im < 0 := joukowski_mapsTo hp
  change rayCDF (-2) w = 1 - rayCDF 2 w at h
  unfold rayCDF at h
  have he : Real.arctan ((-2 - w.re) / (-w.im)) =
      - Real.arctan ((2 - w.re) / (-w.im)) := by
    field_simp [Real.pi_ne_zero] at h
    linarith
  rw [← Real.arctan_neg] at he
  have hf := Real.arctan_injective he
  rw [← neg_div, div_left_inj' (neg_ne_zero.mpr hw.ne)] at hf
  exact (joukowski_re_eq_zero_iff p).1 (show w.re = 0 by linarith)

theorem exists_puncture_of_equal_rayWeights {p : ℂ} (hp : p ∈ domain)
    (h : leftWeight p = rightWeight p) :
    ∃ t ∈ Ioo (0 : ℝ) 1, p = puncture t := by
  refine ⟨p.im, ⟨hp.2, (Complex.im_le_norm p).trans_lt hp.1⟩, Complex.ext ?_ ?_⟩
  · simpa [puncture, Complex.mul_re] using re_eq_zero_of_equal_rayWeights hp h
  · simp [puncture, Complex.mul_im]

theorem arcWeight_puncture {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    arcWeight (puncture t) = (4 / Real.pi) * Real.arctan t := by
  have hre : (puncture t).re = 0 := by simp [puncture, Complex.mul_re]
  have him : (puncture t).im = t := by simp [puncture, Complex.mul_im]
  have hn : ‖puncture t‖ = t := by simp [puncture, abs_of_pos ht.1]
  have hr : (joukowski (puncture t)).re = 0 := (joukowski_re_eq_zero_iff _).2 hre
  have hi : -(joukowski (puncture t)).im = (1 - t^2) / t := by
    rw [joukowski_im, him, hn]
    field_simp [ht.1.ne']
    ring
  have hd : (1 - t^2 : ℝ) ≠ 0 := by
    have h : 0 < (1-t)*(1+t) := mul_pos (sub_pos.mpr ht.2) (by linarith [ht.1])
    nlinarith
  have harg : (2 : ℝ) / ((1 - t^2) / t) = 2*t / (1-t^2) := by
    field_simp [ht.1.ne', hd]
  rw [arcWeight, rayCDF, rayCDF, hr, hi, sub_zero, sub_zero, neg_div, Real.arctan_neg,
    harg, ← Real.two_mul_arctan (by linarith [ht.1]) ht.2]
  ring

theorem cos_arcWeight_puncture {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Real.cos ((Real.pi / 2) * arcWeight (puncture t)) = (1-t^2)/(1+t^2) := by
  rw [arcWeight_puncture ht, show Real.pi / 2 * (4 / Real.pi * Real.arctan t) =
    2 * Real.arctan t by field_simp [Real.pi_ne_zero]; ring,
    Real.cos_two_mul, Real.cos_sq_arctan]
  field_simp
  ring

/-- An equality of the two marked ray weights determines the source center and both
exact threshold formulas. -/
theorem exact_marked_parameters {p : ℂ} (hp : p ∈ domain)
    (h : leftWeight p = rightWeight p) :
    ∃ t ∈ Ioo (0 : ℝ) 1, p = puncture t ∧
      arcWeight p = (4 / Real.pi) * Real.arctan t ∧
      Real.cos ((Real.pi / 2) * arcWeight p) = (1-t^2)/(1+t^2) := by
  obtain ⟨t, ht, rfl⟩ := exists_puncture_of_equal_rayWeights hp h
  exact ⟨t, ht, rfl, arcWeight_puncture ht, cos_arcWeight_puncture ht⟩

#print axioms re_eq_zero_of_equal_rayWeights
#print axioms exact_marked_parameters

end BelgianChocolate.NormalizationCenter
