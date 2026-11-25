import UpperHalfDiskPuncture
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The Joukowski coordinate for the open upper half of the unit disc. -/

namespace BelgianChocolate.NormalizationCenter

open Complex Metric Set
open UpperHalfDisk

/-- Lower half-plane coordinates of the marked half-disc. -/
def lowerHalfPlane : Set ℂ := {w | w.im < 0}

/-- The Joukowski map, using Lean's total inverse at the excluded point zero. -/
noncomputable def joukowski (z : ℂ) : ℂ := z + z⁻¹

theorem joukowski_re (z : ℂ) :
    (joukowski z).re = z.re * (1 + (‖z‖ ^ 2)⁻¹) := by
  simp only [joukowski, add_re, inv_re, normSq_eq_norm_sq, div_eq_mul_inv]
  ring

theorem joukowski_im (z : ℂ) :
    (joukowski z).im = z.im * (1 - (‖z‖ ^ 2)⁻¹) := by
  simp only [joukowski, add_im, inv_im, normSq_eq_norm_sq, div_eq_mul_inv]
  ring

theorem joukowski_im_lt_zero_iff {z : ℂ} (hz : z ≠ 0) (hn : ‖z‖ < 1) :
    (joukowski z).im < 0 ↔ 0 < z.im := by
  have hp := norm_pos_iff.mpr hz
  have hs : 0 < ‖z‖ ^ 2 := by positivity
  have hlt : ‖z‖ ^ 2 < 1 := by nlinarith
  have hi : 1 < (‖z‖ ^ 2)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hs, one_mul]
    exact hlt
  rw [joukowski_im, mul_neg_iff]
  have hf : 1 - (‖z‖ ^ 2)⁻¹ < 0 := sub_neg.mpr hi
  simp [hf, not_lt.mpr hf.le]

theorem joukowski_mapsTo : MapsTo joukowski domain lowerHalfPlane := by
  intro z hz
  have hn : z ≠ 0 := by
    intro h
    simpa [h] using hz.2
  exact (joukowski_im_lt_zero_iff hn hz.1).2 hz.2

private theorem norm_lt_one_ne_zero {z : ℂ} (hz : z ∈ domain) : z ≠ 0 := by
  intro h
  simpa [h] using hz.2

theorem joukowski_injOn : InjOn joukowski domain := by
  intro z hz w hw he
  have hz0 := norm_lt_one_ne_zero hz
  have hw0 := norm_lt_one_ne_zero hw
  have hprod : (z - w) * (z * w - 1) = 0 := by
    unfold joukowski at he
    have hh := congrArg (fun q : ℂ => q * (z * w)) he
    field_simp [hz0, hw0] at hh
    linear_combination hh
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have hnorm : ‖z‖ * ‖w‖ = 1 := by
      simpa only [norm_mul, norm_one] using congrArg norm (sub_eq_zero.mp h)
    have hz1 : ‖z‖ < 1 := hz.1
    have hw1 : ‖w‖ < 1 := hw.1
    have hlt := mul_lt_mul' hz1.le hw1 (norm_pos_iff.mpr hw0).le (by norm_num : (0 : ℝ) < 1)
    linarith

private theorem exists_quadraticPreimage (w : ℂ) : ∃ z ≠ 0, joukowski z = w := by
  let d := Complex.sqrt (w ^ 2 - 4)
  let z := (w + d) / 2
  have hd : d ^ 2 = w ^ 2 - 4 := Complex.sq_sqrt _
  have hroot : z ^ 2 - w * z + 1 = 0 := by
    dsimp [z]
    linear_combination (1/4 : ℂ) * hd
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hroot
  refine ⟨z, hz, ?_⟩
  unfold joukowski
  field_simp [hz]
  linear_combination hroot

theorem joukowski_surjOn : SurjOn joukowski domain lowerHalfPlane := by
  intro w hw
  obtain ⟨z, hz, he⟩ := exists_quadraticPreimage w
  have hw' : w.im < 0 := hw
  have hn : ‖z‖ ≠ 1 := by
    intro h
    have him := joukowski_im z
    rw [he, h, one_pow, inv_one, sub_self, mul_zero] at him
    exact hw'.ne him
  suffices h : ∃ q ≠ 0, ‖q‖ < 1 ∧ joukowski q = w by
    obtain ⟨q, hq, hq1, hqw⟩ := h
    refine ⟨q, ⟨hq1, (joukowski_im_lt_zero_iff hq hq1).1 ?_⟩, hqw⟩
    rwa [hqw]
  rcases lt_or_gt_of_ne hn with h | h
  · exact ⟨z, hz, h, he⟩
  · refine ⟨z⁻¹, inv_ne_zero hz, ?_, ?_⟩
    · rw [norm_inv, inv_eq_one_div, div_lt_iff₀ (norm_pos_iff.mpr hz), one_mul]
      exact h
    · simpa only [joukowski, inv_inv, add_comm] using he

theorem joukowski_bijOn : BijOn joukowski domain lowerHalfPlane :=
  ⟨joukowski_mapsTo, joukowski_injOn, joukowski_surjOn⟩

theorem hasDerivAt_joukowski {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt joukowski (1 - z⁻¹ ^ 2) z := by
  change HasDerivAt (id + fun q : ℂ => q⁻¹) (1 - z⁻¹ ^ 2) z
  simpa only [sub_eq_add_neg, inv_pow, neg_div, one_div] using
    (hasDerivAt_id z).add (hasDerivAt_inv hz)

theorem differentiableOn_joukowski : DifferentiableOn ℂ joukowski domain :=
  fun _ hz => (hasDerivAt_joukowski (norm_lt_one_ne_zero hz)).differentiableAt.differentiableWithinAt

theorem deriv_joukowski_ne_zero {z : ℂ} (hz : z ∈ domain) :
    deriv joukowski z ≠ 0 := by
  rw [(hasDerivAt_joukowski (norm_lt_one_ne_zero hz)).deriv]
  intro h
  have he : z⁻¹ ^ 2 = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖z‖⁻¹ ^ 2 = 1 := by
    simpa only [norm_pow, norm_inv, norm_one] using congrArg norm he
  have hz1 : ‖z‖ < 1 := hz.1
  have hp := norm_pos_iff.mpr (norm_lt_one_ne_zero hz)
  have hc : 1 < ‖z‖⁻¹ := by rw [inv_eq_one_div, lt_div_iff₀ hp, one_mul]; exact hz1
  nlinarith

theorem joukowski_re_eq_zero_iff (z : ℂ) : (joukowski z).re = 0 ↔ z.re = 0 := by
  rw [joukowski_re]
  have hp : 0 < 1 + (‖z‖ ^ 2)⁻¹ := by positivity
  simp [hp.ne']

#print axioms joukowski_bijOn
#print axioms deriv_joukowski_ne_zero
#print axioms joukowski_re_eq_zero_iff

end BelgianChocolate.NormalizationCenter

