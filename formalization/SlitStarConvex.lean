import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

/-! A radial negative slit preserves star convexity at the origin.
The candidate outer domain's star convexity is an explicit input. -/
namespace BelgianChocolate.SlitStarConvex
open Set Metric Complex

/-- The closed negative real ray ending at `α`. -/
def negativeRay (α : ℝ) : Set ℂ := {z | z.im = 0 ∧ z.re ≤ α}

/-- The finite real slit from `-1` to `α`, in physical complex coordinates. -/
def negativeSlit (α : ℝ) : Set ℂ := {z | z.im = 0 ∧ -1 ≤ z.re ∧ z.re ≤ α}

/-- The deformation towards zero cannot cross a negative real ray that
ends strictly before zero. Points initially on the separating real line
are allowed whenever they already avoid the ray. -/
theorem starConvex_remove_negativeRay {G : Set ℂ} {α : ℝ}
    (hG : StarConvex ℝ (0 : ℂ) G) (hα : α < 0) :
    StarConvex ℝ (0 : ℂ) (G \ negativeRay α) := by
  intro z hz a b ha hb hab
  simp only [smul_zero, zero_add]
  refine ⟨?_, ?_⟩
  · simpa only [smul_zero, zero_add] using hG hz.1 ha hb hab
  · intro hray
    change (b • z).im = 0 ∧ (b • z).re ≤ α at hray
    simp only [Complex.smul_im, Complex.smul_re, smul_eq_mul] at hray
    have hbne : b ≠ 0 := by
      intro h
      rw [h, zero_mul] at hray
      linarith [hray.2]
    have him : z.im = 0 := (mul_eq_zero.mp hray.1).resolve_left hbne
    have hb₁ : b ≤ 1 := by linarith
    have hzneg : z.re < 0 := by
      by_contra! h
      have hp := mul_nonneg hb h
      linarith [hray.2]
    have hzle : z.re ≤ α := by
      have hscale : z.re ≤ b * z.re := by nlinarith
      exact hscale.trans hray.2
    exact hz.2 ⟨him, hzle⟩

/-- Inside the open unit disc the infinite ray and the finite slit remove
exactly the same points. -/
theorem remove_negativeSlit_eq_remove_negativeRay {G : Set ℂ} (hG : G ⊆ ball 0 1) (α : ℝ) :
    G \ negativeSlit α = G \ negativeRay α := by
  ext z
  constructor
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, fun hray => ?_⟩
    apply hnot
    have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp (hG hz)
    have hr := Complex.re_le_norm (-z)
    simp only [Complex.neg_re, norm_neg] at hr
    exact ⟨hray.1, by linarith, hray.2⟩
  · rintro ⟨hz, hnot⟩
    exact ⟨hz, fun hslit => hnot ⟨hslit.1, hslit.2.2⟩⟩

/-- The actual finite slit therefore preserves the candidate domain's
star convexity. The statement does not assume a Jordan boundary for the slit domain. -/
theorem starConvex_remove_negativeSlit {G : Set ℂ} {α : ℝ}
    (hG : StarConvex ℝ (0 : ℂ) G) (hball : G ⊆ ball 0 1) (hα : α < 0) :
    StarConvex ℝ (0 : ℂ) (G \ negativeSlit α) := by
  rw [remove_negativeSlit_eq_remove_negativeRay hball]
  exact starConvex_remove_negativeRay hG hα

#print axioms starConvex_remove_negativeSlit
end BelgianChocolate.SlitStarConvex
