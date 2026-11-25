import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace BelgianChocolate.MarkedRealAxis

open Complex Real Set

/-- The normalized cusp coordinate used on both real boundary intervals. -/
noncomputable def cusp (τ : ℂ) : ℂ := -Complex.exp (-((Real.pi : ℂ) * I) / τ)

/-- The curved edge, parametrized by its polar angle. -/
def curvedEdge : Set ℂ :=
  {w | ∃ θ ∈ Set.Ioo 0 Real.pi,
    w = (Real.exp (-Real.sqrt (θ * (Real.pi - θ))) : ℂ) * Complex.exp ((θ : ℂ) * I)}

private theorem cusp_zero_re {τ : ℂ} (hr : τ.re = 0) (hi : 0 < τ.im) :
    ∃ r ∈ Set.Ioo (-1 : ℝ) 0, cusp τ = (r : ℂ) := by
  have hnorm : Complex.normSq τ = τ.im ^ 2 := by
    simp [Complex.normSq_apply, hr, pow_two]
  have he : -((Real.pi : ℂ) * I) / τ = ((-(Real.pi / τ.im) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.div_re, hr, hnorm]
      field_simp
    · simp [Complex.div_im, hr, hnorm]
  refine ⟨-Real.exp (-(Real.pi / τ.im)), ⟨?_, neg_lt_zero.mpr (Real.exp_pos _)⟩, ?_⟩
  · have h := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos Real.pi_pos hi))
    linarith
  · simp [cusp, he, Complex.ofReal_exp]

private theorem cusp_one_re {τ : ℂ} (hr : τ.re = 1) (hi : 0 < τ.im) :
    cusp τ ∈ curvedEdge := by
  let d := 1 + τ.im ^ 2
  let θ := Real.pi * τ.im ^ 2 / d
  let a := Real.pi * τ.im / d
  have hd : 0 < d := by dsimp [d]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hrem : Real.pi - θ = Real.pi / d := by
    dsimp [θ, d]
    field_simp
    ring
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsq : θ * (Real.pi - θ) = a ^ 2 := by
    rw [hrem]
    dsimp [θ, a]
    ring
  refine ⟨θ, ⟨hθ, by linarith [div_pos Real.pi_pos hd, hrem]⟩, ?_⟩
  rw [hsq, Real.sqrt_sq ha]

  have hnorm : Complex.normSq τ = d := by
    simp [Complex.normSq_apply, hr, d, pow_two]
  have he : -((Real.pi : ℂ) * I) / τ + (Real.pi : ℂ) * I =
      ((-a : ℝ) : ℂ) + (θ : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.div_re, hr, hnorm, a]
      field_simp
    · simp [Complex.div_im, hr, hnorm]
      rw [neg_div]
      linarith [hrem]
  unfold cusp
  calc
    -Complex.exp _ = Complex.exp (-((Real.pi : ℂ) * I) / τ + (Real.pi : ℂ) * I) := by
      rw [Complex.exp_add, Complex.exp_pi_mul_I]; ring
    _ = _ := by rw [he, Complex.exp_add, Complex.ofReal_exp]

/-- Both markings refer to one branch function and the same cusp coordinate. -/
theorem marked_real_axes {τ : ℝ → ℂ}
    (hneg : ∀ x ∈ Set.Ioo (-1 : ℝ) 0, (τ x).re = 1 ∧ 0 < (τ x).im)
    (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, (τ x).re = 0 ∧ 0 < (τ x).im) :
    (∀ x ∈ Set.Ioo (-1 : ℝ) 0, cusp (τ x) ∈ curvedEdge) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, ∃ r ∈ Set.Ioo (-1 : ℝ) 0, cusp (τ x) = (r : ℂ)) := by
  exact ⟨fun x hx => cusp_one_re (hneg x hx).1 (hneg x hx).2,
    fun x hx => cusp_zero_re (hpos x hx).1 (hpos x hx).2⟩

end BelgianChocolate.MarkedRealAxis

