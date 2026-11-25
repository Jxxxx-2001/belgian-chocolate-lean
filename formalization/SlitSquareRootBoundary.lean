import SlitSquareRoot

namespace BelgianChocolate.SlitSquareRoot
open Complex Filter Topology

noncomputable def upperSqrt (z : ℂ) : ℂ :=
  (Real.sqrt ((‖z‖ + z.re) / 2) : ℂ) + (Real.sqrt ((‖z‖ - z.re) / 2) : ℂ) * I
noncomputable def lowerSqrt (z : ℂ) : ℂ :=
  (Real.sqrt ((‖z‖ + z.re) / 2) : ℂ) - (Real.sqrt ((‖z‖ - z.re) / 2) : ℂ) * I

theorem continuous_upperSqrt : Continuous upperSqrt := by unfold upperSqrt; fun_prop
theorem continuous_lowerSqrt : Continuous lowerSqrt := by unfold lowerSqrt; fun_prop

theorem sqrt_eq_upperSqrt {z : ℂ} (h : 0 ≤ z.im) : Complex.sqrt z = upperSqrt z := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp [upperSqrt, h]

theorem sqrt_eq_lowerSqrt {z : ℂ} (h : z.im < 0) : Complex.sqrt z = lowerSqrt z := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp [lowerSqrt, not_le.mpr h, sub_eq_add_neg]

theorem tendsto_unfolding_upper {X : Type*} {l : Filter X} {f : X → ℂ} {z : ℂ}
    (α : ℝ) (hf : Tendsto f l (𝓝 z)) (him : ∀ᶠ x in l, 0 ≤ (f x).im) :
    Tendsto (fun x => unfolding α (f x)) l (𝓝 (upperSqrt (z - (α : ℂ)))) := by
  have ht := continuous_upperSqrt.tendsto (z - (α : ℂ)) |>.comp (hf.sub_const (α : ℂ))
  apply ht.congr'
  filter_upwards [him] with x hx
  exact (sqrt_eq_upperSqrt (by simpa using hx)).symm

theorem tendsto_unfolding_lower {X : Type*} {l : Filter X} {f : X → ℂ} {z : ℂ}
    (α : ℝ) (hf : Tendsto f l (𝓝 z)) (him : ∀ᶠ x in l, (f x).im < 0) :
    Tendsto (fun x => unfolding α (f x)) l (𝓝 (lowerSqrt (z - (α : ℂ)))) := by
  have ht := continuous_lowerSqrt.tendsto (z - (α : ℂ)) |>.comp (hf.sub_const (α : ℂ))
  apply ht.congr'
  filter_upwards [him] with x hx
  exact (sqrt_eq_lowerSqrt (by simpa using hx)).symm

theorem upperSqrt_negative {a : ℝ} (ha : 0 ≤ a) :
    upperSqrt (-(a : ℂ)) = (Real.sqrt a : ℂ) * I := by
  have hn : ‖(-(a : ℂ))‖ = a := by simp [abs_of_nonneg ha]
  simp only [upperSqrt, hn, neg_re, ofReal_re]
  rw [show (a + -a) / 2 = 0 by ring, show (a - -a) / 2 = a by ring]
  simp

theorem lowerSqrt_negative {a : ℝ} (ha : 0 ≤ a) :
    lowerSqrt (-(a : ℂ)) = -(Real.sqrt a : ℂ) * I := by
  have hn : ‖(-(a : ℂ))‖ = a := by simp [abs_of_nonneg ha]
  simp only [lowerSqrt, hn, neg_re, ofReal_re]
  rw [show (a + -a) / 2 = 0 by ring, show (a - -a) / 2 = a by ring]
  simp

theorem tendsto_unfolding_upper_at_neg_one {X : Type*} {l : Filter X}
    {f : X → ℂ} {α : ℝ} (hα : -1 ≤ α) (hf : Tendsto f l (𝓝 (-1)))
    (him : ∀ᶠ x in l, 0 ≤ (f x).im) :
    Tendsto (fun x => unfolding α (f x)) l (𝓝 ((Real.sqrt (1 + α) : ℂ) * I)) := by
  have heq : (-1 : ℂ) - (α : ℂ) = -((1 + α : ℝ) : ℂ) := by push_cast; ring
  simpa only [heq, upperSqrt_negative (show 0 ≤ 1 + α by linarith)] using
    tendsto_unfolding_upper α hf him

theorem tendsto_unfolding_lower_at_neg_one {X : Type*} {l : Filter X}
    {f : X → ℂ} {α : ℝ} (hα : -1 ≤ α) (hf : Tendsto f l (𝓝 (-1)))
    (him : ∀ᶠ x in l, (f x).im < 0) :
    Tendsto (fun x => unfolding α (f x)) l (𝓝 (-(Real.sqrt (1 + α) : ℂ) * I)) := by
  have heq : (-1 : ℂ) - (α : ℂ) = -((1 + α : ℝ) : ℂ) := by push_cast; ring
  simpa only [heq, lowerSqrt_negative (show 0 ≤ 1 + α by linarith)] using
    tendsto_unfolding_lower α hf him

#print axioms tendsto_unfolding_upper_at_neg_one
#print axioms tendsto_unfolding_lower_at_neg_one
#print axioms tendsto_unfolding_upper
#print axioms tendsto_unfolding_lower
end BelgianChocolate.SlitSquareRoot
