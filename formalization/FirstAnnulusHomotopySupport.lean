import Mathlib.Topology.Homotopy.Affine
import Mathlib.Analysis.Complex.Convex

namespace BelgianChocolate.FirstAnnulusHomotopySupport
open unitInterval

/-- Pointwise affine deformation of two paths stays in any common convex
subset of the ambient punctured domain. Endpoints remain fixed. -/
theorem homotopic_of_convex_range {Ω S : Set ℂ} (hS : Convex ℝ S) (hSΩ : S ⊆ Ω)
    {a b : Ω} (p q : Path a b)
    (hp : ∀ t, (p t : ℂ) ∈ S) (hq : ∀ t, (q t : ℂ) ∈ S) : p.Homotopic q := by
  refine ⟨{
    toFun := fun x => ⟨(1 - (x.1 : ℝ)) • (p x.2 : ℂ) + (x.1 : ℝ) • (q x.2 : ℂ),
      hSΩ (hS (hp x.2) (hq x.2) (by linarith [x.1.property.2]) x.1.property.1
        (by ring))⟩
    continuous_toFun := by fun_prop
    map_zero_left := by intro t; apply Subtype.ext; simp
    map_one_left := by intro t; apply Subtype.ext; simp
    prop' := by
      intro t x hx
      rcases hx with rfl | rfl
      · apply Subtype.ext
        change (1 - (t : ℝ)) • (p 0 : ℂ) + (t : ℝ) • (q 0 : ℂ) = (p 0 : ℂ)
        simp only [Path.source]
        rw [← add_smul, sub_add_cancel, one_smul]
      · apply Subtype.ext
        change (1 - (t : ℝ)) • (p 1 : ℂ) + (t : ℝ) • (q 1 : ℂ) = (p 1 : ℂ)
        simp only [Path.target]
        rw [← add_smul, sub_add_cancel, one_smul]
  }⟩


/-- A path on the weak side of a real linear functional can be deformed to
a path strictly on that side at every interior parameter. The initial path
may meet the separating line, provided it already avoids the obstacles.
The convex ambient set controls the disc radius throughout the deformation.
Taking the functional to be imaginary part or its negative handles both sides. -/
theorem homotopic_of_weak_strict_linear_side {Ω S : Set ℂ}
    (hS : Convex ℝ S) (hΩS : Ω ⊆ S) (ℓ : ℂ →ₗ[ℝ] ℝ)
    (hside : ∀ z ∈ S, 0 < ℓ z → z ∈ Ω)
    {a b : Ω} (p q : Path a b)
    (hp : ∀ u : unitInterval, u ≠ 0 → u ≠ 1 → 0 ≤ ℓ (p u : ℂ))
    (hq : ∀ u : unitInterval, u ≠ 0 → u ≠ 1 → 0 < ℓ (q u : ℂ)) :
    p.Homotopic q := by
  have hmem (s u : unitInterval) :
      (1 - (s : ℝ)) • (p u : ℂ) + (s : ℝ) • (q u : ℂ) ∈ Ω := by
    by_cases hs : s = 0
    · subst s
      simp
    by_cases hu₀ : u = 0
    · subst u
      simpa only [Path.source, ← add_smul, sub_add_cancel, one_smul] using a.property
    by_cases hu₁ : u = 1
    · subst u
      simpa only [Path.target, ← add_smul, sub_add_cancel, one_smul] using b.property
    apply hside _ (hS (hΩS (p u).property) (hΩS (q u).property)
      (by linarith [s.property.2]) s.property.1 (by ring))
    have hsval : (s : ℝ) ≠ 0 := fun he => hs (Subtype.ext he)
    have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.property.1 hsval.symm
    simp only [map_add, map_smul]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr s.property.2) (hp u hu₀ hu₁))
      (mul_pos hspos (hq u hu₀ hu₁))
  refine ⟨{
    toFun := fun x => ⟨(1 - (x.1 : ℝ)) • (p x.2 : ℂ) +
      (x.1 : ℝ) • (q x.2 : ℂ), hmem x.1 x.2⟩
    continuous_toFun := by fun_prop
    map_zero_left := by intro t; apply Subtype.ext; simp
    map_one_left := by intro t; apply Subtype.ext; simp
    prop' := by
      intro t x hx
      rcases hx with rfl | rfl
      · apply Subtype.ext
        change (1 - (t : ℝ)) • (p 0 : ℂ) + (t : ℝ) • (q 0 : ℂ) = (p 0 : ℂ)
        simp only [Path.source]
        rw [← add_smul, sub_add_cancel, one_smul]
      · apply Subtype.ext
        change (1 - (t : ℝ)) • (p 1 : ℂ) + (t : ℝ) • (q 1 : ℂ) = (p 1 : ℂ)
        simp only [Path.target]
        rw [← add_smul, sub_add_cancel, one_smul]
  }⟩

end BelgianChocolate.FirstAnnulusHomotopySupport

