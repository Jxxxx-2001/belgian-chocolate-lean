import ControllerDiskCompetitor

/-! A definite regular upper-arc point for every finite stable controller. -/

namespace BelgianChocolate.ControlWitness

open Complex Set Polynomial
open BelgianChocolate.HarmonicComparison

set_option backward.isDefEq.respectTransparency false

theorem comparisonQuotient_I : comparisonQuotient I = I := by
  have hn : (1 : ℂ) - I ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
  apply (div_eq_iff hn).mpr
  linear_combination Complex.I_sq

/-- The point i gives a regular value of the disk rational function for
every feasible finite controller with positive parameter. -/
theorem diskController_regular_at_I {δ : ℝ} (hδ : 0 < δ) {x y : ℝ[X]}
    (hx : StrictlyStable x) (hy : StrictlyStable y) (hq : StrictlyStable (closedLoop δ x y)) :
    ContinuousAt (diskController δ x y) I ∧
      diskController δ x y I ∈ ({0,1}ᶜ : Set ℂ) := by
  have he {p : ℝ[X]} (hp : StrictlyStable p) : aeval I p ≠ 0 := by
    intro h
    simpa using hp.2 I h
  have hs : ContinuousAt comparisonQuotient I := by
    have hn : (1 : ℂ) - I ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      simp at hh
    have h1 : ContinuousAt (fun _ : ℂ ↦ (1 : ℂ)) I := continuousAt_const
    have h2 : ContinuousAt (fun z : ℂ ↦ z) I := continuousAt_id
    exact (h1.add h2).div
      (h1.sub h2) hn
  have hc (p : ℝ[X]) : ContinuousAt (fun w : ℂ ↦ aeval (comparisonQuotient w) p) I :=
    (p.differentiableAt_aeval (x := comparisonQuotient I)).continuousAt.comp hs
  refine ⟨?_, ?_⟩
  · have hnum : ContinuousAt
        (fun z : ℂ ↦ ((comparisonQuotient z)^2 - 1) * aeval (comparisonQuotient z) y) I :=
      ((hs.pow 2).sub (continuousAt_const (y := (1 : ℂ)))).mul (hc y)
    have hden : aeval (comparisonQuotient I) (closedLoop δ x y) ≠ 0 := by
      rw [comparisonQuotient_I]
      exact he hq
    exact hnum.div (hc (closedLoop δ x y)) hden
  · rw [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    simp only [diskController, comparisonQuotient_I]
    refine ⟨div_ne_zero (mul_ne_zero (by rw [Complex.I_sq]; norm_num) (he hy)) (he hq), ?_⟩
    intro h
    have hnum := (div_eq_iff (he hq)).mp h
    have hq' : aeval I (closedLoop δ x y) =
        (I^2 - 2 * (δ : ℂ) * I + 1) * aeval I x + (I^2 - 1) * aeval I y := by
      simp [closedLoop]
    have hδ' : I^2 - 2 * (δ : ℂ) * I + 1 ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      simp [Complex.I_sq, Complex.mul_im, Complex.mul_re] at hh
      linarith
    apply (mul_ne_zero hδ' (he hx))
    linear_combination -hnum - hq'

/-- Reversing the source diameter keeps the same upper-arc point regular. -/
theorem diskController_neg_regular_at_I {δ : ℝ} (hδ : 0 < δ) {x y : ℝ[X]}
    (hx : StrictlyStable x) (hy : StrictlyStable y) (hq : StrictlyStable (closedLoop δ x y)) :
    ContinuousAt (fun z : ℂ ↦ diskController δ x y (-z)) I ∧
      diskController δ x y (-I) ∈ ({0,1}ᶜ : Set ℂ) := by
  obtain ⟨hc, hv⟩ := diskController_regular_at_I hδ hx hy hq
  have hI : (starRingEnd ℂ) I = -I := by
    apply Complex.ext <;> simp
  have hconj (z : ℂ) : diskController δ x y (-z) =
      (starRingEnd ℂ) (diskController δ x y (-(starRingEnd ℂ) z)) := by
    simpa using (diskController_conj δ x y (-(starRingEnd ℂ) z))
  have h₁ : ContinuousAt (fun z : ℂ ↦ -(starRingEnd ℂ) z) I :=
    (Complex.continuous_conj.neg).continuousAt
  have h₂ : -(starRingEnd ℂ) I = I := by rw [hI, neg_neg]
  have hm : ContinuousAt (fun z : ℂ ↦ diskController δ x y (-(starRingEnd ℂ) z)) I :=
    ContinuousAt.comp_of_eq (f := fun z : ℂ ↦ -(starRingEnd ℂ) z)
      (g := diskController δ x y) hc h₁ h₂
  have h' : ContinuousAt (fun z : ℂ ↦
      (starRingEnd ℂ) (diskController δ x y (-(starRingEnd ℂ) z))) I :=
    Complex.continuous_conj.continuousAt.comp' hm
  refine ⟨h'.congr (Filter.Eventually.of_forall fun z ↦ (hconj z).symm), ?_⟩
  intro hz
  apply hv
  rw [← hI, diskController_conj] at hz
  rcases mem_insert_iff.mp hz with h | h
  · exact mem_insert_iff.mpr (Or.inl (by simpa using congrArg (starRingEnd ℂ) h))
  · exact mem_insert_iff.mpr (Or.inr (by
      have h' := mem_singleton_iff.mp h
      exact mem_singleton_iff.mpr (by simpa using congrArg (starRingEnd ℂ) h')))

end BelgianChocolate.ControlWitness