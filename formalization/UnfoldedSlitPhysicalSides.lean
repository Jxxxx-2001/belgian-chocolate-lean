import UnfoldedSlitSides

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Metric Filter Topology Bornology
open scoped unitInterval
open BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex

private theorem prevertex_ne {α : ℝ} {F : ℂ → ℂ} (h : UnfoldedHalfPlaneChart α F)
    {x y : ℝ} (hne : x ≠ y) : F (x : ℂ) ≠ F (y : ℂ) := fun he ↦ hne <|
  Complex.ofReal_inj.mp (h.boundary_bij.injOn (by simp) (by simp) he)

theorem UnfoldedHalfPlaneChart.folded_three_sides {α : ℝ} {F : ℂ → ℂ} (h : UnfoldedHalfPlaneChart α F)
    (hl : -1 < α) (hr : α < 0) {q r : ℝ} (hq : F (q : ℂ) = lowerBankEnd α)
    (hR : F (r : ℂ) = rightEnd α) :
    (∀ x : ℝ, x < q → ∃ y ∈ Ioo (-1 : ℝ) 0, folding α (F (x : ℂ)) = (y : ℂ)) ∧
    (∀ x ∈ Ioo q r, ‖folding α (F (x : ℂ))‖ = 1 ∧ (folding α (F (x : ℂ))).im < 0) ∧
    (∀ x : ℝ, r < x → folding α (F (x : ℂ)) ∈ MarkedRealAxis.curvedEdge) := by
  obtain ⟨hB,hL,hU⟩ := h.trace_three_sides hl hr hq hR
  have hnP (x : ℝ) : F (x : ℂ) ≠ upperBankEnd α :=
    (h.boundary_bij.mapsTo (show (x : ℂ) ∈ {z : ℂ | z.im = 0} from by simp)).2
  constructor
  · intro x hx
    have hz : folding α (F (x : ℂ)) ∈ negativeSlit α := by
      rw [← folding_image_bankPath hl]
      exact ⟨_, hB x hx,rfl⟩
    obtain ⟨him,hleft,hright⟩ := hz
    have he : folding α (F (x : ℂ)) = ((folding α (F (x : ℂ))).re : ℂ) :=
      Complex.ext (by simp) (by simpa using him)
    refine ⟨_,⟨lt_of_le_of_ne hleft ?_, hright.trans_lt hr⟩,he⟩
    intro heq
    have hneg : F (x : ℂ) ∈ folding α ⁻¹' ({-1} : Set ℂ) := by
      change folding α (F (x : ℂ)) = -1
      exact he.trans (by rw [← heq]; norm_num)
    rw [folding_neg_one_fiber hl hr] at hneg
    rcases hneg with hneg | hneg
    · exact hnP x hneg
    · exact prevertex_ne h hx.ne (hneg.trans hq.symm)
  constructor
  · intro x hx
    obtain ⟨t,ht⟩ := hL x hx
    have ht₀ : t ≠ 0 := by
      rintro rfl
      rw [(liftedLower hl hr).source] at ht
      exact prevertex_ne h hx.2.ne (ht.symm.trans hR.symm)
    have ht₁ : t ≠ 1 := by
      rintro rfl
      rw [(liftedLower hl hr).target] at ht
      exact prevertex_ne h hx.1.ne' (ht.symm.trans hq.symm)
    rw [← ht,folding_liftedLower]
    exact ⟨norm_lowerArc t, lowerArc_im_neg ⟨lt_of_le_of_ne (show (0 : I) ≤ t from t.property.1) (Ne.symm ht₀),
      lt_of_le_of_ne (unitInterval.le_one _) ht₁⟩⟩
  · intro x hx
    obtain ⟨t,ht⟩ := hU x hx
    rw [← ht,folding_liftedUpper]
    have hm : upperArc t ∈ range upperArc := mem_range_self t
    rw [range_upperArc] at hm
    apply hm.resolve_left
    rintro (hone | hneg)
    · have h0 := upperArc_injective (hone.trans upperArc.source.symm)
      subst t; rw [(liftedUpper hl hr).source] at ht
      exact prevertex_ne h hx.ne' (ht.symm.trans hR.symm)
    · have h1 := upperArc_injective (hneg.trans upperArc.target.symm)
      subst t; rw [(liftedUpper hl hr).target] at ht
      exact hnP x ht.symm

/-- The three open sides have the fixed order used by the manuscript after applying -J. -/
theorem exists_normalized_physical_chart {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    ∃ F : ℂ → ℂ, UnfoldedHalfPlaneChart α F ∧ F (-2) = lowerBankEnd α ∧ F 2 = rightEnd α ∧
    (∀ x : ℝ, x < -2 → ∃ y ∈ Ioo (-1 : ℝ) 0, folding α (F (x : ℂ)) = (y : ℂ)) ∧
    (∀ x ∈ Ioo (-2 : ℝ) 2, ‖folding α (F (x : ℂ))‖ = 1 ∧ (folding α (F (x : ℂ))).im < 0) ∧
    (∀ x : ℝ, 2 < x → folding α (F (x : ℂ)) ∈ MarkedRealAxis.curvedEdge) := by
  obtain ⟨F,hF,hq,hr'⟩ := exists_normalized_unfoldedHalfPlaneChart hl hr
  refine ⟨F,hF,hq,hr',?_⟩
  exact hF.folded_three_sides hl hr (q := -2) (r := 2) (by simpa using hq) (by simpa using hr')

end BelgianChocolate.SlitBoundaryGeometry
