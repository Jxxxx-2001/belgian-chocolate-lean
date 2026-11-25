import UnfoldedSlitChart

/-! Fibers of the closed chart after folding to physical coordinates.
The slit banks coalesce, while the two attachment points are distinct. -/
namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Metric Topology
open scoped unitInterval
open BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex

theorem folding_eq_iff {α : ℝ} {u v : ℂ} :
    folding α u = folding α v ↔ u = v ∨ u = -v := by
  change u ^ 2 + (α : ℂ) = v ^ 2 + (α : ℂ) ↔ _
  rw [add_left_inj]
  constructor
  · intro he
    have h : (u - v) * (u + v) = 0 := by linear_combination he
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · right; linear_combination h
  · rintro (rfl | rfl) <;> ring

theorem folding_fiber (α : ℝ) (z : ℂ) :
    (folding α) ⁻¹' {z} = {unfolding α z, -(unfolding α z)} := by
  ext u
  change folding α u = z ↔ u = unfolding α z ∨ u = -unfolding α z
  nth_rw 1 [← folding_unfolding α z]
  exact folding_eq_iff

theorem folding_upperBankEnd {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    folding α (upperBankEnd α) = -1 := by
  simpa only [(liftedUpper hl hr).target, upperArc.target] using folding_liftedUpper hl hr 1

theorem folding_lowerBankEnd {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    folding α (lowerBankEnd α) = -1 := by
  simpa only [(liftedLower hl hr).target, lowerArc.target] using folding_liftedLower hl hr 1

theorem folding_rightEnd {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    folding α (rightEnd α) = 1 := by
  simpa only [(liftedUpper hl hr).source, upperArc.source] using folding_liftedUpper hl hr 0

theorem folding_neg_one_fiber {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    folding α ⁻¹' ({-1} : Set ℂ) = {upperBankEnd α, lowerBankEnd α} := by
  ext u
  change folding α u = -1 ↔ u = upperBankEnd α ∨ u = lowerBankEnd α
  rw [← folding_upperBankEnd hl hr, folding_eq_iff]
  simp [upperBankEnd, lowerBankEnd]

theorem folding_re_of_re_zero {α : ℝ} {u : ℂ} (hu : u.re = 0) :
    (folding α u).re = α - u.im ^ 2 := by
  simp [folding, pow_two, Complex.mul_re, hu]
  ring

theorem folding_im_of_re_zero {α : ℝ} {u : ℂ} (hu : u.re = 0) :
    (folding α u).im = 0 := by simp [folding, pow_two, Complex.mul_im, hu]

theorem folding_image_bankPath {α : ℝ} (hl : -1 < α) :
    folding α '' range (bankPath α) = negativeSlit α := by
  rw [range_bankPath hl]
  apply Subset.antisymm
  · rintro _ ⟨u, ⟨hu, hbound⟩, rfl⟩
    refine ⟨folding_im_of_re_zero hu, ?_, ?_⟩ <;> rw [folding_re_of_re_zero hu]
    · have hs := Real.sq_sqrt (show 0 ≤ 1 + α by linarith)
      have he := sq_le_sq' (abs_le.mp hbound).1 (abs_le.mp hbound).2
      nlinarith
    · nlinarith [sq_nonneg u.im]
  · rintro z ⟨hz,hz₀,hz₁⟩
    let y := Real.sqrt (α - z.re)
    let u : ℂ := (y : ℂ) * Complex.I
    have hre : u.re = 0 := by simp [u]
    have him : u.im = y := by simp [u]
    have hy : y ^ 2 = α - z.re := Real.sq_sqrt (sub_nonneg.mpr hz₁)
    refine ⟨u, ⟨hre, ?_⟩, Complex.ext ?_ ?_⟩
    · rw [him, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (by linarith)
    · rw [folding_re_of_re_zero hre, him, hy]; ring
    · rw [folding_im_of_re_zero hre, hz]

theorem folding_image_liftedOuter {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    folding α '' range (liftedOuter hl hr) = frontier radialDomain := by
  rw [range_liftedOuter, image_union, ← range_comp, ← range_comp, frontier_radialDomain_eq_arcs]
  simp only [Function.comp_def, folding_liftedUpper, folding_liftedLower]

theorem folding_image_frontier {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    folding α '' frontier (unfoldedDomain α) = frontier radialDomain ∪ negativeSlit α := by
  rw [frontier_unfoldedDomain hl hr, unfoldedBoundary, image_union,
    folding_image_liftedOuter hl hr, folding_image_bankPath hl]

theorem CenteredUnfoldedChart.finite_folded_fiber {α : ℝ} {F : ℂ → ℂ}
    (h : CenteredUnfoldedChart α F) (z : ℂ) :
    (sphere (0 : ℂ) 1 ∩ (folding α ∘ F) ⁻¹' {z}).Finite := by
  apply Set.Finite.of_finite_image _ (h.frontier_bij.injOn.mono inter_subset_left)
  apply (Set.toFinite ({unfolding α z, -unfolding α z} : Set ℂ)).subset
  rintro _ ⟨w, hw, rfl⟩
  rw [← folding_fiber]
  exact hw.2

theorem CenteredUnfoldedChart.physical_boundary_image {α : ℝ} {F : ℂ → ℂ}
    (h : CenteredUnfoldedChart α F) (hl : -1 < α) (hr : α < 0) :
    (folding α ∘ F) '' sphere 0 1 = frontier radialDomain ∪ negativeSlit α := by
  change (fun z ↦ folding α (F z)) '' sphere 0 1 = _
  rw [← image_image (folding α) F, h.frontier_bij.image_eq, folding_image_frontier hl hr]

theorem upperBankEnd_mem_frontier {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    upperBankEnd α ∈ frontier (unfoldedDomain α) := by
  rw [frontier_unfoldedDomain hl hr]
  exact Or.inr ⟨0, (bankPath α).source⟩

theorem lowerBankEnd_mem_frontier {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    lowerBankEnd α ∈ frontier (unfoldedDomain α) := by
  rw [frontier_unfoldedDomain hl hr]
  exact Or.inr ⟨1, (bankPath α).target⟩

theorem rightEnd_mem_frontier {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    rightEnd α ∈ frontier (unfoldedDomain α) := by
  rw [frontier_unfoldedDomain hl hr]
  left; rw [range_liftedOuter]
  exact Or.inl ⟨0, (liftedUpper hl hr).source⟩

/-- The physical point -1 has exactly two preimages on the source circle,
and their unfolded images identify the two banks separately. -/
theorem CenteredUnfoldedChart.neg_one_prime_ends {α : ℝ} {F : ℂ → ℂ}
    (h : CenteredUnfoldedChart α F) (hl : -1 < α) (hr : α < 0) :
    ∃ P ∈ sphere (0 : ℂ) 1, ∃ Q ∈ sphere (0 : ℂ) 1, P ≠ Q ∧
      F P = upperBankEnd α ∧ F Q = lowerBankEnd α ∧
      sphere (0 : ℂ) 1 ∩ (folding α ∘ F) ⁻¹' {-1} = {P,Q} := by
  obtain ⟨P, hP, hFP⟩ := h.frontier_bij.surjOn (upperBankEnd_mem_frontier hl hr)
  obtain ⟨Q, hQ, hFQ⟩ := h.frontier_bij.surjOn (lowerBankEnd_mem_frontier hl hr)
  refine ⟨P,hP,Q,hQ,fun he ↦ bankEnds_ne hl (hFP.symm.trans ((congrArg F he).trans hFQ)), hFP,hFQ,?_⟩
  ext z
  constructor
  · rintro ⟨hz,hz'⟩
    have hfold : F z ∈ folding α ⁻¹' ({-1} : Set ℂ) := hz'
    rw [folding_neg_one_fiber hl hr] at hfold
    rcases hfold with he | he
    · left; exact h.frontier_bij.injOn hz hP (he.trans hFP.symm)
    · right; exact h.frontier_bij.injOn hz hQ (he.trans hFQ.symm)
  · rintro (rfl | rfl)
    · refine ⟨hP, ?_⟩
      change folding α (F _) = -1
      rw [hFP, folding_upperBankEnd hl hr]
    · refine ⟨hQ, ?_⟩
      change folding α (F _) = -1
      rw [hFQ, folding_lowerBankEnd hl hr]

end BelgianChocolate.SlitBoundaryGeometry
