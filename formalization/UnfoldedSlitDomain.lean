import UnfoldedSlitJordan

/-! The right-half-plane quadratic preimage is exactly the inside of the
three-arc Jordan curve, including its two distinct lifts of the physical point -1. -/
namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Metric Topology
open scoped unitInterval
open BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex

def unfoldedDomain (α : ℝ) : Set ℂ := {u | 0 < u.re ∧ folding α u ∈ radialDomain}

theorem unfolding_image_candidateSlit (α : ℝ) :
    unfolding α '' candidateSlit α = unfoldedDomain α := by
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨unfolding_re_pos_on_finiteSlit radialDomain_subset_ball hz,
      (folding_unfolding α z).symm ▸ hz.1⟩
  · rintro u ⟨hu,hz⟩
    refine ⟨folding α u, ⟨hz, ?_⟩, unfolding_folding_of_re_pos hu⟩
    intro h
    exact folding_not_mem_negativeRay hu ⟨h.1, h.2.2⟩

theorem unfoldedDomain_isOpen (α : ℝ) : IsOpen (unfoldedDomain α) :=
  (isOpen_lt (continuous_const (y := (0 : ℝ))) continuous_re).inter
    (isOpen_radialDomain.preimage (differentiable_folding α).continuous)

theorem unfolding_zero_mem {α : ℝ} (hr : α < 0) : unfolding α 0 ∈ unfoldedDomain α := by
  rw [← unfolding_image_candidateSlit]
  refine ⟨0, ⟨zero_mem_radialDomain, ?_⟩, rfl⟩
  intro h
  exact hr.not_ge (by simpa using h.2.2)

theorem unfoldedDomain_isBounded {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    Bornology.IsBounded (unfoldedDomain α) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2, fun u hu ↦ ?_⟩
  have h := mem_ball_zero_iff.mp (radialDomain_subset_ball hu.2)
  have hsq : u ^ 2 = folding α u - (α : ℂ) := by simp [folding]
  have hb := norm_sub_le (folding α u) (α : ℂ)
  rw [← hsq, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hr] at hb
  nlinarith [norm_nonneg u]

theorem frontier_radialDomain_eq_arcs :
    frontier radialDomain = range upperArc ∪ range lowerArc := by
  rw [frontier_radialDomain, range_upperArc, range_lowerArc]
  ext
  simp only [mem_union]
  tauto

theorem folded_mem_frontier_of_mem_liftedOuter {α : ℝ} (hl : -1 < α) (hr : α < 0) {u : ℂ}
    (hu : u ∈ range (liftedOuter hl hr)) : folding α u ∈ frontier radialDomain := by
  rw [range_liftedOuter] at hu
  rw [frontier_radialDomain_eq_arcs]
  rcases hu with ⟨t,rfl⟩ | ⟨t,rfl⟩
  · rw [folding_liftedUpper]; exact Or.inl (mem_range_self t)
  · rw [folding_liftedLower]; exact Or.inr (mem_range_self t)

theorem disjoint_unfoldedDomain_boundary {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    Disjoint (unfoldedDomain α) (unfoldedBoundary hl hr) := by
  rw [disjoint_left]
  intro u hu hb
  rcases hb with ho | hb
  · have hf := folded_mem_frontier_of_mem_liftedOuter hl hr ho
    exact hf.2 (isOpen_radialDomain.interior_eq.symm ▸ hu.2)
  rw [range_bankPath hl] at hb
  exact hu.1.ne' hb.1

theorem frontier_unfoldedDomain_subset {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    frontier (unfoldedDomain α) ⊆ unfoldedBoundary hl hr := by
  intro u hu
  have hre : 0 ≤ u.re := closure_minimal
    (show unfoldedDomain α ⊆ {v : ℂ | 0 ≤ v.re} from fun _ hv ↦ hv.1.le)
    (isClosed_le continuous_const continuous_re) hu.1
  have hfold : folding α u ∈ closure radialDomain :=
    (differentiable_folding α).continuous.closure_preimage_subset radialDomain
      (closure_mono (show unfoldedDomain α ⊆ folding α ⁻¹' radialDomain from fun _ hv ↦ hv.2) hu.1)
  rcases hre.eq_or_lt with h0 | hp
  · right
    rw [range_bankPath hl]
    refine ⟨h0.symm, ?_⟩
    have hclosed : closure radialDomain ⊆ closedBall (0 : ℂ) 1 :=
      closure_minimal (radialDomain_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
    have hb := (Complex.abs_re_le_norm (folding α u)).trans
      (mem_closedBall_zero_iff.mp (hclosed hfold))
    have hlow := (abs_le.mp hb).1
    simp [folding, pow_two, Complex.mul_re, h0.symm] at hlow
    have hs := Real.sq_sqrt (show 0 ≤ 1 + α by linarith)
    have ha := sq_abs u.im
    nlinarith [abs_nonneg u.im, Real.sqrt_nonneg (1 + α)]
  · left
    rw [range_liftedOuter]
    have hfr : folding α u ∈ frontier radialDomain :=
      ⟨hfold, fun hi ↦ hu.2 ((unfoldedDomain_isOpen α).interior_eq.symm ▸
        ⟨hp, (isOpen_radialDomain.interior_eq ▸ hi)⟩)⟩
    rw [frontier_radialDomain_eq_arcs] at hfr
    rcases hfr with ⟨t,he⟩ | ⟨t,he⟩
    · left
      refine ⟨t, ?_⟩
      rw [liftedUpper_eq_unfolding, he, unfolding_folding_of_re_pos hp]
    · right
      have ht : t ≠ 1 := by
        rintro rfl
        rw [lowerArc.target] at he
        apply folding_not_mem_negativeRay hp
        rw [← he]
        exact ⟨by simp, by simpa using hl.le⟩
      refine ⟨t, ?_⟩
      rw [liftedLower_eq_unfolding hl hr ht, he, unfolding_folding_of_re_pos hp]

/-- A bounded nonempty open set missing a Jordan curve and having its frontier
contained in that curve is precisely its inside. -/
theorem eq_jordan_inside_of_frontier_subset {U C : Set ℂ} (hJ : TauCeti.IsJordanCurve C)
    (ho : IsOpen U) (hb : Bornology.IsBounded U) (hn : U.Nonempty)
    (hd : Disjoint U C) (hf : frontier U ⊆ C) : U = TauCeti.filledHull C \ C := by
  have hsub : U ⊆ TauCeti.filledHull C \ C := fun _ h ↦
    ⟨TauCeti.subset_filledHull_of_frontier_subset hb hf h, disjoint_left.mp hd h⟩
  apply Subset.antisymm hsub
  let V := TauCeti.filledHull C \ C
  let _ : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp
    hJ.isConnected_filledHull_sdiff.isPreconnected
  have hc : IsClopen ((Subtype.val : V → ℂ) ⁻¹' U) :=
    isClopen_preimage_val ho (disjoint_left.mpr fun _ hx hy ↦ hy.2 (hf hx))
  obtain ⟨x,hx⟩ := hn
  have he := hc.eq_univ ⟨⟨x,hsub hx⟩,hx⟩
  intro y hy
  exact (show (⟨y,hy⟩ : V) ∈ (Subtype.val : V → ℂ) ⁻¹' U by rw [he]; trivial)

theorem unfoldedDomain_eq_inside {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    unfoldedDomain α = TauCeti.filledHull (unfoldedBoundary hl hr) \ unfoldedBoundary hl hr :=
  eq_jordan_inside_of_frontier_subset (unfoldedBoundary_isJordanCurve hl hr)
    (unfoldedDomain_isOpen α) (unfoldedDomain_isBounded hl hr) ⟨_, unfolding_zero_mem hr⟩
    (disjoint_unfoldedDomain_boundary hl hr) (frontier_unfoldedDomain_subset hl hr)

theorem frontier_unfoldedDomain {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    frontier (unfoldedDomain α) = unfoldedBoundary hl hr := by
  rw [unfoldedDomain_eq_inside hl hr, (unfoldedBoundary_isJordanCurve hl hr).frontier_filledHull_sdiff]

theorem unfoldedDomain_isJordanDomain {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    TauCeti.IsJordanDomain (unfoldedDomain α) := by
  rw [unfoldedDomain_eq_inside hl hr]
  exact (unfoldedBoundary_isJordanCurve hl hr).isJordanDomain_filledHull_sdiff

end BelgianChocolate.SlitBoundaryGeometry
