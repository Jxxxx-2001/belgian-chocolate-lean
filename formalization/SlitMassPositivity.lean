import SlitMassChartIndependence

namespace BelgianChocolate.SlitHarmonicMeasure
open Complex Set Metric
open scoped unitInterval
open BelgianChocolate.SlitBoundaryGeometry BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex

theorem masses_strictly_positive {α : ℝ} {F : ℂ → ℂ} (h : CenteredUnfoldedChart α F)
    (hl : -1 < α) (hr : α < 0) : 0 < a α F ∧ 0 < b α F ∧ 0 < d α F := by
  have img := h.physical_boundary_image hl hr
  have H (E U : Set ℂ) (ho : IsOpen U) (hsub : (frontier radialDomain ∪ negativeSlit α) ∩ U ⊆ E)
      {z : ℂ} (hz : z ∈ frontier radialDomain ∪ negativeSlit α) (hzU : z ∈ U) : 0 < mass α F E := by
    obtain ⟨ζ,hζ,hzζ⟩ := (show z ∈ (folding α ∘ F) '' sphere 0 1 from img.symm ▸ hz)
    apply mass_pos_of_isOpen_hit h ho (fun x hx hu ↦ hsub ⟨img ▸ mem_image_of_mem _ hx,hu⟩) hζ
    change (folding α ∘ F) ζ ∈ U
    rwa [hzζ]
  have hbank : IsClosed (negativeSlit α) :=
    (isClosed_eq continuous_im continuous_const).inter
      ((isClosed_le continuous_const continuous_re).inter (isClosed_le continuous_re continuous_const))
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hmi : m ∈ Ioo (0 : I) 1 := by change (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1; norm_num
  have hnot (p : Path (1 : ℂ) (-1)) (hi : Function.Injective p) : p m ∉ ({1,-1} : Set ℂ) := by
    rintro (he | he)
    · exact hmi.1.ne' (hi (he.trans p.source.symm))
    · exact hmi.2.ne (hi (he.trans p.target.symm))
  have hupper : upperArc m ∈ frontier radialDomain := by
    rw [frontier_radialDomain_eq_arcs]; exact Or.inl (mem_range_self m)
  have hlower : lowerArc m ∈ frontier radialDomain := by
    rw [frontier_radialDomain_eq_arcs]; exact Or.inr (mem_range_self m)
  constructor
  · refine H _ (range lowerArc ∪ negativeSlit α)ᶜ
      (((isCompact_range lowerArc.continuous).isClosed.union hbank).isOpen_compl) ?_ (Or.inl hupper) ?_
    · rintro x ⟨hz,hn⟩
      rw [frontier_radialDomain_eq_arcs,range_upperArc] at hz
      rcases hz with ((he | he) | hlower') | hb
      · exact (hn (Or.inl (range_lowerArc.symm ▸ Or.inl he))).elim
      · exact he
      · exact (hn (Or.inl hlower')).elim
      · exact (hn (Or.inr hb)).elim
    · rintro (hm | hb)
      · exact hnot upperArc upperArc_injective (upper_lower_intersection ▸ ⟨mem_range_self m,hm⟩)
      · exact (upperArc_im_pos hmi).ne' hb.1
  constructor
  · have hαG : (α : ℂ) ∈ radialDomain := by
      change ‖(α : ℂ)‖ < radialRadius _
      simp [radialRadius, abs_of_neg hr]; linarith
    refine H _ radialDomain isOpen_radialDomain ?_ (Or.inr (show (α : ℂ) ∈ negativeSlit α from ⟨by simp,hl.le,le_rfl⟩)) hαG
    rintro x ⟨hf,hg⟩
    exact hf.resolve_left fun hf ↦ hf.2 (isOpen_radialDomain.interior_eq.symm ▸ hg)
  · refine H _ (range upperArc ∪ negativeSlit α)ᶜ
      (((isCompact_range upperArc.continuous).isClosed.union hbank).isOpen_compl) ?_ (Or.inl hlower) ?_
    · rintro x ⟨hz,hn⟩
      rw [frontier_radialDomain_eq_arcs,range_lowerArc] at hz
      rcases hz with (hu | (he | he)) | hb
      · exact (hn (Or.inl hu)).elim
      · exact (hn (Or.inl (range_upperArc.symm ▸ Or.inl he))).elim
      · exact he
      · exact (hn (Or.inr hb)).elim
    · rintro (hm | hb)
      · exact hnot lowerArc lowerArc_injective (upper_lower_intersection ▸ ⟨hm,mem_range_self m⟩)
      · exact (lowerArc_im_neg hmi).ne hb.1

end BelgianChocolate.SlitHarmonicMeasure

