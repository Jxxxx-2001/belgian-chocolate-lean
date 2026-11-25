import UnfoldedSlitNormalization

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Filter Topology Bornology
open scoped unitInterval
open BelgianChocolate.SlitSquareRoot

theorem UnfoldedHalfPlaneChart.trace_top {α : ℝ} {F : ℂ → ℂ} (h : UnfoldedHalfPlaneChart α F) :
    Tendsto (fun t : ℝ ↦ F (t : ℂ)) atTop (𝓝 (upperBankEnd α)) :=
  h.at_infty.comp (tendsto_inf.mpr ⟨RCLike.tendsto_ofReal_atTop_cobounded ℂ,
    tendsto_principal.mpr (Eventually.of_forall fun _ ↦ by simp)⟩)

private theorem liftedUpper_lower_inter_subset {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    range (liftedUpper hl hr) ∩ range (liftedLower hl hr) ⊆ {rightEnd α} := by
  rintro _ ⟨⟨s,rfl⟩,⟨t,he⟩⟩
  obtain ⟨rfl, _⟩ := liftedUpper_lower_meet hl hr he.symm
  exact (liftedUpper hl hr).source

private theorem pos_trace_outer {α : ℝ} {F : ℂ → ℂ} (h : UnfoldedHalfPlaneChart α F)
    (hl : -1 < α) (hr : α < 0) {q r : ℝ} (hq : F (q : ℂ) = lowerBankEnd α)
    (hR : F (r : ℂ) = rightEnd α) {x : ℝ} (hx : q ≤ x) :
    F (x : ℂ) ∈ range (liftedOuter hl hr) := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [hq]; exact ⟨1,(liftedOuter hl hr).target⟩
  have hro : F (r : ℂ) ∈ range (liftedOuter hl hr) := by
    rw [hR,range_liftedOuter]; exact Or.inl ⟨0,(liftedUpper hl hr).source⟩
  have hf := (h.boundary_bij.mapsTo (show (x : ℂ) ∈ {z : ℂ | z.im = 0} from by simp)).1
  rw [frontier_unfoldedDomain hl hr] at hf
  exact hf.resolve_right fun hb ↦ h.no_cross hl hr hq isPreconnected_Ioi (by simp)
    (h.prevertex_order hl hr hq hR) hx hro hb

private theorem no_cross_outer_arcs {α : ℝ} {F : ℂ → ℂ} (h : UnfoldedHalfPlaneChart α F)
    (hl : -1 < α) (hr : α < 0) {q r : ℝ} (hq : F (q : ℂ) = lowerBankEnd α)
    (hR : F (r : ℂ) = rightEnd α) {S : Set ℝ} (hs : IsPreconnected S)
    (hqs : S ⊆ Ici q) (hrs : r ∉ S) {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (ha' : F (a : ℂ) ∈ range (liftedUpper hl hr)) (hb' : F (b : ℂ) ∈ range (liftedLower hl hr)) :
    False := by
  let f : ℝ → ℂ := fun t ↦ F (t : ℂ)
  have hc : Continuous f := h.cont.comp_continuous continuous_ofReal (fun _ ↦ by simp)
  have him := hs.image f hc.continuousOn
  have hu := (isCompact_range (liftedUpper hl hr).continuous).isClosed
  have hd := (isCompact_range (liftedLower hl hr).continuous).isClosed
  have hsub : f '' S ⊆ range (liftedUpper hl hr) ∪ range (liftedLower hl hr) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [← range_liftedOuter]
    exact pos_trace_outer h hl hr hq hR (hqs hx)
  obtain ⟨_,⟨t,ht,rfl⟩,hw⟩ := isPreconnected_closed_iff.mp him _ _ hu hd hsub
    ⟨_,⟨a,ha,rfl⟩,ha'⟩ ⟨_,⟨b,hb,rfl⟩,hb'⟩
  have he : F (t : ℂ) = rightEnd α := liftedUpper_lower_inter_subset hl hr hw
  have htr : (t : ℂ) = (r : ℂ) := h.boundary_bij.injOn (by simp) (by simp) (he.trans hR.symm)
  exact hrs (Complex.ofReal_inj.mp htr ▸ ht)

theorem UnfoldedHalfPlaneChart.trace_three_sides {α : ℝ} {F : ℂ → ℂ} (h : UnfoldedHalfPlaneChart α F)
    (hl : -1 < α) (hr : α < 0) {q r : ℝ} (hq : F (q : ℂ) = lowerBankEnd α)
    (hR : F (r : ℂ) = rightEnd α) :
    (∀ x : ℝ, x < q → F (x : ℂ) ∈ range (bankPath α)) ∧
    (∀ x ∈ Ioo q r, F (x : ℂ) ∈ range (liftedLower hl hr)) ∧
    (∀ x : ℝ, r < x → F (x : ℂ) ∈ range (liftedUpper hl hr)) := by
  have hqr := h.prevertex_order hl hr hq hR
  have hpos : 0 < Real.sqrt (1 + α) := Real.sqrt_pos.mpr (by linarith)
  have hPb : upperBankEnd α ≠ 0 := by simp [upperBankEnd,hpos.ne']
  have hQb : lowerBankEnd α ≠ 0 := by simp [lowerBankEnd,hpos.ne']
  have hzbank : (0 : ℂ) ∈ range (bankPath α) := by rw [range_bankPath hl]; simp
  have hz : (0 : ℂ) ∈ frontier (unfoldedDomain α) := by
    rw [frontier_unfoldedDomain hl hr]; exact Or.inr hzbank
  obtain ⟨m,hm⟩ := h.real_prevertex hz hPb.symm
  have hmB : F (m : ℂ) ∈ range (bankPath α) := hm ▸ hzbank
  have hmq : m < q := by
    by_contra! hm'
    have ho := pos_trace_outer h hl hr hq hR hm'
    have hi : F (m : ℂ) ∈ range (liftedOuter hl hr) ∩ range (bankPath α) := ⟨ho,hmB⟩
    rw [liftedOuter_bankPath_inter,hm] at hi
    rcases hi with hi | hi
    · exact hPb hi.symm
    · exact hQb (Eq.symm hi)
  constructor
  · intro x hx
    have hf := (h.boundary_bij.mapsTo (show (x : ℂ) ∈ {z : ℂ | z.im = 0} from by simp)).1
    rw [frontier_unfoldedDomain hl hr] at hf
    exact hf.resolve_left fun ho ↦ h.no_cross hl hr hq isPreconnected_Iio (by simp) hx hmq ho hmB
  constructor
  · intro x hx
    have hx' := pos_trace_outer h hl hr hq hR hx.1.le
    rw [range_liftedOuter] at hx'
    apply hx'.resolve_left
    intro hu
    apply no_cross_outer_arcs h hl hr hq hR isPreconnected_Ico
      (Ico_subset_Ici_self : Ico q r ⊆ Ici q) (by simp) ⟨hx.1.le,hx.2⟩ ⟨le_rfl,hqr⟩ hu
    rw [hq]; exact ⟨1,(liftedLower hl hr).target⟩
  · intro x hx
    have hP : upperBankEnd α ∉ range (liftedLower hl hr) := by
      rintro ⟨t,ht⟩
      have hh := liftedUpper_lower_meet hl hr ((liftedUpper hl hr).target.trans ht.symm)
      exact one_ne_zero hh.1
    have htail := h.trace_top.eventually
      ((isCompact_range (liftedLower hl hr).continuous).isClosed.isOpen_compl.mem_nhds hP)
    obtain ⟨y,hy,hyb⟩ := (htail.and (eventually_gt_atTop r)).exists
    have hy' := pos_trace_outer h hl hr hq hR (hqr.trans hyb).le
    rw [range_liftedOuter] at hy'
    have hupper := hy'.resolve_right hy
    have hx' := pos_trace_outer h hl hr hq hR (hqr.trans hx).le
    rw [range_liftedOuter] at hx'
    exact hx'.resolve_right fun hlo ↦ no_cross_outer_arcs h hl hr hq hR isPreconnected_Ioi
      (show Ioi r ⊆ Ici q from fun _ hh ↦ hqr.le.trans hh.le) (by simp) hyb hx hupper hlo

end BelgianChocolate.SlitBoundaryGeometry
