import UnfoldedSlitMarking

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Filter Topology Bornology

private noncomputable def affine (a b : ℝ) (z : ℂ) : ℂ := (a : ℂ)*z+(b : ℂ)

private theorem affine_im (a b : ℝ) (z : ℂ) : (affine a b z).im = a * z.im := by
  simp [affine, Complex.mul_im]

private theorem affine_bijOn {a b : ℝ} (ha : 0 < a) {S : Set ℂ}
    (hS : ∀ z : ℂ, affine a b z ∈ S ↔ z ∈ S) : BijOn (affine a b) S S := by
  have hne := Complex.ofReal_ne_zero.mpr ha.ne'
  refine ⟨fun z hz ↦ (hS z).mpr hz, fun x _ y _ h ↦ mul_left_cancel₀ hne (add_right_cancel h), ?_⟩
  intro z hz
  let w : ℂ := (z - b) / a
  have he : affine a b w = z := by dsimp [affine,w]; field_simp; ring
  exact ⟨w,(hS w).mp (he.symm ▸ hz),he⟩

theorem UnfoldedHalfPlaneChart.precomp_affine {α a b : ℝ} {F : ℂ → ℂ}
    (h : UnfoldedHalfPlaneChart α F) (ha : 0 < a) :
    UnfoldedHalfPlaneChart α (fun z ↦ F ((a : ℂ) * z + b)) := by
  have h0 := affine_bijOn (b := b) ha (S := {z : ℂ | z.im = 0}) (fun z ↦ by
    change (affine a b z).im = 0 ↔ z.im = 0
    rw [affine_im, mul_eq_zero, or_iff_right ha.ne'])
  have hle := affine_bijOn (b := b) ha (S := {z : ℂ | 0 ≤ z.im}) (fun z ↦ by
    change 0 ≤ (affine a b z).im ↔ 0 ≤ z.im
    rw [affine_im, mul_nonneg_iff_of_pos_left ha])
  have hlt := affine_bijOn (b := b) ha (S := UpperHalfPlane.upperHalfPlaneSet) (fun z ↦ by
    change 0 < (affine a b z).im ↔ 0 < z.im
    rw [affine_im, mul_pos_iff_of_pos_left ha])
  have hc : Continuous (affine a b) := by unfold affine; fun_prop
  have hd : Differentiable ℂ (affine a b) := by unfold affine; fun_prop
  refine ⟨h.cont.comp hc.continuousOn hle.mapsTo, h.holo.comp hd.differentiableOn hlt.mapsTo,
    h.interior_bij.comp hlt,h.closed_bij.comp hle,h.boundary_bij.comp h0,?_⟩
  apply h.at_infty.comp
  refine tendsto_inf.mpr ⟨?_, ?_⟩
  · exact ((tendsto_add_const_cobounded (b : ℂ)).comp
      (tendsto_mul_left_cobounded (Complex.ofReal_ne_zero.mpr ha.ne'))).mono_left inf_le_left
  · exact tendsto_principal.mpr (Filter.mem_of_superset
      (Filter.mem_inf_of_right (Filter.mem_principal_self _)) hle.mapsTo)

theorem exists_normalized_unfoldedHalfPlaneChart {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    ∃ F : ℂ → ℂ, UnfoldedHalfPlaneChart α F ∧ F (-2) = lowerBankEnd α ∧ F 2 = rightEnd α := by
  obtain ⟨F,hF⟩ := exists_unfoldedHalfPlaneChart hl hr
  obtain ⟨q,hq⟩ := hF.real_prevertex (lowerBankEnd_mem_frontier hl hr) (bankEnds_ne hl).symm
  have hRP : rightEnd α ≠ upperBankEnd α := by
    intro h
    have hh := congrArg Complex.re h
    simp [rightEnd, upperBankEnd] at hh
    linarith [Real.sqrt_pos.mpr (show 0 < 1 - α by linarith)]
  obtain ⟨r,hr'⟩ := hF.real_prevertex (rightEnd_mem_frontier hl hr) hRP
  have hqr := hF.prevertex_order hl hr hq hr'
  let a := (r-q)/4
  let b := (r+q)/2
  have ha : 0 < a := by dsimp [a]; linarith
  refine ⟨fun z ↦ F ((a : ℂ)*z + b), hF.precomp_affine ha, ?_, ?_⟩
  · convert hq using 2
    dsimp [a,b]; push_cast; ring
  · convert hr' using 2
    dsimp [a,b]; push_cast; ring

end BelgianChocolate.SlitBoundaryGeometry
