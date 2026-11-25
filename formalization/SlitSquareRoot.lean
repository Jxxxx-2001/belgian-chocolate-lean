import SlitStarConvex
import TauCeti.Analysis.Complex.Sqrt
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Tactic

/-! The concrete square-root unfolding of a negative slit. Boundary prime-end
identifications and the Jordan property of an unfolded candidate remain separate. -/
namespace BelgianChocolate.SlitSquareRoot
open Complex Set Topology
open BelgianChocolate.SlitStarConvex

noncomputable def unfolding (α : ℝ) (z : ℂ) : ℂ := Complex.sqrt (z - (α : ℂ))
noncomputable def folding (α : ℝ) (u : ℂ) : ℂ := u ^ 2 + (α : ℂ)

theorem sub_mem_slitPlane_iff (α : ℝ) (z : ℂ) :
    z - (α : ℂ) ∈ Complex.slitPlane ↔ z ∉ negativeRay α := by
  change (0 < (z - (α : ℂ)).re ∨ (z - (α : ℂ)).im ≠ 0) ↔
    ¬(z.im = 0 ∧ z.re ≤ α)
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, sub_pos, not_and_or, not_le]
  tauto

/-- The slit is unfolded into the open right half-plane, including all
nonreal points and the real interval to the right of its tip. -/
theorem unfolding_re_pos {α : ℝ} {z : ℂ} (hz : z ∉ negativeRay α) :
    0 < (unfolding α z).re :=
  (Complex.sqrt_re_pos_iff _).mpr ((sub_mem_slitPlane_iff α z).mpr hz)

@[simp] theorem folding_unfolding (α : ℝ) (z : ℂ) : folding α (unfolding α z) = z := by
  simp [folding, unfolding, Complex.sq_sqrt]

/-- Squaring is a left inverse of the chosen root, so unfolding is injective. -/
theorem unfolding_injective (α : ℝ) : Function.Injective (unfolding α) := by
  intro z w h
  have hh := congrArg (folding α) h
  simpa only [folding_unfolding] using hh

/-- The inverse polynomial is injective on the open right half-plane. -/
theorem folding_injOn_rightHalfPlane (α : ℝ) : InjOn (folding α) {u : ℂ | 0 < u.re} := by
  intro u hu v hv h
  change 0 < u.re at hu
  change 0 < v.re at hv
  have hs : u ^ 2 = v ^ 2 := add_right_cancel h
  have hf : (u - v) * (u + v) = 0 := by
    calc
      _ = u ^ 2 - v ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hs
  rcases mul_eq_zero.mp hf with hminus | hplus
  · exact sub_eq_zero.mp hminus
  · have hr := congrArg Complex.re hplus
    simp only [Complex.add_re, Complex.zero_re] at hr
    linarith

/-- The principal branch is the inverse of squaring throughout that half-plane. -/
@[simp] theorem unfolding_folding_of_re_pos {α : ℝ} {u : ℂ} (hu : 0 < u.re) :
    unfolding α (folding α u) = u := by
  have hs : (unfolding α (folding α u)) ^ 2 = u ^ 2 := by
    simp [unfolding, folding, Complex.sq_sqrt]
  have hf : (unfolding α (folding α u) - u) *
      (unfolding α (folding α u) + u) = 0 := by
    calc
      _ = (unfolding α (folding α u)) ^ 2 - u ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hs
  rcases mul_eq_zero.mp hf with hminus | hplus
  · exact sub_eq_zero.mp hminus
  · have hr := congrArg Complex.re hplus
    simp only [Complex.add_re, Complex.zero_re] at hr
    have hnonneg : 0 ≤ (unfolding α (folding α u)).re := Complex.sqrt_re_nonneg _
    linarith

theorem folding_not_mem_negativeRay {α : ℝ} {u : ℂ} (hu : 0 < u.re) :
    folding α u ∉ negativeRay α := by
  apply (sub_mem_slitPlane_iff α _).mp
  apply (Complex.sqrt_re_pos_iff _).mp
  change 0 < (unfolding α (folding α u)).re
  rw [unfolding_folding_of_re_pos hu]
  exact hu

/-- Unfolding is holomorphic on the precise slit complement. -/
theorem differentiableOn_unfolding (α : ℝ) :
    DifferentiableOn ℂ (unfolding α) (negativeRay α)ᶜ := by
  apply Complex.differentiableOn_sqrt.comp (differentiableOn_id.sub_const (α : ℂ))
  intro z hz
  exact (sub_mem_slitPlane_iff α z).mpr hz

/-- The inverse polynomial is entire. -/
theorem differentiable_folding (α : ℝ) : Differentiable ℂ (folding α) := by
  unfold folding
  fun_prop

/-- This is a homeomorphism of the actual open domains, not an assertion that
the two physical shores of the slit have the same boundary extension. -/
noncomputable def unfoldingHomeomorph (α : ℝ) :
    ↥((negativeRay α)ᶜ) ≃ₜ {u : ℂ | 0 < u.re} where
  toFun z := ⟨unfolding α z, unfolding_re_pos z.property⟩
  invFun u := ⟨folding α u, folding_not_mem_negativeRay u.property⟩
  left_inv z := Subtype.ext (folding_unfolding α z)
  right_inv u := Subtype.ext (unfolding_folding_of_re_pos u.property)
  continuous_toFun := Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp (differentiableOn_unfolding α).continuousOn) _
  continuous_invFun := Continuous.subtype_mk
    ((differentiable_folding α).continuous.comp continuous_subtype_val) _

/-- In a candidate subdomain of the unit disc, the finite slit uses this same
analytic branch and has strictly positive unfolded real part. -/
theorem unfolding_re_pos_on_finiteSlit {G : Set ℂ} {α : ℝ} (hG : G ⊆ Metric.ball 0 1)
    {z : ℂ} (hz : z ∈ G \ negativeSlit α) : 0 < (unfolding α z).re := by
  rw [remove_negativeSlit_eq_remove_negativeRay hG] at hz
  exact unfolding_re_pos hz.2

#print axioms unfoldingHomeomorph
#print axioms unfolding_re_pos_on_finiteSlit
end BelgianChocolate.SlitSquareRoot
