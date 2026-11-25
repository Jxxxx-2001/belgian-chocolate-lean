import SourceDiskCompetitor
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Normalize the real source coordinate so that the simple derivative at zero is positive. -/

namespace BelgianChocolate.SourceDiskPaths

open Complex Metric Set Filter
open scoped ComplexConjugate Topology

/-- The manuscript's conjugation condition on the unscaled unit disk. -/
def RealSymmetricOnDisk (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ ball (0 : ℂ) 1, f (conj z) = conj (f z)

theorem source_deriv_zero_real {f : ℂ → ℂ} {d : ℂ} (hreal : RealSymmetricOnDisk f)
    (hd : HasDerivAt f d 0) : d.im = 0 := by
  have hconj : HasDerivAt (conj ∘ f ∘ conj) (conj d) 0 := by
    simpa only [map_zero] using hd.conj_conj
  have heq : f =ᶠ[𝓝 (0 : ℂ)] (conj ∘ f ∘ conj) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    change f z = conj (f (conj z))
    rw [hreal z hz, conj_conj]
  have h := congrArg Complex.im ((hconj.congr_of_eventuallyEq heq).unique hd)
  rw [Complex.conj_im] at h
  linarith

theorem neg_mapsTo_sourceDisk (t : ℝ) :
    MapsTo (fun z : ℂ => -z) (sourceDisk t) (sourceDisk t) := by
  rintro z ⟨hn, hzero, hplus, hminus⟩
  refine ⟨by simpa only [norm_neg] using hn, neg_ne_zero.mpr hzero, ?_, ?_⟩
  · intro h
    apply hminus
    simpa only [neg_neg, neg_mul] using congrArg Neg.neg h
  · intro h
    apply hplus
    simpa only [neg_neg, neg_mul] using congrArg Neg.neg h

private theorem hasDerivAt_sourceNeg (z : ℂ) :
    HasDerivAt (fun w : ℂ => -w) (-1) z := by
  simpa only [id_eq, neg_one_mul] using (hasDerivAt_id z).const_mul (-1 : ℂ)

theorem hasDerivAt_neg_source {f : ℂ → ℂ} {d z : ℂ} (hd : HasDerivAt f d (-z)) :
    HasDerivAt (fun w => f (-w)) (-d) z := by
  simpa only [Function.comp_def, mul_neg, mul_one] using
    HasDerivAt.comp z hd (hasDerivAt_sourceNeg z)

theorem markedCompetitor_neg_source {t : ℝ} {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    MarkedCompetitor t (fun z => f (-z)) where
  holomorphic := by
    refine hf.holomorphic.comp (fun z _ =>
      (hasDerivAt_sourceNeg z).differentiableAt.differentiableWithinAt) ?_
    intro z hz
    exact mem_ball_zero_iff.mpr (by simpa only [norm_neg] using mem_ball_zero_iff.mp hz)
  avoids := hf.avoids.comp (neg_mapsTo_sourceDisk t)
  zero_value := by simpa only [neg_zero] using hf.zero_value
  plus_value := by simpa only [neg_mul] using hf.minus_value
  minus_value := by simpa only [neg_mul, neg_neg] using hf.plus_value
  zero_simple := by
    obtain ⟨d, hd, hne⟩ := hf.zero_simple
    exact ⟨-d, hasDerivAt_neg_source (by simpa only [neg_zero] using hd), neg_ne_zero.mpr hne⟩
  plus_simple := by
    obtain ⟨d, hd, hne⟩ := hf.minus_simple
    exact ⟨-d, hasDerivAt_neg_source (by simpa only [neg_mul] using hd), neg_ne_zero.mpr hne⟩
  minus_simple := by
    obtain ⟨d, hd, hne⟩ := hf.plus_simple
    exact ⟨-d, hasDerivAt_neg_source (by simpa only [neg_mul, neg_neg] using hd), neg_ne_zero.mpr hne⟩

theorem realSymmetric_neg_source {f : ℂ → ℂ} (hreal : RealSymmetricOnDisk f) :
    RealSymmetricOnDisk (fun z => f (-z)) := by
  intro z hz
  have hnz : -z ∈ ball (0 : ℂ) 1 :=
    mem_ball_zero_iff.mpr (by simpa only [norm_neg] using mem_ball_zero_iff.mp hz)
  simpa only [map_neg] using hreal (-z) hnz

/-- Reversing the source coordinate if necessary supplies the positive
derivative convention and preserves the original real-symmetric competitor class. -/
theorem exists_positive_source_derivative {t : ℝ} {f : ℂ → ℂ}
    (hf : MarkedCompetitor t f) (hreal : RealSymmetricOnDisk f) :
    ∃ (g : ℂ → ℂ) (d : ℂ),
      (g = f ∨ g = fun z => f (-z)) ∧ MarkedCompetitor t g ∧ RealSymmetricOnDisk g ∧
        HasDerivAt g d 0 ∧ d.im = 0 ∧ 0 < d.re := by
  obtain ⟨d, hd, hne⟩ := hf.zero_simple
  have him := source_deriv_zero_real hreal hd
  have hre : d.re ≠ 0 := by
    intro hr
    exact hne (Complex.ext (hr.trans Complex.zero_re.symm) (him.trans Complex.zero_im.symm))
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · have hd' : HasDerivAt (fun z => f (-z)) (-d) 0 :=
      hasDerivAt_neg_source (by simpa only [neg_zero] using hd)
    exact ⟨_, -d, Or.inr rfl, markedCompetitor_neg_source hf, realSymmetric_neg_source hreal, hd',
      by rw [Complex.neg_im, him, neg_zero], by rw [Complex.neg_re]; exact neg_pos.mpr hneg⟩
  · exact ⟨f, d, Or.inl rfl, hf, hreal, hd, him, hpos⟩

end BelgianChocolate.SourceDiskPaths

