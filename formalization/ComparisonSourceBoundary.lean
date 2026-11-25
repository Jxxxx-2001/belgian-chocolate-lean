import ComparisonOuterArc
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Complex.Convex

/-! The source half-disc has a real diameter and one open semicircle on its boundary. -/

namespace BelgianChocolate.HarmonicComparison

open Complex Metric Set

/-- The closure of the source half-disc is the closed upper half of the unit disc. -/
theorem closure_comparisonHalfDisk :
    closure comparisonHalfDisk = {z : ℂ | ‖z‖ ≤ 1 ∧ 0 ≤ z.im} := by
  apply Subset.antisymm
  · have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ 1 ∧ 0 ≤ z.im} :=
      (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im)
    apply closure_minimal ?_ hclosed
    rw [comparisonHalfDisk_eq_norm]
    exact fun _ hz => ⟨hz.1.le, hz.2.le⟩
  · intro z hz
    let p : ℂ := ((1 / 2 : ℝ) : ℂ) * Complex.I
    have hpn : ‖p‖ < 1 := by norm_num [p]
    have hpi : 0 < p.im := by norm_num [p, Complex.mul_im]
    have hseg : openSegment ℝ p z ⊆ comparisonHalfDisk := by
      rintro w ⟨a, b, ha, hb, hab, rfl⟩
      rw [comparisonHalfDisk_eq_norm]
      refine ⟨?_, ?_⟩
      · have hn : ‖a • p + b • z‖ ≤ a * ‖p‖ + b * ‖z‖ := by
          simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb] using
            norm_add_le (a • p) (b • z)
        exact hn.trans_lt (by
          have hlt := mul_lt_of_lt_one_right ha hpn
          have hle := mul_le_of_le_one_right hb.le hz.1
          linarith)
      · simp only [Complex.add_im, Complex.smul_im]
        exact add_pos_of_pos_of_nonneg (mul_pos ha hpi) (mul_nonneg hb.le hz.2)
    apply closure_mono hseg
    rw [closure_openSegment]
    exact right_mem_segment ℝ p z

/-- Boundary points are either in the open upper semicircle or in the
closed real diameter. -/
theorem frontier_comparisonHalfDisk :
    frontier comparisonHalfDisk =
      comparisonOuterArc ∪ Complex.ofReal '' Icc (-1 : ℝ) 1 := by
  rw [isOpen_comparisonHalfDisk.frontier_eq, closure_comparisonHalfDisk, comparisonHalfDisk_eq_norm]
  ext z
  constructor
  · rintro ⟨hz, hnot⟩
    rcases eq_or_lt_of_le hz.2 with hi | hi
    · right
      have hreal : ((z.re : ℝ) : ℂ) = z := by
        apply Complex.ext <;> simp [← hi]
      have hnorm : |z.re| ≤ 1 := by
        rw [← hreal] at hz
        exact (by simpa using hz.1)
      exact ⟨z.re, abs_le.mp hnorm, hreal⟩
    · left
      refine ⟨eq_of_le_of_not_lt hz.1 ?_, hi⟩
      exact fun hlt => hnot ⟨hlt, hi⟩
  · rintro (⟨hn, hi⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨⟨hn.le, hi.le⟩, fun hc => hn.not_lt hc.1⟩
    · refine ⟨⟨?_, by simp⟩, ?_⟩
      · simpa using (abs_le.mpr hx)
      · intro hc
        exact (lt_irrefl 0) (by simpa using hc.2)

/-- The three seams of the physical boundary comparison. -/
def comparisonSeams : Set ℂ := {-1, 0, 1}

theorem comparisonSeams_finite : comparisonSeams.Finite := by
  unfold comparisonSeams
  exact (finite_singleton _).insert _ |>.insert _

/-- Every frontier point outside the seams is on one of the three open arcs. -/
theorem frontier_comparisonHalfDisk_other {z : ℂ} (hz : z ∈ frontier comparisonHalfDisk)
    (hs : z ∉ comparisonSeams) :
    z ∈ comparisonOuterArc ∨
      z ∈ Complex.ofReal '' Ioo (-1 : ℝ) 0 ∨ z ∈ Complex.ofReal '' Ioo (0 : ℝ) 1 := by
  rw [frontier_comparisonHalfDisk] at hz
  rcases hz with hh | ⟨x, hx, rfl⟩
  · exact Or.inl hh
  · right
    have hne₀ : x ≠ 0 := by intro h; subst x; apply hs; simp [comparisonSeams]
    have hne₁ : x ≠ 1 := by intro h; subst x; apply hs; simp [comparisonSeams]
    have hneNeg : x ≠ -1 := by intro h; subst x; apply hs; simp [comparisonSeams]
    rcases lt_or_gt_of_ne hne₀ with hneg | hpos
    · exact Or.inl ⟨x, ⟨lt_of_le_of_ne hx.1 hneNeg.symm, hneg⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hpos, lt_of_le_of_ne hx.2 hne₁⟩, rfl⟩

end BelgianChocolate.HarmonicComparison

