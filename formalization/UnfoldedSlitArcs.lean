import SlitArcSquareRoot
import SlitRadialDomain

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Topology
open scoped unitInterval
open BelgianChocolate.SlitSquareRoot

noncomputable def upperBankEnd (α : ℝ) : ℂ := (Real.sqrt (1 + α) : ℂ) * Complex.I
noncomputable def lowerBankEnd (α : ℝ) : ℂ := -(Real.sqrt (1 + α) : ℂ) * Complex.I
noncomputable def rightEnd (α : ℝ) : ℂ := (Real.sqrt (1 - α) : ℂ)

private theorem upperSqrt_positive {a : ℝ} (ha : 0 ≤ a) :
    upperSqrt (a : ℂ) = (Real.sqrt a : ℂ) := by
  simp [upperSqrt, abs_of_nonneg ha, add_self_div_two]

private theorem lowerSqrt_positive {a : ℝ} (ha : 0 ≤ a) :
    lowerSqrt (a : ℂ) = (Real.sqrt a : ℂ) := by
  simp [lowerSqrt, abs_of_nonneg ha, add_self_div_two]

noncomputable def liftedUpper {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    Path (rightEnd α) (upperBankEnd α) where
  toFun t := upperSqrt (upperArc t - (α : ℂ))
  continuous_toFun := continuous_upperSqrt.comp (upperArc.continuous.sub continuous_const)
  source' := by
    rw [upperArc.source, ← Complex.ofReal_one, ← Complex.ofReal_sub, upperSqrt_positive (by linarith)]
    rfl
  target' := by
    rw [upperArc.target, show (-1 : ℂ) - (α : ℂ) = -((1 + α : ℝ) : ℂ) by push_cast; ring,
      upperSqrt_negative (by linarith)]
    rfl

noncomputable def liftedLower {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    Path (rightEnd α) (lowerBankEnd α) where
  toFun t := lowerSqrt (lowerArc t - (α : ℂ))
  continuous_toFun := continuous_lowerSqrt.comp (lowerArc.continuous.sub continuous_const)
  source' := by
    rw [lowerArc.source, ← Complex.ofReal_one, ← Complex.ofReal_sub, lowerSqrt_positive (by linarith)]
    rfl
  target' := by
    rw [lowerArc.target, show (-1 : ℂ) - (α : ℂ) = -((1 + α : ℝ) : ℂ) by push_cast; ring,
      lowerSqrt_negative (by linarith)]
    rfl

theorem liftedUpper_eq_unfolding {α : ℝ} (hl : -1 < α) (hr : α < 0) (t : I) :
    liftedUpper hl hr t = unfolding α (upperArc t) := by
  apply Eq.symm
  apply sqrt_eq_upperSqrt
  simpa using upperArc_im_nonneg t

private theorem interval_interior {t : I} (h0 : t ≠ 0) (h1 : t ≠ 1) :
    t ∈ Ioo (0 : I) 1 :=
  ⟨lt_of_le_of_ne (show (0 : I) ≤ t from t.property.1) (Ne.symm h0), lt_of_le_of_ne (unitInterval.le_one _) h1⟩

theorem liftedLower_eq_unfolding {α : ℝ} (hl : -1 < α) (hr : α < 0) {t : I} (ht : t ≠ 1) :
    liftedLower hl hr t = unfolding α (lowerArc t) := by
  by_cases h : t = 0
  · subst t
    rw [Path.source, lowerArc.source, unfolding, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      sqrt_eq_upperSqrt (by simp), upperSqrt_positive (by linarith)]
    rfl
  apply Eq.symm
  apply sqrt_eq_lowerSqrt
  simpa using lowerArc_im_neg (interval_interior h ht)

@[simp] theorem folding_liftedUpper {α : ℝ} (hl : -1 < α) (hr : α < 0) (t : I) :
    folding α (liftedUpper hl hr t) = upperArc t := by
  rw [liftedUpper_eq_unfolding, folding_unfolding]

@[simp] theorem folding_liftedLower {α : ℝ} (hl : -1 < α) (hr : α < 0) (t : I) :
    folding α (liftedLower hl hr t) = lowerArc t := by
  by_cases h : t = 1
  · subst t
    rw [(liftedLower hl hr).target, lowerArc.target]
    simp only [folding, lowerBankEnd, mul_pow, Complex.I_sq, neg_sq,
      ← Complex.ofReal_pow, Real.sq_sqrt (show 0 ≤ 1 + α by linarith)]
    push_cast
    ring
  rw [liftedLower_eq_unfolding hl hr h, folding_unfolding]

theorem liftedUpper_injective {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    Function.Injective (liftedUpper hl hr) := by
  intro s t h
  exact upperArc_injective (by simpa only [folding_liftedUpper] using congrArg (folding α) h)

theorem liftedLower_injective {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    Function.Injective (liftedLower hl hr) := by
  intro s t h
  exact lowerArc_injective (by simpa only [folding_liftedLower] using congrArg (folding α) h)

theorem bankEnds_ne {α : ℝ} (hl : -1 < α) : upperBankEnd α ≠ lowerBankEnd α := by
  intro h
  have hh := congrArg Complex.im h
  simp [upperBankEnd, lowerBankEnd] at hh
  linarith [Real.sqrt_pos.mpr (show 0 < 1 + α by linarith)]

theorem liftedUpper_lower_meet {α : ℝ} (hl : -1 < α) (hr : α < 0) {s t : I}
    (h : liftedUpper hl hr s = liftedLower hl hr t) : s = 0 ∧ t = 0 := by
  have hfold : upperArc s = lowerArc t := by
    simpa only [folding_liftedUpper, folding_liftedLower] using congrArg (folding α) h
  have hmem : upperArc s ∈ range upperArc ∩ range lowerArc :=
    ⟨mem_range_self s, ⟨t,hfold.symm⟩⟩
  rw [upper_lower_intersection] at hmem
  rcases hmem with hpos | hneg
  · exact ⟨upperArc_injective (hpos.trans upperArc.source.symm),
      lowerArc_injective (hfold.symm.trans (hpos.trans lowerArc.source.symm))⟩
  have hs : s = 1 := upperArc_injective (hneg.trans upperArc.target.symm)
  have ht : t = 1 := lowerArc_injective (hfold.symm.trans (hneg.trans lowerArc.target.symm))
  subst s; subst t
  exact (bankEnds_ne hl (by simpa only [Path.target] using h)).elim

end BelgianChocolate.SlitBoundaryGeometry
