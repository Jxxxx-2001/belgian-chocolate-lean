import UnfoldedSlitArcs
import TauCeti.Analysis.Complex.Conformal.Jordan.Domain

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Topology
open scoped unitInterval
open BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex

theorem upperArc_im_pos {u : I} (hu : u ∈ Ioo (0 : I) 1) : 0 < (upperArc u).im := by
  have h0 : 0 < (u : ℝ) := hu.1
  have h1 : (u : ℝ) < 1 := hu.2
  have hs := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0)
    (show Real.pi * (u : ℝ) < Real.pi by nlinarith [Real.pi_pos])
  change 0 < (upperPoint (Real.pi * (u : ℝ))).im
  simpa [upperPoint, Complex.mul_im, Complex.exp_mul_I, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_sin] using
    mul_pos (Real.exp_pos (-Real.sqrt ((Real.pi * (u : ℝ)) * (Real.pi - Real.pi * (u : ℝ))))) hs

theorem liftedUpper_re_pos {α : ℝ} (hl : -1 < α) (hr : α < 0) {t : I} (ht : t ≠ 1) :
    0 < (liftedUpper hl hr t).re := by
  by_cases h : t = 0
  · subst t
    rw [(liftedUpper hl hr).source]
    exact Real.sqrt_pos.mpr (by linarith)
  rw [liftedUpper_eq_unfolding]
  apply unfolding_re_pos
  intro hh
  exact (upperArc_im_pos ⟨lt_of_le_of_ne (show (0 : I) ≤ t from t.property.1) (Ne.symm h),
    lt_of_le_of_ne (unitInterval.le_one _) ht⟩).ne' hh.1

theorem liftedLower_re_pos {α : ℝ} (hl : -1 < α) (hr : α < 0) {t : I} (ht : t ≠ 1) :
    0 < (liftedLower hl hr t).re := by
  by_cases h : t = 0
  · subst t
    rw [(liftedLower hl hr).source]
    exact Real.sqrt_pos.mpr (by linarith)
  rw [liftedLower_eq_unfolding hl hr ht]
  apply unfolding_re_pos
  intro hh
  exact (lowerArc_im_neg ⟨lt_of_le_of_ne (show (0 : I) ≤ t from t.property.1) (Ne.symm h),
    lt_of_le_of_ne (unitInterval.le_one _) ht⟩).ne hh.1

noncomputable def liftedOuter {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    Path (upperBankEnd α) (lowerBankEnd α) :=
  (liftedUpper hl hr).symm.trans (liftedLower hl hr)

theorem range_liftedOuter {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    range (liftedOuter hl hr) = range (liftedUpper hl hr) ∪ range (liftedLower hl hr) := by
  rw [liftedOuter, Path.trans_range, Path.symm_range]

private theorem injective_two_arcs {X : Type*} [TopologicalSpace X] {x y z : X}
    {p : Path x y} {q : Path x z} (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ {s t : I}, p s = q t → s = 0 ∧ t = 0) : Function.Injective (p.symm.trans q) := by
  intro s t h
  rw [Path.trans_apply, Path.trans_apply] at h
  simp only [Path.symm_apply] at h
  split_ifs at h with hs ht ht
  · have h' : 1 - 2 * (s : ℝ) = 1 - 2 * (t : ℝ) :=
      congrArg Subtype.val (hp h)
    exact Subtype.ext (by linarith)
  · obtain ⟨ha,hb⟩ := hmeet h
    have ha' : 1 - 2 * (s : ℝ) = 0 := congrArg Subtype.val ha
    have hb' : 2 * (t : ℝ) - 1 = 0 := congrArg Subtype.val hb
    exact Subtype.ext (by linarith)
  · obtain ⟨ha,hb⟩ := hmeet h.symm
    have ha' : 1 - 2 * (t : ℝ) = 0 := congrArg Subtype.val ha
    have hb' : 2 * (s : ℝ) - 1 = 0 := congrArg Subtype.val hb
    exact Subtype.ext (by linarith)
  · have h' : 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 :=
      congrArg Subtype.val (hq h)
    exact Subtype.ext (by linarith)

theorem liftedOuter_injective {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    Function.Injective (liftedOuter hl hr) :=
  injective_two_arcs (liftedUpper_injective hl hr) (liftedLower_injective hl hr)
    (liftedUpper_lower_meet hl hr)

/-- The two physical slit banks make one vertical segment, meeting at zero. -/
noncomputable def bankPath (α : ℝ) : Path (upperBankEnd α) (lowerBankEnd α) where
  toFun t := (((1 - 2 * (t : ℝ)) * Real.sqrt (1 + α) : ℝ) : ℂ) * Complex.I
  continuous_toFun := by fun_prop
  source' := by simp [upperBankEnd]
  target' := by norm_num [lowerBankEnd]

theorem bankPath_im (α : ℝ) (t : I) :
    (bankPath α t).im = (1 - 2 * (t : ℝ)) * Real.sqrt (1 + α) := by
  simp [bankPath]

theorem bankPath_injective {α : ℝ} (hl : -1 < α) : Function.Injective (bankPath α) := by
  intro s t h
  have hh := congrArg Complex.im h
  rw [bankPath_im, bankPath_im] at hh
  have he := mul_right_cancel₀ (Real.sqrt_pos.mpr (show 0 < 1 + α by linarith)).ne' hh
  exact Subtype.ext (by linarith)

theorem bankPath_re (α : ℝ) (t : I) : (bankPath α t).re = 0 := by
  simp [bankPath]

theorem range_bankPath {α : ℝ} (hl : -1 < α) :
    range (bankPath α) = {u | u.re = 0 ∧ |u.im| ≤ Real.sqrt (1 + α)} := by
  ext u
  have hpos : 0 < Real.sqrt (1 + α) := Real.sqrt_pos.mpr (by linarith)
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨bankPath_re _ _, ?_⟩
    rw [bankPath_im]
    rw [abs_mul, abs_of_pos hpos]
    exact mul_le_of_le_one_left hpos.le (abs_le.mpr ⟨by linarith [t.property.2], by linarith [t.property.1]⟩)
  · rintro ⟨hu,hb⟩
    obtain ⟨hy₀, hy₁⟩ := abs_le.mp hb
    let t := (Real.sqrt (1 + α) - u.im) / (2 * Real.sqrt (1 + α))
    have hden : 0 < 2 * Real.sqrt (1 + α) := by positivity
    have ht : t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hy₁) hden.le, (div_le_one hden).mpr (by linarith)⟩
    refine ⟨⟨t, ht⟩, Complex.ext (by rw [bankPath_re, hu]) ?_⟩
    rw [bankPath_im]
    change (1 - 2 * t) * Real.sqrt (1 + α) = u.im
    dsimp [t]; field_simp; ring

theorem liftedOuter_bankPath_inter {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    range (liftedOuter hl hr) ∩ range (bankPath α) = {upperBankEnd α, lowerBankEnd α} := by
  apply Subset.antisymm
  · rintro u ⟨houter, hbank⟩
    rw [range_bankPath hl] at hbank
    have hzero := hbank.1
    rw [range_liftedOuter] at houter
    rcases houter with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · by_cases ht : t = 1
      · subst t; rw [(liftedUpper hl hr).target]; exact mem_insert _ _
      exact ((liftedUpper_re_pos hl hr ht).ne' hzero).elim
    · by_cases ht : t = 1
      · subst t; rw [(liftedLower hl hr).target]; exact mem_insert_of_mem _ rfl
      exact ((liftedLower_re_pos hl hr ht).ne' hzero).elim
  · rintro u (rfl | rfl)
    · exact ⟨⟨0, (liftedOuter hl hr).source⟩, ⟨0, (bankPath α).source⟩⟩
    · exact ⟨⟨1, (liftedOuter hl hr).target⟩, ⟨1, (bankPath α).target⟩⟩

noncomputable def unfoldedBoundary {α : ℝ} (hl : -1 < α) (hr : α < 0) : Set ℂ :=
  range (liftedOuter hl hr) ∪ range (bankPath α)

theorem unfoldedBoundary_isJordanCurve {α : ℝ} (hl : -1 < α) (hr : α < 0) :
    TauCeti.IsJordanCurve (unfoldedBoundary hl hr) :=
  TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair
    (liftedOuter_injective hl hr) (bankPath_injective hl) (liftedOuter_bankPath_inter hl hr)

end BelgianChocolate.SlitBoundaryGeometry
