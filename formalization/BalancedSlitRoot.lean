import SlitLeftBalanceBarrier
import SlitParameterRegularity
import SlitRightBalanceBarrier
import Mathlib.Topology.Order.IntermediateValue

/-! The canonical harmonic weights and the intermediate-value step of the
balanced-slit construction. -/

namespace BelgianChocolate.SlitHarmonicMeasure

open Set BelgianChocolate.SlitBoundaryGeometry

/-- A centered chart for each slit parameter in the physical parameter interval. -/
noncomputable def centeredChart (α : ℝ) : ℂ → ℂ :=
  if h : α ∈ Ioo (-1 : ℝ) 0 then
    Classical.choose (exists_centeredUnfoldedChart h.1 h.2)
  else 0

theorem centeredChart_spec {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 0) :
    CenteredUnfoldedChart α (centeredChart α) := by
  rw [centeredChart, dite_eq_left hα]
  exact Classical.choose_spec (exists_centeredUnfoldedChart hα.1 hα.2)

/-- Harmonic measure of the curved upper edge from the physical origin. -/
noncomputable def curvedMass (α : ℝ) : ℝ := a α (centeredChart α)

/-- Harmonic measure of the two slit banks from the physical origin. -/
noncomputable def slitMass (α : ℝ) : ℝ := b α (centeredChart α)

/-- Harmonic measure of the lower semicircle from the physical origin. -/
noncomputable def lowerMass (α : ℝ) : ℝ := d α (centeredChart α)

def IsBalanced (α : ℝ) : Prop :=
  α ∈ Ioo (-1 : ℝ) 0 ∧ curvedMass α = slitMass α

theorem mass_partition {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 0) :
    curvedMass α + slitMass α + lowerMass α = 1 :=
  a_add_b_add_d (centeredChart_spec hα) hα.1 hα.2

theorem continuousOn_curvedMass : ContinuousOn curvedMass (Ioo (-1 : ℝ) 0) :=
  (variation_of_centered_charts fun _ => centeredChart_spec).1

theorem continuousOn_lowerMass : ContinuousOn lowerMass (Ioo (-1 : ℝ) 0) :=
  (variation_of_centered_charts fun _ => centeredChart_spec).2.2.1

theorem continuousOn_slitMass : ContinuousOn slitMass (Ioo (-1 : ℝ) 0) :=
  (variation_of_centered_charts fun _ => centeredChart_spec).2.1

theorem strictAntiOn_curvedMass : StrictAntiOn curvedMass (Ioo (-1 : ℝ) 0) :=
  (variation_of_centered_charts fun _ => centeredChart_spec).2.2.2.1

theorem strictMonoOn_slitMass : StrictMonoOn slitMass (Ioo (-1 : ℝ) 0) :=
  (variation_of_centered_charts fun _ => centeredChart_spec).2.2.2.2.1

/-- Opposite signs and continuity of the difference yield a balanced slit. -/
theorem exists_balanced_of_signs
    (hcont : ContinuousOn (fun α => curvedMass α - slitMass α) (Ioo (-1 : ℝ) 0))
    {β : ℝ} (hβ : β ∈ Ioo (-19 / 20 : ℝ) 0) (hsgn : curvedMass β < slitMass β) :
    ∃ α : ℝ, IsBalanced α := by
  have hleft : (-19 / 20 : ℝ) ∈ Ioo (-1 : ℝ) 0 := by norm_num
  have hsub : Icc (-19 / 20 : ℝ) β ⊆ Ioo (-1 : ℝ) 0 :=
    fun _ hx => ⟨hleft.1.trans_le hx.1, hx.2.trans_lt hβ.2⟩
  have hpos : slitMass (-19 / 20) < curvedMass (-19 / 20) :=
    a_gt_b_at_short_slit (centeredChart_spec hleft)
  have hz := intermediate_value_Icc' hβ.1.le (hcont.mono hsub)
    (show (0 : ℝ) ∈ Icc (curvedMass β - slitMass β)
      (curvedMass (-19 / 20) - slitMass (-19 / 20)) from
      ⟨sub_nonpos.mpr hsgn.le, sub_nonneg.mpr hpos.le⟩)
  obtain ⟨α, hα, heq⟩ := hz
  exact ⟨α, hsub hα, sub_eq_zero.mp heq⟩

/-- Both signs used in the intermediate-value argument follow from the
concrete slit barriers. -/
theorem exists_balanced_of_continuous
    (hcont : ContinuousOn (fun α => curvedMass α - slitMass α) (Ioo (-1 : ℝ) 0)) :
    ∃ α : ℝ, IsBalanced α := by
  refine exists_balanced_of_signs hcont ⟨?_, rightBalanceTip_mem.2⟩
    (a_lt_b_at_right_tip (centeredChart_spec rightBalanceTip_mem))
  have hpos : 0 < Real.exp (-(Real.pi / 2)) / 64 := by positivity
  have hle : Real.exp (-(Real.pi / 2)) / 64 ≤ 1 / 64 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  unfold rightBalanceTip
  nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hle)]

/-- The strict comparison of the two harmonic weights gives uniqueness. -/
theorem balanced_unique_of_strict_comparison
    (ha : StrictAntiOn curvedMass (Ioo (-1 : ℝ) 0))
    (hb : StrictMonoOn slitMass (Ioo (-1 : ℝ) 0))
    {α β : ℝ} (hα : IsBalanced α) (hβ : IsBalanced β) : α = β := by
  apply le_antisymm
  · by_contra! hlt
    have ha' := ha hβ.1 hα.1 hlt
    rw [hα.2, hβ.2] at ha'
    exact ha'.not_gt (hb hβ.1 hα.1 hlt)
  · by_contra! hlt
    have ha' := ha hα.1 hβ.1 hlt
    rw [hα.2, hβ.2] at ha'
    exact ha'.not_gt (hb hα.1 hβ.1 hlt)

theorem existsUnique_balanced_slit : ∃! α : ℝ, IsBalanced α := by
  obtain ⟨α, hα⟩ := exists_balanced_of_continuous (continuousOn_curvedMass.sub continuousOn_slitMass)
  exact ⟨α, hα, fun _ hβ =>
    balanced_unique_of_strict_comparison strictAntiOn_curvedMass strictMonoOn_slitMass hβ hα⟩

end BelgianChocolate.SlitHarmonicMeasure
