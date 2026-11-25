import SlitBarrierMean

namespace BelgianChocolate.SlitHarmonicMeasure

open Complex Metric Set
open BelgianChocolate.SlitBoundaryGeometry BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex
open scoped Topology

private noncomputable def outerRadius : ℝ := Real.exp (-(Real.pi / 2))

private theorem outerRadius_pos : 0 < outerRadius := Real.exp_pos _

private theorem outerRadius_le_one : outerRadius ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])

private theorem curvedEdge_norm_ge {w : ℂ} (hw : w ∈ MarkedRealAxis.curvedEdge) :
    outerRadius ≤ ‖w‖ := by
  obtain ⟨θ, hθ, rfl⟩ := hw
  exact (norm_upperPoint_bounds ⟨hθ.1.le, hθ.2.le⟩).1

private theorem lowerEdge_norm_ge {w : ℂ} (hw : w ∈ lowerEdge) :
    outerRadius ≤ ‖w‖ := by
  obtain ⟨θ, _, rfl⟩ := hw
  simpa [Complex.norm_exp, Complex.mul_re] using outerRadius_le_one

/-- The real part of a quadratic on the unfolded chart majorizes the
indicator of the region beyond the minimum radius of the outer arcs. -/
private theorem outer_mass_le {α : ℝ} {F : ℂ → ℂ} (hr : α < 0)
    (hnear : -α ≤ outerRadius / 2) (h : CenteredUnfoldedChart α F) :
    mass α F {w | outerRadius ≤ ‖w‖} ≤ 8 * Real.sqrt (-α) / outerRadius := by
  let E : Set ℂ := {w | outerRadius ≤ ‖w‖}
  let H : ℂ → ℂ := fun z => (2 / (outerRadius : ℂ)) * (4 * F z - F z ^ 2)
  have hcoef : (2 / (outerRadius : ℂ)) = ((2 / outerRadius : ℝ) : ℂ) := by
    push_cast
    rfl
  have hform (z : ℂ) : (H z).re = (2 / outerRadius) *
      (4 * (F z).re - (F z).re ^ 2 + (F z).im ^ 2) := by
    change ((2 / (outerRadius : ℂ)) * (4 * F z - F z ^ 2)).re = _
    rw [hcoef]
    simp [Complex.mul_re, Complex.sub_re, pow_two, outerRadius_pos.ne']
    ring
  have hα : ‖(α : ℂ)‖ = -α := by rw [norm_real, Real.norm_eq_abs, abs_of_neg hr]
  have hsquare (z : ℂ) : ‖F z‖ ^ 2 = ‖folding α (F z) - (α : ℂ)‖ := by
    rw [folding, add_sub_cancel_right, norm_pow]
  have hcoef_nonneg : 0 ≤ 2 / outerRadius := div_nonneg (by norm_num) outerRadius_pos.le
  have hcenter : (H 0).re ≤ 8 * Real.sqrt (-α) / outerRadius := by
    have hzero : folding α (F 0) = 0 := h.folded_interior.1
    have hs0 : ‖F 0‖ ^ 2 = -α := by rw [hsquare, hzero, zero_sub, norm_neg, hα]
    have hn : ‖F 0‖ = Real.sqrt (-α) := by rw [← hs0, Real.sqrt_sq (norm_nonneg _)]
    have hs : (F 0).re ≤ Real.sqrt (-α) := hn ▸ Complex.re_le_norm (F 0)
    rw [hform]
    have hleft : 4 * (F 0).re - (F 0).re ^ 2 + (F 0).im ^ 2 ≤ 4 * Real.sqrt (-α) := by
      have he := congrArg Complex.re (show (F 0)^2 + (α : ℂ) = 0 from hzero)
      simp [pow_two, Complex.mul_re] at he
      linarith
    calc
      _ ≤ (2 / outerRadius) * (4 * Real.sqrt (-α)) :=
        mul_le_mul_of_nonneg_left hleft hcoef_nonneg
      _ = _ := by ring
  apply le_trans (mass_le_re_barrier (H := H) h
    ((isClosed_le continuous_const continuous_norm).measurableSet) ?_ ?_ ?_) hcenter
  · exact ((h.holomorphic.const_mul 4).sub (h.holomorphic.pow 2)).const_mul _
  · exact ((h.closed_continuous.const_mul 4).sub (h.closed_continuous.pow 2)).const_mul _
  · intro z hz
    have hclosed := sphere_subset_closedBall hz
    have hre : 0 ≤ (F z).re :=
      closure_minimal (s := unfoldedDomain α) (fun _ hu => hu.1.le)
        (isClosed_le continuous_const continuous_re) (h.closed_bij.mapsTo hclosed)
    have hnorm : ‖F z‖ ^ 2 ≤ 2 := by
      rw [hsquare z]
      have htri := norm_sub_le (folding α (F z)) (α : ℂ)
      rw [hα] at htri
      linarith [norm_folded_chart_le_one h hclosed, outerRadius_le_one]
    have hx : (F z).re ≤ 2 := by
      have hxn := Complex.re_le_norm (F z)
      nlinarith [norm_nonneg (F z)]
    have hmajor : ‖F z‖ ^ 2 ≤ 4 * (F z).re - (F z).re ^ 2 + (F z).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [mul_nonneg hre (sub_nonneg.mpr hx)]
    rw [hform]
    change E.indicator (fun _ => (1 : ℝ)) (folding α (F z)) ≤ _
    by_cases he : folding α (F z) ∈ E
    · rw [Set.indicator_of_mem he]
      have hlow : outerRadius / 2 ≤ ‖F z‖ ^ 2 := by
        rw [hsquare z]
        have ht := norm_add_le (folding α (F z) - (α : ℂ)) (α : ℂ)
        rw [sub_add_cancel, hα] at ht
        change outerRadius ≤ ‖folding α (F z)‖ at he
        linarith
      calc
        1 = (2 / outerRadius) * (outerRadius / 2) := by field_simp [outerRadius_pos.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (hlow.trans hmajor) hcoef_nonneg
    · rw [Set.indicator_of_notMem he]
      exact mul_nonneg hcoef_nonneg ((sq_nonneg ‖F z‖).trans hmajor)

private theorem a_le_right_bound {α : ℝ} {F : ℂ → ℂ} (hr : α < 0)
    (hnear : -α ≤ outerRadius / 2) (h : CenteredUnfoldedChart α F) :
    a α F ≤ 8 * Real.sqrt (-α) / outerRadius :=
  (mass_mono (fun _ hw => curvedEdge_norm_ge hw)).trans (outer_mass_le hr hnear h)

private theorem d_le_right_bound {α : ℝ} {F : ℂ → ℂ} (hr : α < 0)
    (hnear : -α ≤ outerRadius / 2) (h : CenteredUnfoldedChart α F) :
    d α F ≤ 8 * Real.sqrt (-α) / outerRadius :=
  (mass_mono (fun _ hw => lowerEdge_norm_ge hw)).trans (outer_mass_le hr hnear h)

/-- A concrete slit tip sufficiently close to the origin for the opposite
sign in the intermediate-value argument. -/
noncomputable def rightBalanceTip : ℝ := -(Real.exp (-(Real.pi / 2)) / 64) ^ 2

theorem rightBalanceTip_mem : rightBalanceTip ∈ Ioo (-1 : ℝ) 0 := by
  change -1 < -(outerRadius / 64) ^ 2 ∧ -(outerRadius / 64) ^ 2 < 0
  have hp : 0 < outerRadius / 64 := div_pos outerRadius_pos (by norm_num)
  have hq := outerRadius_le_one
  constructor <;> nlinarith [sq_pos_of_pos hp, mul_nonneg hp.le (show 0 ≤ 1 - outerRadius / 64 by linarith)]

theorem a_lt_b_at_right_tip {F : ℂ → ℂ} (h : CenteredUnfoldedChart rightBalanceTip F) :
    a rightBalanceTip F < b rightBalanceTip F := by
  have hp : 0 < outerRadius / 64 := div_pos outerRadius_pos (by norm_num)
  obtain ⟨hl, hr⟩ := rightBalanceTip_mem
  have hnear : -rightBalanceTip ≤ outerRadius / 2 := by
    change -(-(outerRadius / 64) ^ 2) ≤ outerRadius / 2
    nlinarith [outerRadius_le_one,
      mul_nonneg hp.le (show 0 ≤ 1 - outerRadius / 64 by linarith [outerRadius_le_one])]
  have hbound : 8 * Real.sqrt (-rightBalanceTip) / outerRadius = 1 / 8 := by
    change 8 * Real.sqrt (-(-(outerRadius / 64) ^ 2)) / outerRadius = _
    rw [neg_neg, Real.sqrt_sq hp.le]
    field_simp [outerRadius_pos.ne']
    norm_num
  have ha := a_le_right_bound hr hnear h
  have hd := d_le_right_bound hr hnear h
  rw [hbound] at ha hd
  linarith [a_add_b_add_d h hl hr]

theorem b_tendsto_at_right {F : ℝ → ℂ → ℂ}
    (hF : ∀ α ∈ Ioo (-1 : ℝ) 0, CenteredUnfoldedChart α (F α)) :
    Filter.Tendsto (fun α => b α (F α)) (𝓝[<] (0 : ℝ)) (𝓝 1) := by
  have hc : Continuous (fun α : ℝ => 1 - 2 * (8 * Real.sqrt (-α) / outerRadius)) := by
    fun_prop
  have ht : Filter.Tendsto (fun α : ℝ => 1 - 2 * (8 * Real.sqrt (-α) / outerRadius))
      (𝓝[<] (0 : ℝ)) (𝓝 1) := by
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ht tendsto_const_nhds ?_
    (Filter.Eventually.of_forall (fun α => (mass_mono (subset_univ _)).trans_eq (mass_univ α (F α))))
  have hopen : ∀ᶠ α : ℝ in 𝓝[<] (0 : ℝ), -(outerRadius / 2) < α :=
    mem_nhdsWithin_of_mem_nhds (lt_mem_nhds (by linarith [outerRadius_pos]))
  filter_upwards [self_mem_nhdsWithin (s := Iio (0 : ℝ)),
    mem_nhdsWithin_of_mem_nhds (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0)), hopen] with α hr hl hnear
  have hnear' : -α ≤ outerRadius / 2 := by linarith
  have h := hF α ⟨hl, hr⟩
  change 1 - 2 * (8 * Real.sqrt (-α) / outerRadius) ≤ b α (F α)
  linarith [a_le_right_bound hr hnear' h, d_le_right_bound hr hnear' h, a_add_b_add_d h hl hr]

end BelgianChocolate.SlitHarmonicMeasure
