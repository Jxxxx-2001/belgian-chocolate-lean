import SlitBarrierMean

namespace BelgianChocolate.SlitHarmonicMeasure

open Complex Metric Set MeasureTheory
open BelgianChocolate.SlitBoundaryGeometry BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex
open scoped Topology
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
/-- As the slit shrinks at the left endpoint, the rational harmonic
barrier `(1-α²)/(1-αw)` equals or exceeds one along the slit. -/
theorem b_le_one_sub_sq {α : ℝ} {F : ℂ → ℂ} (hl : -1 < α) (hr : α < 0)
    (h : CenteredUnfoldedChart α F) : b α F ≤ 1-α^2 := by
  let G := folding α ∘ F
  let H := fun z : ℂ => ((1-α^2 : ℝ) : ℂ)/(1-(α : ℂ)*G z)
  have hk : 0 < 1-α^2 := by
    nlinarith [mul_pos (by linarith : 0 < 1+α) (by linarith : 0 < 1-α)]
  have hden {z : ℂ} (hz : z ∈ closedBall 0 1) : 0 < (1-(α : ℂ)*G z).re := by
    have hn : ‖G z‖ ≤ 1 := norm_folded_chart_le_one h hz
    have hlr := (neg_le_of_abs_le ((Complex.abs_re_le_norm (G z)).trans hn))
    simp [Complex.mul_re]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hr.le (by linarith : 0 ≤ (G z).re+1)]
  have hne {z : ℂ} (hz : z ∈ closedBall 0 1) : 1-(α : ℂ)*G z ≠ 0 := by
    intro he
    have hh := hden hz
    rw [he] at hh
    simp at hh
  have hdiff := h.folded_interior.2.1
  have hcont : ContinuousOn G (closedBall 0 1) :=
    (differentiable_folding α).continuous.comp_continuousOn h.closed_continuous
  have hH₀ : (H 0).re = 1-α^2 := by
    have hz : G 0 = 0 := h.folded_interior.1
    simp only [H, hz, mul_zero, sub_zero, div_one, ofReal_re]
  rw [← hH₀]
  apply mass_le_re_barrier (H := H) h
  · change MeasurableSet ({w : ℂ | w.im = 0} ∩ ({w : ℂ | -1 ≤ w.re} ∩ {w : ℂ | w.re ≤ α}))
    exact ((isClosed_eq continuous_im continuous_const).inter
      ((isClosed_le continuous_const continuous_re).inter (isClosed_le continuous_re continuous_const))).measurableSet
  · change DifferentiableOn ℂ (fun z => ((1-α^2 : ℝ) : ℂ)/(1-(α : ℂ)*G z)) _
    have hdG : DifferentiableOn ℂ G (ball 0 1) := hdiff
    exact (differentiableOn_const _).div ((differentiableOn_const (1 : ℂ)).sub
      (hdG.const_mul (α : ℂ))) (fun _ hz => hne (ball_subset_closedBall hz))
  · change ContinuousOn (fun z => ((1-α^2 : ℝ) : ℂ)/(1-(α : ℂ)*G z)) _
    have h1 : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (closedBall 0 1) := continuousOn_const
    have hk' : ContinuousOn (fun _ : ℂ => ((1-α^2 : ℝ) : ℂ)) (closedBall 0 1) := continuousOn_const
    exact hk'.div (h1.sub (hcont.const_mul (α : ℂ))) (fun _ hz => hne hz)
  · intro z hz
    have hz' := sphere_subset_closedBall hz
    by_cases he : G z ∈ negativeSlit α
    · change (negativeSlit α).indicator (fun _ => (1 : ℝ)) (G z) ≤ (H z).re
      rw [Set.indicator_of_mem he]
      have hzr : ((G z).re : ℂ) = G z := Complex.ext (by simp) (by simpa using he.1.symm)
      have hb := he.2.2
      have hp := hden hz'
      rw [← hzr] at hp
      simp only [← ofReal_mul, ← ofReal_one, ← ofReal_sub, ofReal_re] at hp
      change 1 ≤ (((1-α^2 : ℝ) : ℂ)/(1-(α : ℂ)*G z)).re
      rw [← hzr]
      simp only [← ofReal_mul, ← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]
      apply (one_le_div hp).mpr
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hr.le (sub_nonneg.mpr hb)]
    · change (negativeSlit α).indicator (fun _ => (1 : ℝ)) (G z) ≤ (H z).re
      rw [Set.indicator_of_notMem he]
      change 0 ≤ (((1-α^2 : ℝ) : ℂ)/(1-(α : ℂ)*G z)).re
      simp only [Complex.div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
      exact div_nonneg (mul_nonneg hk.le (hden hz').le) (Complex.normSq_nonneg _)

/-- The lower semicircle has mass at most three quarters for every centered
chart. The majorant is the real part of `(3+w²+2iw)/4`. -/
theorem d_le_three_quarters {α : ℝ} {F : ℂ → ℂ} (h : CenteredUnfoldedChart α F) :
    d α F ≤ 3/4 := by
  let E : Set ℂ := {w | ‖w‖ = 1 ∧ w.im ≤ 0}
  have hsub : lowerEdge ⊆ E := by
    rintro _ ⟨θ, hθ, rfl⟩
    refine ⟨?_, ?_⟩
    · simp [Complex.norm_exp, Complex.mul_re]
    · simp [Complex.exp_im]
      exact (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le
  apply (mass_mono (α := α) (F := F) hsub).trans
  let G := folding α ∘ F
  let H := fun z : ℂ => (3+(G z)^2+2*I*G z)/4
  have hc : ContinuousOn G (closedBall 0 1) :=
    (differentiable_folding α).continuous.comp_continuousOn h.closed_continuous
  have hd : DifferentiableOn ℂ G (ball 0 1) := h.folded_interior.2.1
  have h0 : (H 0).re = 3/4 := by norm_num [H, G, h.zero]
  rw [← h0]
  apply mass_le_re_barrier (H := H) h
  · change MeasurableSet ({w : ℂ | ‖w‖ = 1} ∩ {w : ℂ | w.im ≤ 0})
    exact ((isClosed_eq continuous_norm continuous_const).inter
      (isClosed_le continuous_im continuous_const)).measurableSet
  · exact (((differentiableOn_const (3 : ℂ)).add (hd.pow 2)).add
      (hd.const_mul (2*I))).div_const 4
  · have hcst : ContinuousOn (fun _ : ℂ => (3 : ℂ)) (closedBall 0 1) := continuousOn_const
    exact ((hcst.add (hc.pow 2)).add (hc.const_mul (2*I))).div_const 4
  · intro z hz
    have hnorm : ‖G z‖ ≤ 1 := norm_folded_chart_le_one h (sphere_subset_closedBall hz)
    have him := (abs_le.mp ((Complex.abs_im_le_norm _).trans hnorm))
    have hform : (H z).re = (3+(G z).re^2-(G z).im^2-2*(G z).im)/4 := by
      simp [H, sq, Complex.mul_re]
      ring
    change E.indicator (fun _ => (1 : ℝ)) (G z) ≤ (H z).re
    rw [hform]
    by_cases he : G z ∈ E
    · rw [Set.indicator_of_mem he]
      have hsq := Complex.sq_norm (G z)
      rw [he.1] at hsq
      simp [Complex.normSq_apply] at hsq
      have hprod := mul_nonpos_of_nonpos_of_nonneg he.2 (by linarith [him.1] : 0 ≤ 1+(G z).im)
      change (1 : ℝ) ≤ _
      nlinarith
    · rw [Set.indicator_of_notMem he]
      have habs := sq_le_sq' him.1 him.2
      nlinarith [sq_nonneg (G z).re]

/-- A concrete short slit already gives the left sign required by the
intermediate-value argument. -/
theorem a_gt_b_of_short_slit {α : ℝ} {F : ℂ → ℂ} (hl : -1 < α) (hr : α < 0)
    (hsmall : 7 / 8 < α^2) (h : CenteredUnfoldedChart α F) : b α F < a α F := by
  linarith [b_le_one_sub_sq hl hr h, d_le_three_quarters h, a_add_b_add_d h hl hr]

theorem a_gt_b_at_short_slit {F : ℂ → ℂ} (h : CenteredUnfoldedChart (-19/20) F) :
    b (-19/20) F < a (-19/20) F := by
  exact a_gt_b_of_short_slit (by norm_num) (by norm_num) (by norm_num) h

theorem b_tendsto_at_left {F : ℝ → ℂ → ℂ}
    (hF : ∀ α ∈ Ioo (-1 : ℝ) 0, CenteredUnfoldedChart α (F α)) :
    Filter.Tendsto (fun α => b α (F α)) (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
  have hc : Continuous (fun α : ℝ => 1-α^2) := by fun_prop
  have ht : Filter.Tendsto (fun α : ℝ => 1-α^2) (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
    simpa using (hc.continuousAt (x := (-1 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (-1 : ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Filter.Eventually.of_forall (fun _ => mass_nonneg ..))
  filter_upwards [self_mem_nhdsWithin (s := Ioi (-1 : ℝ)),
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with α hl hr
  exact b_le_one_sub_sq hl hr (hF α ⟨hl, hr⟩)

end BelgianChocolate.SlitHarmonicMeasure
