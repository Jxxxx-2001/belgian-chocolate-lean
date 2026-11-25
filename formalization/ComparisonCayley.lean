import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! The logarithmic coordinate used for the candidate and the competing lift. -/

namespace BelgianChocolate.HarmonicComparison

open Complex Filter Metric Set Topology

/-- The Cayley quotient sending the unit disc into the right half plane. -/
noncomputable def comparisonQuotient (w : ℂ) : ℂ := (1 + w) / (1 - w)

/-- The logarithmic coordinate of the harmonic comparison. -/
noncomputable def comparisonLog (w : ℂ) : ℂ := Complex.log (comparisonQuotient w)

theorem comparisonQuotient_re (w : ℂ) :
    (comparisonQuotient w).re = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  rw [comparisonQuotient, Complex.div_re, ← add_div, Complex.normSq_apply w]
  congr 1
  simp only [add_re, sub_re, one_re, add_im, sub_im, one_im, zero_add, zero_sub]
  ring

theorem comparisonQuotient_im (w : ℂ) :
    (comparisonQuotient w).im = (2 * w.im) / Complex.normSq (1 - w) := by
  rw [comparisonQuotient, Complex.div_im, ← sub_div]
  congr 1
  simp only [add_re, sub_re, one_re, add_im, sub_im, one_im, zero_add, zero_sub]
  ring

private theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have heq : w = 1 := (sub_eq_zero.mp h).symm
  simp [heq] at hw

theorem comparisonQuotient_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (comparisonQuotient w).re := by
  rw [comparisonQuotient_re, ← Complex.sq_norm w]
  apply div_pos
  · nlinarith [norm_nonneg w]
  · exact Complex.normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hw)

theorem differentiableOn_comparisonLog :
    DifferentiableOn ℂ comparisonLog (ball 0 1) := by
  have hA : DifferentiableOn ℂ (fun w : ℂ ↦ 1 + w) (ball 0 1) :=
    (differentiableOn_const (1 : ℂ)).add differentiableOn_id
  have hB : DifferentiableOn ℂ (fun w : ℂ ↦ 1 - w) (ball 0 1) :=
    (differentiableOn_const (1 : ℂ)).sub differentiableOn_id
  have hQ : DifferentiableOn ℂ comparisonQuotient (ball 0 1) := by
    change DifferentiableOn ℂ (fun w : ℂ ↦ (1 + w) / (1 - w)) (ball 0 1)
    exact hA.div hB (fun _ hz ↦ one_sub_ne_zero_of_norm_lt_one (mem_ball_zero_iff.mp hz))
  change DifferentiableOn ℂ (fun w ↦ Complex.log (comparisonQuotient w)) (ball 0 1)
  exact hQ.clog (fun _ hz ↦ Complex.mem_slitPlane_iff.mpr
    (Or.inl (comparisonQuotient_re_pos (mem_ball_zero_iff.mp hz))))

@[simp] theorem comparisonLog_zero : comparisonLog 0 = 0 := by
  simp [comparisonLog, comparisonQuotient]

theorem abs_im_comparisonLog_lt {w : ℂ} (hw : ‖w‖ < 1) :
    |(comparisonLog w).im| < Real.pi / 2 := by
  rw [comparisonLog, Complex.log_im, Complex.abs_arg_lt_pi_div_two_iff]
  exact Or.inl (comparisonQuotient_re_pos hw)

theorem im_comparisonLog_eq_zero_of_im_eq_zero {w : ℂ} (hw : ‖w‖ < 1)
    (hwi : w.im = 0) : (comparisonLog w).im = 0 := by
  rw [comparisonLog, Complex.log_im, Complex.arg_eq_zero_iff]
  exact ⟨(comparisonQuotient_re_pos hw).le, by simp [comparisonQuotient_im, hwi]⟩

/-- At a point of the open lower semicircle the coordinate has a continuous
local boundary value, with imaginary part equal to `-π/2`. -/
theorem tendsto_im_comparisonLog_at_lowerCircle {w : ℂ} (hw : ‖w‖ = 1)
    (hwi : w.im < 0) :
    Tendsto (fun z ↦ (comparisonLog z).im) (𝓝 w) (𝓝 (-(Real.pi / 2))) := by
  have hd : (1 : ℂ) - w ≠ 0 := by
    intro h
    have heq : w = 1 := (sub_eq_zero.mp h).symm
    simp [heq] at hwi
  have hQi : (comparisonQuotient w).im < 0 := by
    rw [comparisonQuotient_im]
    exact div_neg_of_neg_of_pos (by linarith) (Complex.normSq_pos.mpr hd)
  have hQr : (comparisonQuotient w).re = 0 := by
    rw [comparisonQuotient_re, ← Complex.sq_norm w, hw]
    simp
  have hA : ContinuousAt (fun z : ℂ ↦ 1 + z) w := continuousAt_const.add continuousAt_id
  have hB : ContinuousAt (fun z : ℂ ↦ 1 - z) w := continuousAt_const.sub continuousAt_id
  have hQ : ContinuousAt comparisonQuotient w := by
    change ContinuousAt (fun z : ℂ ↦ (1 + z) / (1 - z)) w
    exact hA.div hB hd
  have hK : ContinuousAt comparisonLog w := by
    change ContinuousAt (fun z ↦ Complex.log (comparisonQuotient z)) w
    exact hQ.clog (Complex.mem_slitPlane_iff.mpr (Or.inr hQi.ne))
  have him : (comparisonLog w).im = -(Real.pi / 2) := by
    rw [comparisonLog, Complex.log_im, Complex.arg_eq_neg_pi_div_two_iff]
    exact ⟨hQr, hQi⟩
  have hKIm : ContinuousAt (Complex.im ∘ comparisonLog) w :=
    Complex.continuous_im.continuousAt.comp hK
  have hvalue : (Complex.im ∘ comparisonLog) w = -(Real.pi / 2) := him
  rw [← hvalue]
  exact hKIm.tendsto

theorem injOn_comparisonLog : InjOn comparisonLog (ball (0 : ℂ) 1) := by
  intro x hx y hy heq
  have hxn := mem_ball_zero_iff.mp hx
  have hyn := mem_ball_zero_iff.mp hy
  have hQne {w : ℂ} (hw : ‖w‖ < 1) : comparisonQuotient w ≠ 0 := by
    intro he
    have hr := comparisonQuotient_re_pos hw
    simp [he] at hr
  have hQ : comparisonQuotient x = comparisonQuotient y := by
    simpa only [comparisonLog, Complex.exp_log (hQne hxn), Complex.exp_log (hQne hyn)]
      using congrArg Complex.exp heq
  have hcross := (div_eq_div_iff (one_sub_ne_zero_of_norm_lt_one hxn)
    (one_sub_ne_zero_of_norm_lt_one hyn)).mp hQ
  linear_combination (1 / 2 : ℂ) * hcross

/-- The candidate on the lower unit semicircle and any interior competitor
give the pointwise lower boundary estimate on the open outer arc. The
competitor need not have a boundary value there. -/
theorem im_comparisonLog_difference_lower_at_lowerCircle
    {f g : ℂ → ℂ} {ξ p : ℂ}
    (hg : Tendsto g (𝓝[ball (0 : ℂ) 1] ξ) (𝓝 p))
    (hp : ‖p‖ = 1) (hpi : p.im < 0)
    (hf : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ < 1) :
    ∀ ε > 0, ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z ξ < d →
      -ε ≤ (comparisonLog (f z) - comparisonLog (g z)).im := by
  intro ε hε
  have hlim := (tendsto_im_comparisonLog_at_lowerCircle hp hpi).comp hg
  have hnear : ∀ᶠ z in 𝓝[ball (0 : ℂ) 1] ξ,
      (comparisonLog (g z)).im < -(Real.pi / 2) + ε :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨d, hd, hbound⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hnear
  refine ⟨d, hd, ?_⟩
  intro z hz hdist
  have hlow := (abs_lt.mp (abs_im_comparisonLog_lt (hf z hz))).1
  have hu := hbound ⟨mem_ball.mpr hdist, hz⟩
  rw [Complex.sub_im]
  linarith

/-- At ordinary points of the open positive segment the two lift values are
real and lie in the disc, so the imaginary part of the difference tends to zero. -/
theorem im_comparisonLog_difference_lower_at_realValues
    {f g : ℂ → ℂ} {ξ p q : ℂ}
    (hf : Tendsto f (𝓝[ball (0 : ℂ) 1] ξ) (𝓝 p))
    (hg : Tendsto g (𝓝[ball (0 : ℂ) 1] ξ) (𝓝 q))
    (hp : ‖p‖ < 1) (hpi : p.im = 0)
    (hq : ‖q‖ < 1) (hqi : q.im = 0) :
    ∀ ε > 0, ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z ξ < d →
      -ε ≤ (comparisonLog (f z) - comparisonLog (g z)).im := by
  have hcont {w : ℂ} (hw : ‖w‖ < 1) : ContinuousAt comparisonLog w :=
    differentiableOn_comparisonLog.continuousOn.continuousAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw))
  have hf' := (hcont hp).tendsto.comp hf
  have hg' := (hcont hq).tendsto.comp hg
  have hlim : Tendsto (fun z ↦ (comparisonLog (f z) - comparisonLog (g z)).im)
      (𝓝[ball (0 : ℂ) 1] ξ) (𝓝 0) := by
    have h := Complex.continuous_im.continuousAt.tendsto.comp (hf'.sub hg')
    rwa [Complex.sub_im, im_comparisonLog_eq_zero_of_im_eq_zero hp hpi,
      im_comparisonLog_eq_zero_of_im_eq_zero hq hqi, sub_zero] at h
  intro ε hε
  have hnear : ∀ᶠ z in 𝓝[ball (0 : ℂ) 1] ξ,
      -ε < (comparisonLog (f z) - comparisonLog (g z)).im :=
    hlim.eventually (lt_mem_nhds (neg_lt_zero.mpr hε))
  obtain ⟨d, hd, hbound⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hnear
  exact ⟨d, hd, fun z hz hdist ↦ (hbound ⟨mem_ball.mpr hdist, hz⟩).le⟩

end BelgianChocolate.HarmonicComparison
