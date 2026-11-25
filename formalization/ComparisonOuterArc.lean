import ComparisonCayley
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! The strict outer-arc comparison after shrinking the competing source. -/

namespace BelgianChocolate.HarmonicComparison

open Complex Filter Metric Set Topology
open scoped Topology

/-- The source half-disc used for the two holomorphic lifts. -/
noncomputable def comparisonHalfDisk : Set ℂ :=
  ball 0 1 ∩ {z | 0 < z.im}

/-- The open outer arc of the source half-disc. -/
def comparisonOuterArc : Set ℂ :=
  {z | ‖z‖ = 1 ∧ 0 < z.im}

theorem comparisonHalfDisk_eq_norm :
    comparisonHalfDisk = {z : ℂ | ‖z‖ < 1 ∧ 0 < z.im} := by
  ext z
  simp [comparisonHalfDisk]

theorem isOpen_comparisonHalfDisk : IsOpen comparisonHalfDisk :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

private theorem norm_scaled (r : ℝ) (hr : 0 < r) (z : ℂ) :
    ‖(r : ℂ) * z‖ = r * ‖z‖ := by
  simp [abs_of_pos hr]

private theorem im_scaled (r : ℝ) (z : ℂ) :
    ((r : ℂ) * z).im = r * z.im := by simp [Complex.mul_im]

theorem scale_halfDisk_mem {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    {z : ℂ} (hz : z ∈ comparisonHalfDisk) : (r : ℂ) * z ∈ comparisonHalfDisk := by
  refine ⟨mem_ball_zero_iff.mpr ?_, ?_⟩
  · rw [norm_scaled r hr]
    exact (mul_lt_of_lt_one_right hr (mem_ball_zero_iff.mp hz.1)).trans_le hr'
  · change 0 < ((r : ℂ) * z).im
    rw [im_scaled]
    exact mul_pos hr hz.2

theorem scale_outerArc_mem {r : ℝ} (hr : 0 < r) (hr' : r < 1)
    {z : ℂ} (hz : z ∈ comparisonOuterArc) : (r : ℂ) * z ∈ comparisonHalfDisk := by
  refine ⟨mem_ball_zero_iff.mpr ?_, ?_⟩
  · simpa only [norm_scaled r hr, hz.1, mul_one] using hr'
  · change 0 < ((r : ℂ) * z).im
    rw [im_scaled]
    exact mul_pos hr hz.2

theorem shrunkLift_norm_lt_one {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    {η φ : ℂ → ℂ} (hη : MapsTo η (ball 0 1) comparisonHalfDisk)
    (hφ : MapsTo φ comparisonHalfDisk (ball 0 1)) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖φ ((r : ℂ) * η z)‖ < 1 :=
  fun _ hz => mem_ball_zero_iff.mp (hφ (scale_halfDisk_mem hr hr' (hη hz)))

theorem differentiableOn_shrunkLift {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    {η φ : ℂ → ℂ} (hη : DifferentiableOn ℂ η (ball 0 1))
    (hmap : MapsTo η (ball 0 1) comparisonHalfDisk)
    (hφ : DifferentiableOn ℂ φ comparisonHalfDisk) :
    DifferentiableOn ℂ (fun z => φ ((r : ℂ) * η z)) (ball 0 1) :=
  hφ.comp (hη.const_mul (r : ℂ)) (fun _ hz => scale_halfDisk_mem hr hr' (hmap hz))

/-- The normalized disc center `it_s` shrinks to the competitor center `it`. -/
theorem shrunk_center {t ts : ℝ} (hts : 0 < ts) :
    ((t / ts : ℝ) : ℂ) * ((ts : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
  have htsc : (ts : ℂ) ≠ 0 := by exact_mod_cast hts.ne'
  rw [Complex.ofReal_div]
  field_simp

theorem shrunkLift_zero {t ts : ℝ} (hts : 0 < ts) {η φ : ℂ → ℂ}
    (hη : η 0 = (ts : ℂ) * Complex.I) (hφ : φ ((t : ℂ) * Complex.I) = 0) :
    φ (((t / ts : ℝ) : ℂ) * η 0) = 0 := by
  rwa [hη, shrunk_center hts]

/-- A closed-disc trace of the candidate on the lower unit circle has limiting
imaginary coordinate (-π/2). Any interior trace of the competitor gives a
strictly positive limiting difference. -/
theorem tendsto_im_difference_of_interior_and_lowerCircle {f g : ℂ → ℂ} {ζ l p : ℂ}
    (hf : Tendsto f (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 l))
    (hg : Tendsto g (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    (hl : ‖l‖ < 1) (hp : ‖p‖ = 1) (hpi : p.im < 0) :
    Tendsto (fun z => (comparisonLog (f z) - comparisonLog (g z)).im)
      (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 ((comparisonLog l).im + Real.pi / 2)) := by
  have hk : ContinuousAt comparisonLog l :=
    differentiableOn_comparisonLog.continuousOn.continuousAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hl))
  have hf' : Tendsto (fun z => (comparisonLog (f z)).im)
      (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 (comparisonLog l).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp (hk.tendsto.comp hf)
  have hg' := (tendsto_im_comparisonLog_at_lowerCircle hp hpi).comp hg
  simpa only [Complex.sub_im, sub_neg_eq_add, Function.comp_def] using hf'.sub hg'

/-- If the scale is strictly below one, an open source outer-arc point
becomes interior. The resulting limiting value of the imaginary difference
has a positive margin. -/
theorem shrunk_outerArc_strict_limit {r : ℝ} (hr : 0 < r) (hr' : r < 1)
    {η φ g : ℂ → ℂ} {ζ q p : ℂ}
    (hη : Tendsto η (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 q))
    (hq : q ∈ comparisonOuterArc)
    (hφ : ContinuousOn φ comparisonHalfDisk) (hmap : MapsTo φ comparisonHalfDisk (ball 0 1))
    (hg : Tendsto g (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    (hp : ‖p‖ = 1) (hpi : p.im < 0) :
    ∃ m : ℝ, 0 < m ∧ Tendsto
      (fun z => (comparisonLog (φ ((r : ℂ) * η z)) - comparisonLog (g z)).im)
      (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 m) := by
  have hqr := scale_outerArc_mem hr hr' hq
  have hf : Tendsto (fun z => φ ((r : ℂ) * η z))
      (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 (φ ((r : ℂ) * q))) := by
    have hlim : Tendsto (fun z => (r : ℂ) * η z)
        (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 ((r : ℂ) * q)) := tendsto_const_nhds.mul hη
    exact (hφ.continuousAt (isOpen_comparisonHalfDisk.mem_nhds hqr)).tendsto.comp hlim
  have hl := mem_ball_zero_iff.mp (hmap hqr)
  refine ⟨_, ?_, tendsto_im_difference_of_interior_and_lowerCircle hf hg hl hp hpi⟩
  have hlow := (abs_lt.mp (abs_im_comparisonLog_lt hl)).1
  linarith

/-- A pointwise positive margin on a sufficiently small interior
neighborhood of the chosen shrunk outer-arc point. -/
theorem shrunk_outerArc_eventually_strict {r : ℝ} (hr : 0 < r) (hr' : r < 1)
    {η φ g : ℂ → ℂ} {ζ q p : ℂ}
    (hη : Tendsto η (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 q))
    (hq : q ∈ comparisonOuterArc)
    (hφ : ContinuousOn φ comparisonHalfDisk) (hmap : MapsTo φ comparisonHalfDisk (ball 0 1))
    (hg : Tendsto g (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    (hp : ‖p‖ = 1) (hpi : p.im < 0) :
    ∃ ε > 0, ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z ζ < d →
      ε ≤ (comparisonLog (φ ((r : ℂ) * η z)) - comparisonLog (g z)).im := by
  obtain ⟨m, hm, hlim⟩ := shrunk_outerArc_strict_limit hr hr' hη hq hφ hmap hg hp hpi
  have hnear : ∀ᶠ z in 𝓝[ball (0 : ℂ) 1] ζ,
      m / 2 < (comparisonLog (φ ((r : ℂ) * η z)) - comparisonLog (g z)).im :=
    hlim.eventually (lt_mem_nhds (half_lt_self hm))
  obtain ⟨d, hd, hbound⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hnear
  exact ⟨m / 2, half_pos hm, d, hd, fun z hz hdist => (hbound ⟨mem_ball.mpr hdist, hz⟩).le⟩

/-- The weak boundary estimate works also at scale one. It uses the
candidate's trace and the open-strip bound for the interior competitor. -/
theorem shrunk_outerArc_lower_bound {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    {η φ g : ℂ → ℂ} {ζ p : ℂ}
    (hη : MapsTo η (ball 0 1) comparisonHalfDisk)
    (hφ : MapsTo φ comparisonHalfDisk (ball 0 1))
    (hg : Tendsto g (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    (hp : ‖p‖ = 1) (hpi : p.im < 0) :
    ∀ ε > 0, ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z ζ < d →
      -ε ≤ (comparisonLog (φ ((r : ℂ) * η z)) - comparisonLog (g z)).im :=
  im_comparisonLog_difference_lower_at_lowerCircle hg hp hpi
    (shrunkLift_norm_lt_one hr hr' hη hφ)

/-- Equality of the two lifts on the disc is inconsistent with a strictly
shrunk competitor at a tracked outer-arc point. -/
theorem shrunk_outerArc_not_eqOn {r : ℝ} (hr : 0 < r) (hr' : r < 1)
    {η φ g : ℂ → ℂ} {ζ q p : ℂ} (hζ : ‖ζ‖ = 1)
    (hη : Tendsto η (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 q))
    (hq : q ∈ comparisonOuterArc)
    (hφ : ContinuousOn φ comparisonHalfDisk) (hmap : MapsTo φ comparisonHalfDisk (ball 0 1))
    (hg : Tendsto g (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    (hp : ‖p‖ = 1) (hpi : p.im < 0) :
    ¬ EqOn (fun z => φ ((r : ℂ) * η z)) g (ball 0 1) := by
  intro heq
  have hne : NeBot (𝓝[ball (0 : ℂ) 1] ζ) := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact mem_closedBall_zero_iff.mpr hζ.le
  let _ : NeBot (𝓝[ball (0 : ℂ) 1] ζ) := hne
  obtain ⟨m, hm, hlim⟩ := shrunk_outerArc_strict_limit hr hr' hη hq hφ hmap hg hp hpi
  have hevent : (fun _ : ℂ => (0 : ℝ)) =ᶠ[𝓝[ball (0 : ℂ) 1] ζ]
      (fun z => (comparisonLog (φ ((r : ℂ) * η z)) - comparisonLog (g z)).im) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have he : φ ((r : ℂ) * η z) = g z := heq hz
    rw [he, sub_self, Complex.zero_im]
  have hzero := tendsto_const_nhds.congr' hevent
  exact hm.ne' (tendsto_nhds_unique hlim hzero)

/-- The manuscript comparison at (r=t/t_s) forces equality of the source
parameters once equality of the two lifts has been obtained. -/
theorem eq_parameter_of_outerArc_comparison {t ts : ℝ} (ht : 0 < t) (hts : 0 < ts) (hle : t ≤ ts)
    {η φ g : ℂ → ℂ} {ζ q p : ℂ} (hζ : ‖ζ‖ = 1)
    (hη : Tendsto η (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 q))
    (hq : q ∈ comparisonOuterArc)
    (hφ : ContinuousOn φ comparisonHalfDisk) (hmap : MapsTo φ comparisonHalfDisk (ball 0 1))
    (hg : Tendsto g (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    (hp : ‖p‖ = 1) (hpi : p.im < 0)
    (heq : EqOn (fun z => φ (((t / ts : ℝ) : ℂ) * η z)) g (ball 0 1)) : t = ts := by
  by_contra hne
  have hr := div_pos ht hts
  have hr' := (div_lt_one hts).2 (lt_of_le_of_ne hle hne)
  exact (shrunk_outerArc_not_eqOn hr hr' hζ hη hq hφ hmap hg hp hpi) heq

/-- Substituting the common source parameter and using surjectivity of the
centered chart transfers equality to the actual source half-disc. -/
theorem pullback_lift_eqOn_of_eq_parameter {t ts : ℝ} (hts : 0 < ts) (he : t = ts)
    {η φ Φ : ℂ → ℂ} (hη : SurjOn η (ball 0 1) comparisonHalfDisk)
    (heq : EqOn (fun z => φ (((t / ts : ℝ) : ℂ) * η z)) (fun z => Φ (η z)) (ball 0 1)) :
    EqOn φ Φ comparisonHalfDisk := by
  intro q hq
  obtain ⟨z, hz, rfl⟩ := hη hq
  have h : φ (((t / ts : ℝ) : ℂ) * η z) = Φ (η z) := heq hz
  rwa [he, div_self hts.ne', Complex.ofReal_one, one_mul] at h

/-- Closed-disc boundary data for the chart and candidate suffice to exhibit
an actual tracked outer-arc point and rule out a strictly smaller source
parameter. The conclusion includes equality of the unscaled lifts. -/
theorem eq_parameter_and_lifts_of_closedDisc_comparison
    {t ts : ℝ} (ht : 0 < t) (hts : 0 < ts) (hle : t ≤ ts) {η φ Φ : ℂ → ℂ}
    (hηsurj : SurjOn η (ball 0 1) comparisonHalfDisk)
    (hηouter : SurjOn η (sphere 0 1) comparisonOuterArc)
    (hηcont : ContinuousOn η (closedBall 0 1))
    (hΦcont : ContinuousOn (fun z => Φ (η z)) (closedBall 0 1))
    (hΦouter : MapsTo Φ comparisonOuterArc {p | ‖p‖ = 1 ∧ p.im < 0})
    (hφcont : ContinuousOn φ comparisonHalfDisk)
    (hφmap : MapsTo φ comparisonHalfDisk (ball 0 1))
    (heq : EqOn (fun z => φ (((t / ts : ℝ) : ℂ) * η z)) (fun z => Φ (η z)) (ball 0 1)) :
    t = ts ∧ EqOn φ Φ comparisonHalfDisk := by
  have hi : Complex.I ∈ comparisonOuterArc := ⟨by simp, by simp⟩
  obtain ⟨z, hz, hzi⟩ := hηouter hi
  have hnorm : ‖z‖ = 1 := by simpa [mem_sphere, Complex.dist_eq] using hz
  have hzcl : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hnorm.le
  have houter : η z ∈ comparisonOuterArc := hzi ▸ hi
  have htarget := hΦouter houter
  have hηlim : Tendsto η (𝓝[ball (0 : ℂ) 1] z) (𝓝 (η z)) :=
    (hηcont z hzcl).mono ball_subset_closedBall
  have hΦlim : Tendsto (fun w => Φ (η w)) (𝓝[ball (0 : ℂ) 1] z) (𝓝 (Φ (η z))) :=
    (hΦcont z hzcl).mono ball_subset_closedBall
  have he := eq_parameter_of_outerArc_comparison ht hts hle hnorm hηlim houter
    hφcont hφmap hΦlim htarget.1 htarget.2 heq
  exact ⟨he, pullback_lift_eqOn_of_eq_parameter hts he hηsurj heq⟩

end BelgianChocolate.HarmonicComparison

