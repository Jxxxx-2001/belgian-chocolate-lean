import HarmonicComparison
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace BelgianChocolate.HarmonicComparison

open Complex Filter Metric Set Topology

private theorem contracted_mem {z : ℂ} (hz : z ∈ closedBall 0 1) {r : ℝ}
    (hr : 0 ≤ r) (hr' : r < 1) : r • z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact (mul_le_of_le_one_right hr (mem_closedBall_zero_iff.mp hz)).trans_lt hr'

/-- Radial increments of the imaginary primitive are uniformly Lipschitz
on the outer half of each radius, including radii ending at the unit circle. -/
theorem radial_im_dist_le {F W : ℂ → ℂ} {M : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hW : ∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W z)
    (hM : ∀ z ∈ ball (0 : ℂ) 1, |(W z).im| ≤ M)
    {z : ℂ} (hz : z ∈ closedBall 0 1) {r s : ℝ}
    (hr : r ∈ Ico (1/2 : ℝ) 1) (hs : s ∈ Ico (1/2 : ℝ) 1) :
    dist (F (r • z)).im (F (s • z)).im ≤ (2*M) * dist r s := by
  let d : ℝ → ℝ := fun t ↦ (F (t • z)).im
  let d' : ℝ → ℝ := fun t ↦ (W (t • z)).im / t
  have hmem (t : ℝ) (ht : t ∈ Ico (1/2 : ℝ) 1) : t • z ∈ ball (0 : ℂ) 1 :=
    contracted_mem hz (by linarith [ht.1]) ht.2
  have hder (t : ℝ) (ht : t ∈ Ico (1/2 : ℝ) 1) : HasDerivAt d (d' t) t :=
    hasDerivAt_radial_im (by linarith [ht.1])
      (hF.differentiableAt (isOpen_ball.mem_nhds (hmem t ht))) (hW _ (hmem t ht))
  have hbound (t : ℝ) (ht : t ∈ Ico (1/2 : ℝ) 1) : ‖d' t‖ ≤ 2*M := by
    have hpos : 0 < t := by linarith [ht.1]
    have hb := hM _ (hmem t ht)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hb
    rw [Real.norm_eq_abs, show d' t = _ from rfl, abs_div, abs_of_pos hpos,
      div_le_iff₀ hpos]
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr ht.1)]
  simpa only [dist_eq_norm] using
    (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht ↦ (hder t ht).hasDerivWithinAt) hbound (convex_Ico _ _) hs hr)

/-- The imaginary part of the primitive has a continuous closed-disc trace
when the imaginary part of `z * deriv F z` is bounded. -/
theorem exists_continuousOn_im_extension {F W : ℂ → ℂ} {M : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hW : ∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W z)
    (hM : ∀ z ∈ ball (0 : ℂ) 1, |(W z).im| ≤ M) :
    ∃ D : ℂ → ℝ, ContinuousOn D (closedBall 0 1) ∧
      EqOn D (fun z ↦ (F z).im) (ball 0 1) := by
  let r : ℕ → ℝ := fun n ↦ 1 - (1/2 : ℝ) ^ (n+1)
  have hr (n : ℕ) : r n ∈ Ico (1/2 : ℝ) 1 := by
    have hp : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp' : 0 < (1/2 : ℝ)^n := by positivity
    dsimp [r]
    rw [pow_succ]
    constructor <;> linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ))
      (by norm_num : (1/2 : ℝ) < 1)
    simpa [r, pow_succ] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hp.mul (tendsto_const_nhds (x := (1/2 : ℝ))))
  let A : ℕ → ℂ → ℝ := fun n z ↦ (F (r n • z)).im
  have hAc (n : ℕ) : ContinuousOn (A n) (closedBall 0 1) := by
    have hc : Continuous (fun z : ℂ ↦ r n • z) := continuous_id.const_smul (r n)
    have hm : MapsTo (fun z : ℂ ↦ r n • z) (closedBall 0 1) (ball 0 1) :=
      fun z hz ↦ contracted_mem hz (by linarith [(hr n).1]) (hr n).2
    exact Complex.continuous_im.comp_continuousOn (hF.continuousOn.comp hc.continuousOn hm)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (mem_ball_self zero_lt_one))
  have hAu : UniformCauchySeqOn A atTop (closedBall 0 1) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    have hden : 0 < 2*M+1 := by linarith
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hrlim.cauchySeq (ε/(2*M+1)) (div_pos hε hden)
    refine ⟨N, fun m hm n hn z hz ↦ ?_⟩
    have hb := radial_im_dist_le hF hW hM hz (hr m) (hr n)
    have hd := (lt_div_iff₀ hden).mp (hN m hm n hn)
    exact hb.trans_lt (by nlinarith [dist_nonneg (x := r m) (y := r n)])
  let D : ℂ → ℝ := fun z ↦ limUnder atTop (fun n ↦ A n z)
  have hD (z : ℂ) (hz : z ∈ closedBall 0 1) : Tendsto (fun n ↦ A n z) atTop (𝓝 (D z)) :=
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hAu.cauchySeq hz))
  refine ⟨D, (hAu.tendstoUniformlyOn_of_tendsto hD).continuousOn
    (Eventually.of_forall hAc).frequently, ?_⟩
  intro z hz
  have hzlim : Tendsto (fun n ↦ r n • z) atTop (𝓝 z) := by
    simpa using hrlim.smul_const z
  exact tendsto_nhds_unique (hD z (ball_subset_closedBall hz))
    (Complex.continuous_im.continuousAt.tendsto.comp
      ((hF.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt.tendsto.comp hzlim))

/-- A continuous real trace can be supplied independently of the arbitrary
values chosen for the complex primitive outside its domain of holomorphy. -/
theorem eqOn_zero_of_traceBoundaryComparison {F W : ℂ → ℂ} {D : ℂ → ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hF0 : F 0 = 0)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W z)
    (hD : ContinuousOn D (closedBall 0 1)) (hDF : EqOn D (fun z ↦ (F z).im) (ball 0 1))
    (hb : ∀ ξ : ℂ, ‖ξ‖ = 1 → IsMinOn D (closedBall 0 1) ξ →
      ∀ ε > 0, ∃ b ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo b 1, -ε ≤ (W (r • ξ)).im) :
    EqOn W (fun _ ↦ 0) (ball 0 1) := by
  let G : ℂ → ℂ := fun z ↦ ⟨(F z).re, D z⟩
  have hGF : EqOn G F (ball 0 1) := fun z hz ↦ Complex.ext rfl (hDF hz)
  have hG : DifferentiableOn ℂ G (ball 0 1) := hF.congr hGF
  apply eqOn_zero_of_radialBoundaryComparison hG
    ((hGF (mem_ball_self zero_lt_one)).trans hF0) _ hD hb
  intro z hz
  have he : G =ᶠ[𝓝 z] F := Filter.mem_of_superset (isOpen_ball.mem_nhds hz) hGF
  rw [he.deriv_eq]
  exact hW z hz

/-- It suffices to check boundary comparisons on a continuous trace of the
normalized primitive. Boundedness of the imaginary part constructs that trace. -/
theorem eqOn_zero_of_boundedIm_boundaryComparison {W : ℂ → ℂ} {M : ℝ}
    (hW : DifferentiableOn ℂ W (ball 0 1)) (hW0 : W 0 = 0)
    (hM : ∀ z ∈ ball (0 : ℂ) 1, |(W z).im| ≤ M)
    (hb : ∀ (F : ℂ → ℂ) (D : ℂ → ℝ), F 0 = 0 →
      (∀ z ∈ ball (0 : ℂ) 1, HasDerivAt F (dslope W 0 z) z) →
      (∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W z) →
      ContinuousOn D (closedBall 0 1) → EqOn D (fun z ↦ (F z).im) (ball 0 1) →
      ∀ ξ : ℂ, ‖ξ‖ = 1 → IsMinOn D (closedBall 0 1) ξ →
        ∀ ε > 0, ∃ b ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo b 1, -ε ≤ (W (r • ξ)).im) :
    EqOn W (fun _ ↦ 0) (ball 0 1) := by
  obtain ⟨F, hF0, hdF, hFW⟩ := exists_comparisonPrimitive hW hW0
  have hF : DifferentiableOn ℂ F (ball 0 1) :=
    fun z hz ↦ (hdF z hz).differentiableAt.differentiableWithinAt
  obtain ⟨D, hD, hDF⟩ := exists_continuousOn_im_extension hF hFW hM
  exact eqOn_zero_of_traceBoundaryComparison hF hF0 hFW hD hDF (hb F D hF0 hdF hFW hD hDF)

/-- At a point of one-sided continuity of the real part of W, the angular
derivative of the primitive trace equals that real part. -/
theorem hasDerivAt_angular_trace {F W : ℂ → ℂ} {D : ℂ → ℝ} {θ : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hW : ∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W z)
    (hD : ContinuousOn D (closedBall 0 1))
    (hDF : EqOn D (fun z ↦ (F z).im) (ball 0 1))
    (hcW : ContinuousWithinAt (fun z ↦ (W z).re) (closedBall 0 1) (circleMap 0 1 θ)) :
    HasDerivAt (fun t ↦ D (circleMap 0 1 t)) (W (circleMap 0 1 θ)).re θ := by
  let p := 𝓝[<] (1 : ℝ)
  have hp : Tendsto id p (𝓝 (1 : ℝ)) := nhdsWithin_le_nhds
  have hrad : ∀ᶠ r : ℝ in p, r ∈ Ioo 0 1 := by
    filter_upwards [hp.eventually_const_lt (by norm_num : (0:ℝ) < 1),
      self_mem_nhdsWithin (s := Iio (1 : ℝ))] with r h₀ h₁
    exact ⟨h₀,h₁⟩
  have hinner (r : ℝ) (hr : r ∈ Ioo 0 1) (t : ℝ) : circleMap 0 r t ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, abs_of_pos hr.1] using hr.2
  have hpolar : Continuous (fun q : ℝ × ℝ ↦ circleMap 0 q.1 q.2) := by
    unfold circleMap
    fun_prop
  have hcircle (t : ℝ) : ContinuousAt (circleMap 0 1) t :=
    (hasDerivAt_circleMap 0 1 t).continuousAt
  have hjoin : Tendsto (fun q : ℝ × ℝ ↦ circleMap 0 q.1 q.2)
      (p ×ˢ 𝓝 θ) (𝓝[closedBall 0 1] (circleMap 0 1 θ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · apply (hpolar.continuousAt (x := ((1 : ℝ), θ))).tendsto.mono_left
      rw [nhds_prod_eq]
      exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
    · filter_upwards [tendsto_fst.eventually hrad] with q hq
      exact ball_subset_closedBall (hinner _ hq _)
  have hboundary : Tendsto (circleMap 0 1) (𝓝 θ) (𝓝[closedBall 0 1] (circleMap 0 1 θ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(hcircle θ).tendsto, Eventually.of_forall
      (circleMap_mem_closedBall 0 (by norm_num : (0:ℝ) ≤ 1))⟩
  apply hasDerivAt_of_tendstoUniformlyOnFilter
    (f := fun r t : ℝ ↦ (F (circleMap 0 r t)).im)
    (f' := fun r t : ℝ ↦ (W (circleMap 0 r t)).re)
    (g' := fun t : ℝ ↦ (W (circleMap 0 1 t)).re) (l := p)
  · exact tendstoUniformlyOnFilter_iff_tendsto.mpr
      (((hcW.tendsto.comp (hboundary.comp tendsto_snd)).prodMk_nhds (hcW.tendsto.comp hjoin)).mono_right
        (nhds_le_uniformity _))
  · filter_upwards [tendsto_fst.eventually hrad] with q hq
    exact hasDerivAt_angular_im (hF.differentiableAt (isOpen_ball.mem_nhds (hinner _ hq _)))
      (hW _ (hinner _ hq _))
  · apply Eventually.of_forall
    intro t
    have hb := circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0:ℝ) ≤ 1) t
    have ht : Tendsto (fun r : ℝ ↦ circleMap 0 r t) p
        (𝓝[closedBall 0 1] (circleMap 0 1 t)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : Continuous (fun r : ℝ ↦ circleMap 0 r t) :=
          by unfold circleMap; fun_prop
        exact (hc.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [hrad] with r hr using ball_subset_closedBall (hinner _ hr _)
    have hDt : Tendsto (fun r : ℝ ↦ D (circleMap 0 r t)) p (𝓝 (D (circleMap 0 1 t))) :=
      (hD _ hb).tendsto.comp ht
    apply hDt.congr'
    filter_upwards [hrad] with r hr using hDF (hinner _ hr _)

/-- At a minimum on a graph arc the angular derivative vanishes, so the
boundary real parts of the compared functions agree. -/
theorem re_eq_zero_of_trace_isMinOn {F W : ℂ → ℂ} {D : ℂ → ℝ} {θ : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hW : ∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W z)
    (hD : ContinuousOn D (closedBall 0 1)) (hDF : EqOn D (fun z ↦ (F z).im) (ball 0 1))
    (hcW : ContinuousWithinAt (fun z ↦ (W z).re) (closedBall 0 1) (circleMap 0 1 θ))
    (hm : IsMinOn D (closedBall 0 1) (circleMap 0 1 θ)) :
    (W (circleMap 0 1 θ)).re = 0 := by
  have hmin : IsLocalMin (fun t ↦ D (circleMap 0 1 t)) θ :=
    Eventually.of_forall fun t ↦ hm (circleMap_mem_closedBall _ (by norm_num) t)
  exact hmin.hasDerivAt_eq_zero (hasDerivAt_angular_trace hF hW hD hDF hcW)

/-- A same-graph boundary point at a minimum has zero imaginary difference.
Only relative continuity at that point and the two graph identities are used. -/
theorem im_eq_zero_of_sameGraph_min {F W₁ W₀ : ℂ → ℂ} {D : ℂ → ℝ} {ξ : ℂ}
    (hξ : ‖ξ‖ = 1) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hW : ∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W₁ z - W₀ z)
    (hD : ContinuousOn D (closedBall 0 1)) (hDF : EqOn D (fun z ↦ (F z).im) (ball 0 1))
    (hc₁ : ContinuousWithinAt W₁ (closedBall 0 1) ξ)
    (hc₀ : ContinuousWithinAt W₀ (closedBall 0 1) ξ)
    (hm : IsMinOn D (closedBall 0 1) ξ) {v : ℝ → ℝ}
    (h₁ : (W₁ ξ).im = v (W₁ ξ).re) (h₀ : (W₀ ξ).im = v (W₀ ξ).re) :
    (W₁ ξ - W₀ ξ).im = 0 := by
  have hξarg : circleMap 0 1 ξ.arg = ξ := by
    simpa only [circleMap_zero, ← hξ] using Complex.norm_mul_exp_arg_mul_I ξ
  have hc : ContinuousWithinAt (fun z ↦ (W₁ z - W₀ z).re) (closedBall 0 1) ξ :=
    Complex.continuous_re.continuousAt.comp_continuousWithinAt (hc₁.sub hc₀)
  have he := re_eq_zero_of_trace_isMinOn (θ := ξ.arg) hF hW hD hDF (by simpa only [hξarg] using hc) (by simpa only [hξarg] using hm)
  rw [hξarg, Complex.sub_re, sub_eq_zero] at he
  rw [Complex.sub_im, h₁, h₀, he, sub_self]

/-- At a minimum on a common boundary graph, the interior imaginary difference
obeys the lower bound in the radial comparison. -/
theorem graph_arc_radial_lowerBound {F W₁ W₀ : ℂ → ℂ} {D : ℂ → ℝ} {ξ : ℂ}
    (hξ : ‖ξ‖ = 1) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hW : ∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W₁ z - W₀ z)
    (hD : ContinuousOn D (closedBall 0 1)) (hDF : EqOn D (fun z ↦ (F z).im) (ball 0 1))
    (hc₁ : ContinuousWithinAt W₁ (closedBall 0 1) ξ)
    (hc₀ : ContinuousWithinAt W₀ (closedBall 0 1) ξ)
    (hm : IsMinOn D (closedBall 0 1) ξ) {v : ℝ → ℝ}
    (h₁ : (W₁ ξ).im = v (W₁ ξ).re) (h₀ : (W₀ ξ).im = v (W₀ ξ).re) :
    ∀ ε > 0, ∃ b ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo b 1, -ε ≤ (W₁ (r • ξ) - W₀ (r • ξ)).im := by
  have hi := im_eq_zero_of_sameGraph_min hξ hF hW hD hDF hc₁ hc₀ hm h₁ h₀
  have hc : ContinuousWithinAt (fun z ↦ (W₁ z - W₀ z).im) (closedBall 0 1) ξ :=
    Complex.continuous_im.continuousAt.comp_continuousWithinAt (hc₁.sub hc₀)
  intro ε hε
  have hnear := Metric.continuousWithinAt_iff.mp hc ε hε
  obtain ⟨δ, hδ, hclose⟩ := hnear
  refine ⟨max (1/2) (1-δ/2), ⟨lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    max_lt (by norm_num) (by linarith)⟩, ?_⟩
  intro r hr
  have hr₀ : 0 ≤ r := by linarith [(le_max_left (1/2:ℝ) (1-δ/2)).trans_lt hr.1]
  have hrδ := (le_max_right (1/2:ℝ) (1-δ/2)).trans_lt hr.1
  have hrmem : r • ξ ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr₀,
      hξ, mul_one] using hr.2.le
  have hrdist : dist (r • ξ) ξ < δ := by
    rw [dist_eq_norm, show r • ξ - ξ = (r - 1) • ξ by rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs, hξ, mul_one,
      abs_of_nonpos (by linarith [hr.2] : r - 1 ≤ 0)]
    linarith
  have hl := hclose hrmem hrdist
  change dist (W₁ (r • ξ) - W₀ (r • ξ)).im (W₁ ξ - W₀ ξ).im < ε at hl
  rw [hi, Real.dist_eq, sub_zero, abs_lt] at hl
  exact hl.1.le

end BelgianChocolate.HarmonicComparison
