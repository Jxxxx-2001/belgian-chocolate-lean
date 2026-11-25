import HarmonicRadialBound
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-! The analytic primitive used in the unit-disc comparison. -/

namespace BelgianChocolate.HarmonicComparison

open Complex Filter Metric Set Topology

/-- The normalized primitive of the holomorphic extension of `W(z) / z`. -/
theorem exists_comparisonPrimitive {W : ℂ → ℂ}
    (hW : DifferentiableOn ℂ W (ball 0 1)) (hW0 : W 0 = 0) :
    ∃ F : ℂ → ℂ, F 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasDerivAt F (dslope W 0 z) z) ∧
      (∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W z) := by
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hs := (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hzero)).2 hW
  obtain ⟨F, hF0, hF⟩ := hs.isExactOn_ball.with_val_at 0 0
  refine ⟨F, hF0, hF, ?_⟩
  intro z hz
  rw [(hF z hz).deriv]
  by_cases hz0 : z = 0
  · simp [hz0, hW0]
  · rw [dslope_of_ne _ hz0, slope_def_field]
    rw [hW0, sub_zero, sub_zero]
    field_simp

/-- Along a ray, the derivative of the imaginary part is the imaginary part of
`W` divided by the radius. -/
theorem hasDerivAt_radial_im {F W : ℂ → ℂ} {ξ : ℂ} {r : ℝ}
    (hr : r ≠ 0)
    (hF : DifferentiableAt ℂ F (r • ξ))
    (hW : (r • ξ) * deriv F (r • ξ) = W (r • ξ)) :
    HasDerivAt (fun s : ℝ ↦ (F (s • ξ)).im) ((W (r • ξ)).im / r) r := by
  have hscale : HasDerivAt (fun s : ℝ ↦ s • ξ) ξ r := by
    simpa using (hasDerivAt_id r).smul_const ξ
  have hFR : HasFDerivAt F
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv F (r • ξ))).restrictScalars ℝ)
      (r • ξ) := hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hchain := imCLM.hasFDerivAt.comp_hasDerivAt r (hFR.comp_hasDerivAt r hscale)
  refine hchain.congr_deriv ?_
  have him := congrArg Complex.im hW
  simp only [real_smul, mul_assoc, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero] at him
  apply (eq_div_iff hr).2
  change (ξ * deriv F (r • ξ)).im * r = (W (r • ξ)).im
  rw [mul_comm _ r]
  simpa only [real_smul, mul_im] using him

/-- On an interior circle, the angular derivative of the imaginary part is the
real part of the original function `W`. -/
theorem hasDerivAt_angular_im {F W : ℂ → ℂ} {r θ : ℝ}
    (hF : DifferentiableAt ℂ F (circleMap 0 r θ))
    (hW : circleMap 0 r θ * deriv F (circleMap 0 r θ) = W (circleMap 0 r θ)) :
    HasDerivAt (fun s : ℝ ↦ (F (circleMap 0 r s)).im) (W (circleMap 0 r θ)).re θ := by
  have hFR : HasFDerivAt F
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv F (circleMap 0 r θ))).restrictScalars ℝ)
      (circleMap 0 r θ) := hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hchain := imCLM.hasFDerivAt.comp_hasDerivAt θ
    (hFR.comp_hasDerivAt θ (hasDerivAt_circleMap 0 r θ))
  refine hchain.congr_deriv ?_
  change (circleMap 0 r θ * I * deriv F (circleMap 0 r θ)).im = _
  rw [mul_right_comm, hW]
  simp

/-- A real radial profile with an inward linear gap at its endpoint cannot have
derivatives bounded from below by arbitrarily small negative constants near that
endpoint. The proof uses only the mean value theorem. -/
theorem not_eventually_deriv_ge_of_radial_gap {d d' : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hcont : ContinuousOn d (Icc 0 1))
    (hderiv : ∀ r ∈ Ioo 0 1, HasDerivAt d (d' r) r)
    (hgap : ∀ r ∈ Ioo 0 1, a * (1 - r) ≤ d r - d 1) :
    ¬ (∀ ε > 0, ∃ b ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo b 1, -ε ≤ d' r) := by
  intro h
  obtain ⟨b, hb, hnear⟩ := h (a / 2) (by positivity)
  obtain ⟨r, hr, heq⟩ := exists_hasDerivAt_eq_slope d d' hb.2
    (hcont.mono (Icc_subset_Icc_left hb.1.le))
    (fun x hx ↦ hderiv x ⟨hb.1.trans hx.1, hx.2⟩)
  have hden : 0 < 1 - b := sub_pos.mpr hb.2
  have huv := (le_div_iff₀ hden).1 (heq ▸ hnear r hr)
  nlinarith [hgap b hb, mul_pos ha hden]

/-- Unit-disc comparison after the boundary data have been expressed radially:
at each boundary minimum of the imaginary part of the primitive, the radial
imaginary difference has lower limit at least zero. -/
theorem eqOn_zero_of_radialBoundaryComparison {F W : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hF0 : F 0 = 0)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, z * deriv F z = W z)
    (hcont : ContinuousOn (fun z ↦ (F z).im) (closedBall 0 1))
    (hboundary : ∀ ξ : ℂ, ‖ξ‖ = 1 →
      IsMinOn (fun z ↦ (F z).im) (closedBall 0 1) ξ →
      ∀ ε > 0, ∃ b ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo b 1, -ε ≤ (W (r • ξ)).im) :
    EqOn W (fun _ ↦ 0) (ball 0 1) := by
  let D : ℂ → ℝ := fun z ↦ (F z).im
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hclosedzero : (0 : ℂ) ∈ closedBall 0 1 := ball_subset_closedBall hzero
  obtain ⟨ξ, hξ, hmin⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMinOn ⟨0, hclosedzero⟩ hcont
  have hconst_of_inner_min (c : ℂ) (hc : c ∈ ball 0 1)
      (hmc : IsMinOn D (ball 0 1) c) : EqOn W (fun _ ↦ 0) (ball 0 1) := by
    let G : ℂ → ℂ := fun z ↦ Complex.exp (Complex.I * F z)
    have hG : DifferentiableOn ℂ G (ball 0 1) := (hF.const_mul Complex.I).cexp
    have hGnorm (z : ℂ) : ‖G z‖ = Real.exp (-D z) := by
      rw [Complex.norm_exp]
      congr 1
      simp [D, Complex.mul_re]
    have hGmax : IsMaxOn (norm ∘ G) (ball 0 1) c := by
      intro z hz
      change ‖G z‖ ≤ ‖G c‖
      rw [hGnorm, hGnorm, Real.exp_le_exp]
      exact neg_le_neg (hmc hz)
    have hGc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hG hc hGmax
    intro z hz
    have hdF := (hF.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hd := (hdF.const_mul Complex.I).cexp
    have hdeq : G =ᶠ[nhds z] (fun _ ↦ G c) :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds hz) hGc
    have hdz := hd.unique ((hasDerivAt_const z (G c)).congr_of_eventuallyEq hdeq)
    change G z * (Complex.I * deriv F z) = 0 at hdz
    have hdz' := (mul_eq_zero.mp hdz).resolve_left (Complex.exp_ne_zero _)
    have hdz'' := (mul_eq_zero.mp hdz').resolve_left Complex.I_ne_zero
    simpa [hdz''] using (hW z hz).symm
  by_cases hinner : ξ ∈ ball (0 : ℂ) 1
  · exact hconst_of_inner_min ξ hinner (fun z hz ↦ hmin (ball_subset_closedBall hz))
  have hξnorm : ‖ξ‖ = 1 := by
    rw [mem_closedBall_zero_iff] at hξ
    rw [mem_ball_zero_iff, not_lt] at hinner
    exact le_antisymm hξ hinner
  have hmle : D ξ ≤ 0 := by
    simpa [D, hF0] using hmin hclosedzero
  by_cases hm : D ξ = 0
  · apply hconst_of_inner_min 0 hzero
    intro z hz
    have hz' := hmin (ball_subset_closedBall hz)
    change D ξ ≤ D z at hz'
    simpa [D, hF0, hm] using (show 0 ≤ D z by linarith)
  have hmneg : D ξ < 0 := lt_of_le_of_ne hmle hm
  let a : ℝ := -D ξ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hnorm (r : ℝ) (hr : 0 ≤ r) : ‖r • ξ‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hξnorm, mul_one]
  have hmem (r : ℝ) (hr : r ∈ Ioo 0 1) : r • ξ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hnorm _ hr.1.le]
    exact hr.2
  let d : ℝ → ℝ := fun r ↦ D (r • ξ)
  have hdcont : ContinuousOn d (Icc 0 1) := by
    apply hcont.comp (continuous_id.smul continuous_const).continuousOn
    intro r hr
    change r • ξ ∈ closedBall (0 : ℂ) 1
    rw [mem_closedBall_zero_iff, hnorm _ hr.1]
    exact hr.2
  have hdderiv : ∀ r ∈ Ioo (0 : ℝ) 1,
      HasDerivAt d ((W (r • ξ)).im / r) r := by
    intro r hr
    exact hasDerivAt_radial_im hr.1.ne'
      (hF.differentiableAt (isOpen_ball.mem_nhds (hmem r hr))) (hW _ (hmem r hr))
  have hgap (r : ℝ) (hr : r ∈ Ioo 0 1) : a * (1 - r) ≤ d r - d 1 := by
    have hbound := BelgianChocolate.im_sub_lowerBound_ge_harnack hF hF0 hmneg
      (fun z hz ↦ hmin (ball_subset_closedBall hz)) (mem_ball_zero_iff.mp (hmem r hr))
    rw [hnorm _ hr.1.le] at hbound
    have hstep : a ≤ (-D ξ) / (1 + r) := by
      apply (le_div_iff₀ (by linarith [hr.1] : 0 < 1 + r)).2
      have ht := mul_nonneg ha.le (sub_nonneg.mpr hr.2.le)
      dsimp [a] at *
      nlinarith
    calc
      a * (1 - r) ≤ ((-D ξ) / (1 + r)) * (1 - r) :=
        mul_le_mul_of_nonneg_right hstep (by linarith [hr.2])
      _ = (1 - r) / (1 + r) * (-D ξ) := by ring
      _ ≤ d r - d 1 := by simpa [d] using hbound
  exfalso
  apply not_eventually_deriv_ge_of_radial_gap ha hdcont hdderiv hgap
  intro ε hε
  obtain ⟨b, hb, hnear⟩ := hboundary ξ hξnorm hmin (ε / 2) (by positivity)
  refine ⟨max b (1 / 2), ⟨lt_of_lt_of_le hb.1 (le_max_left _ _), ?_⟩, ?_⟩
  · exact max_lt hb.2 (by norm_num)
  · intro r hr
    have hbr := (le_max_left b (1 / 2)).trans_lt hr.1
    have hhalf := (le_max_right b (1 / 2)).trans_lt hr.1
    rw [le_div_iff₀ (by linarith : 0 < r)]
    nlinarith [hnear r ⟨hbr, hr.2⟩, mul_pos hε (sub_pos.mpr hhalf)]

end BelgianChocolate.HarmonicComparison
