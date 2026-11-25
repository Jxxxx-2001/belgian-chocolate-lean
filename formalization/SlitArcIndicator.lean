import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-! Holomorphic functions whose real parts give ordinary interior traces of
open circle arcs away from their two endpoints. -/

namespace BelgianChocolate.SlitArcIndicator

open Complex Set Metric Filter
open scoped ComplexConjugate Topology

private noncomputable def arcCayley (c z : ℂ) : ℂ := (c - conj c * z) / (1 - z)

private theorem one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ≠ 0 := by
  intro he
  have := sub_eq_zero.mp he
  rw [← this, norm_one] at hz
  exact (lt_irrefl _ hz)

private theorem arcCayley_im (c z : ℂ) :
    (arcCayley c z).im = c.im * (1 - ‖z‖ ^ 2) / normSq (1 - z) := by
  rw [arcCayley, div_im, ← normSq_eq_norm_sq]
  simp only [sub_re, sub_im, one_re, one_im, mul_re, mul_im, conj_re, conj_im,
    normSq_apply]
  ring

private theorem arcCayley_im_pos {c z : ℂ} (hc : 0 < c.im) (hz : ‖z‖ < 1) :
    0 < (arcCayley c z).im := by
  rw [arcCayley_im]
  exact div_pos (mul_pos hc (by nlinarith [norm_nonneg z]))
    (normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hz))

/-- A holomorphic function on the upper half-plane with real part equal to
the principal argument divided by pi. -/
noncomputable def upperArgument (z : ℂ) : ℂ :=
  -(Complex.I * Complex.log z) / (Real.pi : ℂ)

theorem upperArgument_re (z : ℂ) : (upperArgument z).re = z.arg / Real.pi := by
  rw [upperArgument, div_ofReal_re]
  simp [Complex.mul_re, Complex.log_im]

theorem differentiableAt_upperArgument {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ upperArgument z :=
  ((differentiableAt_log (Or.inr hz.ne')).const_mul I).neg.div_const _

private noncomputable def arcFunction (c z : ℂ) : ℂ := upperArgument (arcCayley c z)

private theorem arcFunction_re (c z : ℂ) :
    (arcFunction c z).re = (arcCayley c z).arg / Real.pi := by
  exact upperArgument_re _

private theorem differentiableOn_arcFunction {c : ℂ} (hc : 0 < c.im) :
    DifferentiableOn ℂ (arcFunction c) (ball 0 1) := by
  intro z hz
  have hn := mem_ball_zero_iff.mp hz
  have hC : DifferentiableAt ℂ (arcCayley c) z := by
    unfold arcCayley
    apply DifferentiableAt.div _ _ (one_sub_ne_zero_of_norm_lt_one hn) <;> fun_prop
  exact ((differentiableAt_upperArgument (arcCayley_im_pos hc hn)).comp z hC).differentiableWithinAt

theorem upperArgument_between {w : ℂ} (hw : 0 < w.im) :
    (upperArgument w).re ∈ Ioo (0 : ℝ) 1 := by
  have harg₀ : 0 < w.arg := by
    rw [arg_of_im_pos hw]
    apply Real.arccos_pos.mpr
    apply (div_lt_one (norm_pos_iff.mpr (fun h => by simp [h] at hw))).mpr
    have hs : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
      rw [← normSq_eq_norm_sq, normSq_apply]
    by_contra! h
    have hn := mul_nonneg (sub_nonneg.mpr h) (add_nonneg
      ((norm_nonneg w).trans h) (norm_nonneg w))
    nlinarith [mul_pos hw hw]
  have harg₁ := arg_lt_pi_iff.mpr (Or.inr hw.ne')
  rw [upperArgument_re]
  exact ⟨div_pos harg₀ Real.pi_pos, (div_lt_one Real.pi_pos).mpr harg₁⟩

/-- Real argument has an ordinary one-sided limit at every nonzero point
on the real axis approached through the upper half-plane. -/
theorem tendsto_upperArgument_re {ι : Type*} {l : Filter ι} {f : ι → ℂ} {z : ℂ}
    (ht : Tendsto f l (𝓝 z)) (him : ∀ᶠ w in l, 0 < (f w).im)
    (hz : 0 ≤ z.im) (hn : z ≠ 0) :
    Tendsto (fun w => (upperArgument (f w)).re) l (𝓝 (z.arg / Real.pi)) := by
  let V (w : ℂ) := Real.arccos (w.re / ‖w‖) / Real.pi
  have hv : ContinuousAt V z :=
    (Real.continuous_arccos.continuousAt.comp
      (continuous_re.continuousAt.div continuous_norm.continuousAt (norm_ne_zero_iff.mpr hn))).div_const _
  have he : V z = z.arg / Real.pi := by
    unfold V
    rw [arg_of_im_nonneg_of_ne_zero hz hn]
  rw [← he]
  apply Tendsto.congr' _ (hv.tendsto.comp ht)
  filter_upwards [him] with w hw
  rw [upperArgument_re, arg_of_im_pos hw]
  rfl

private theorem arcFunction_tendsto {c z : ℂ} (hc : 0 < c.im) (hz : ‖z‖ = 1)
    (hz₁ : z ≠ 1) (hn : arcCayley c z ≠ 0) :
    Tendsto (fun w => (arcFunction c w).re) (𝓝[ball 0 1] z)
      (𝓝 ((arcCayley c z).arg / Real.pi)) := by
  have hC : ContinuousAt (arcCayley c) z := by
    unfold arcCayley
    apply ContinuousAt.div _ _ (sub_ne_zero.mpr hz₁.symm) <;> fun_prop
  apply tendsto_upperArgument_re hC.continuousWithinAt.tendsto _ _ hn
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact arcCayley_im_pos hc (mem_ball_zero_iff.mp hw)
  · rw [arcCayley_im, hz]
    simp

private noncomputable def cis (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * I)

private theorem cis_re (x : ℝ) : (cis x).re = Real.cos x := by simp [cis, Complex.exp_re]
private theorem cis_im (x : ℝ) : (cis x).im = Real.sin x := by simp [cis, Complex.exp_im]
private theorem norm_cis (x : ℝ) : ‖cis x‖ = 1 := by simp [cis, Complex.norm_exp]

private theorem cis_add (x y : ℝ) : cis (x + y) = cis x * cis y := by
  simp only [cis, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem cis_double (x : ℝ) : cis (2 * x) = cis x ^ 2 := by
  rw [two_mul, cis_add, pow_two]

private theorem cis_two_pi : cis (2 * Real.pi) = 1 := by
  apply Complex.ext <;> simp [cis_re, cis_im]

private theorem cis_double_ne_one {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) : cis (2*x) ≠ 1 := by
  intro he
  have hre := congrArg Complex.re he
  rw [cis_double, pow_two, Complex.mul_re, cis_re, cis_im, one_re] at hre
  nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2]

private theorem arcCayley_cis {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) (θ : ℝ) :
    arcCayley (cis θ) (cis (2*x)) = ((Real.sin (x-θ) / Real.sin x : ℝ) : ℂ) := by
  have hs := Real.sin_sq_add_cos_sq x
  have hsp := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hr₂ : (2 : ℂ).re = 2 := by norm_num
  have hi₂ : (2 : ℂ).im = 0 := by norm_num
  have hden : 1 - cis (2*x) = (-2 * (Real.sin x : ℂ) * I) * cis x := by
    rw [cis_double, pow_two]
    apply Complex.ext
    · simp only [sub_re, one_re, mul_re, mul_im, cis_re, cis_im, neg_re, hr₂,
        ofReal_re, ofReal_im, I_re, I_im, neg_im, hi₂]
      linear_combination -hs
    · simp only [sub_im, one_im, mul_re, mul_im, cis_re, cis_im, neg_re, hr₂,
        ofReal_re, ofReal_im, I_re, I_im, neg_im, hi₂]
      ring
  have hnum : cis θ - conj (cis θ) * cis (2*x) =
      (2 * (Real.sin (θ-x) : ℂ) * I) * cis x := by
    rw [cis_double, pow_two, Real.sin_sub]
    apply Complex.ext
    · simp only [sub_re, mul_re, mul_im, cis_re, cis_im, conj_re, conj_im, hr₂,
        ofReal_re, ofReal_im, I_re, I_im, hi₂]
      linear_combination -Real.cos θ * hs
    · simp only [sub_im, mul_re, mul_im, cis_re, cis_im, conj_re, conj_im, hr₂,
        ofReal_re, ofReal_im, I_re, I_im, hi₂]
      linear_combination -Real.sin θ * hs
  unfold arcCayley
  apply (div_eq_iff (sub_ne_zero.mpr (cis_double_ne_one hx).symm)).mpr
  rw [hnum, hden, show x-θ = -(θ-x) by ring, Real.sin_neg]
  push_cast only [Complex.ofReal_neg, Complex.ofReal_div]
  have hsp' : (Real.sin x : ℂ) ≠ 0 := by exact_mod_cast hsp.ne'
  field_simp [hsp']

/-- The positively oriented open arc starting at `u` and sweeping angle
`2 * θ`. The intended parameters have `‖u‖ = 1` and `0 < θ < π`. -/
noncomputable def openArc (u : ℂ) (θ : ℝ) : Set ℂ :=
  (fun x : ℝ => u * circleMap 0 1 (2*x)) '' Ioo 0 θ

private theorem baseArc_eq (θ : ℝ) :
    openArc 1 θ = (fun x : ℝ => cis (2*x)) '' Ioo 0 θ := by
  simp [openArc, cis, circleMap_zero]

private theorem exists_cis_double {z : ℂ} (hz : ‖z‖ = 1) (hz₁ : z ≠ 1) :
    ∃ x ∈ Ioo (0 : ℝ) Real.pi, z = cis (2*x) := by
  have he : cis z.arg = z := by simpa [cis, hz] using Complex.norm_mul_exp_arg_mul_I z
  have ha : z.arg ≠ 0 := by
    intro h
    rw [h] at he
    exact hz₁ (by simpa [cis] using he.symm)
  rcases lt_or_gt_of_ne ha with hn | hp
  · refine ⟨(z.arg + 2 * Real.pi)/2, ⟨?_, ?_⟩, ?_⟩
    · linarith [neg_pi_lt_arg z, Real.pi_pos]
    · linarith
    · rw [show 2 * ((z.arg + 2 * Real.pi) / 2) = z.arg + 2 * Real.pi by ring,
        cis_add, cis_two_pi, mul_one, he]
  · refine ⟨z.arg / 2, ⟨by positivity, ?_⟩, ?_⟩
    · linarith [arg_le_pi z, Real.pi_pos]
    · rw [show 2 * (z.arg / 2) = z.arg by ring, he]

/-- Every ordered pair of distinct unit-circle points specifies an oriented
open arc by its positive sweep. -/
theorem exists_openArc_parameter {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : u ≠ v) : ∃ θ ∈ Ioo (0 : ℝ) Real.pi, v = u * circleMap 0 1 (2*θ) := by
  have hnorm : ‖conj u * v‖ = 1 := by simp [hu, hv]
  have hunit : u * conj u = 1 := by rw [Complex.mul_conj', hu]; norm_num
  have hne : conj u * v ≠ 1 := by
    intro he
    exact huv (by simpa only [← mul_assoc, hunit, one_mul, mul_one] using
      (congrArg (u * ·) he).symm)
  obtain ⟨θ, hθ, he⟩ := exists_cis_double hnorm hne
  refine ⟨θ, hθ, ?_⟩
  simpa only [circleMap_zero, Complex.ofReal_one, one_mul, cis, ← mul_assoc, hunit] using
    congrArg (u * ·) he

private theorem baseArc_tendsto {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) {z : ℂ}
    (hz : ‖z‖ = 1) (h₀ : z ≠ 1) (h₁ : z ≠ cis (2*θ)) :
    Tendsto (fun w => (arcFunction (cis θ) w).re) (𝓝[ball 0 1] z)
      (𝓝 ((openArc 1 θ).indicator (fun _ => (1 : ℝ)) z)) := by
  classical
  have hc : 0 < (cis θ).im := by rw [cis_im]; exact Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  obtain ⟨x, hx, hex⟩ := exists_cis_double hz h₀
  have hne : x ≠ θ := fun h => h₁ (h ▸ hex)
  have hformula := hex.symm ▸ arcCayley_cis hx θ
  have hxsign (u : ℝ) (hu : u ∈ Ioo 0 Real.pi) :
      0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2
  have hneg (hlt : x < θ) : Real.sin (x - θ) / Real.sin x < 0 :=
    div_neg_of_neg_of_pos
      (Real.sin_neg_of_neg_of_neg_pi_lt (sub_neg.mpr hlt) (by linarith [hx.1, hθ.2]))
      (hxsign x hx)
  have hpos (hlt : θ < x) : 0 < Real.sin (x - θ) / Real.sin x :=
    div_pos (hxsign _ ⟨sub_pos.mpr hlt, by linarith [hx.2, hθ.1]⟩) (hxsign x hx)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm : z ∈ openArc 1 θ := by
      rw [baseArc_eq]
      exact ⟨x, ⟨hx.1, hlt⟩, hex.symm⟩
    have hnc : arcCayley (cis θ) z ≠ 0 := by
      rw [hformula]
      exact_mod_cast (hneg hlt).ne
    have he := arcFunction_tendsto hc hz h₀ hnc
    rw [indicator_of_mem hm]
    rwa [hformula, arg_ofReal_of_neg (hneg hlt), div_self Real.pi_ne_zero] at he
  · have hm : z ∉ openArc 1 θ := by
      rw [baseArc_eq]
      rintro ⟨y, hy, hyz⟩
      change cis (2*y) = z at hyz
      have hyπ : y ∈ Ioo 0 Real.pi := ⟨hy.1, hy.2.trans hθ.2⟩
      have hyneg : Real.sin (y - θ) / Real.sin y < 0 :=
        div_neg_of_neg_of_pos
          (Real.sin_neg_of_neg_of_neg_pi_lt (sub_neg.mpr hy.2) (by linarith [hy.1, hθ.2]))
          (hxsign y hyπ)
      have he : ((Real.sin (y-θ) / Real.sin y : ℝ) : ℂ) =
          ((Real.sin (x-θ) / Real.sin x : ℝ) : ℂ) := by
        rw [← arcCayley_cis hyπ θ, hyz, hformula]
      linarith [congrArg Complex.re he, hyneg, hpos hgt,
        Complex.ofReal_re (Real.sin (y-θ) / Real.sin y),
        Complex.ofReal_re (Real.sin (x-θ) / Real.sin x)]
    have hnc : arcCayley (cis θ) z ≠ 0 := by
      rw [hformula]
      exact_mod_cast (hpos hgt).ne'
    have he := arcFunction_tendsto hc hz h₀ hnc
    rw [indicator_of_notMem hm]
    rwa [hformula, arg_ofReal_of_nonneg (hpos hgt).le, zero_div] at he

/-- The indicator of an oriented open unit-circle arc is the real boundary
trace of a holomorphic function whose real part lies strictly between zero
and one inside the disk. The traces hold under unrestricted approaches from
inside the disk at every boundary point other than the two arc endpoints. -/
theorem exists_holomorphic_openArc_indicator {u : ℂ} (hu : ‖u‖ = 1) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, (H z).re ∈ Ioo (0 : ℝ) 1) ∧
      ∀ z ∈ sphere (0 : ℂ) 1, z ≠ u → z ≠ u * circleMap 0 1 (2*θ) →
        Tendsto (fun w => (H w).re) (𝓝[ball 0 1] z)
          (𝓝 ((openArc u θ).indicator (fun _ => (1 : ℝ)) z)) := by
  classical
  let rot (z : ℂ) := conj u * z
  have hrot (z : ℂ) : ‖rot z‖ = ‖z‖ := by simp [rot, hu]
  have hrot_ball : MapsTo rot (ball 0 1) (ball 0 1) := by
    intro z hz
    rwa [mem_ball_zero_iff, hrot, ← mem_ball_zero_iff]
  have hcu : conj u * u = 1 := by
    rw [mul_comm, Complex.mul_conj', hu]
    norm_num
  have hurot (z : ℂ) : u * rot z = z := by
    change u * (conj u * z) = z
    rw [← mul_assoc, mul_comm u _, hcu, one_mul]
  have hc : 0 < (cis θ).im := by rw [cis_im]; exact Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  refine ⟨arcFunction (cis θ) ∘ rot, (differentiableOn_arcFunction hc).comp (by fun_prop) hrot_ball,
    fun _ hz => upperArgument_between (arcCayley_im_pos hc (mem_ball_zero_iff.mp (hrot_ball hz))), ?_⟩
  intro z hz h₀ h₁
  have hzrot : ‖rot z‖ = 1 := by rw [hrot]; simpa [mem_sphere, dist_zero_right] using hz
  have hrot₀ : rot z ≠ 1 := by
    intro he
    apply h₀
    rw [← hurot z, he, mul_one]
  have hrot₁ : rot z ≠ cis (2*θ) := by
    intro he
    apply h₁
    rw [← hurot z, he]
    simp [circleMap_zero, cis]
  have hcont : Continuous rot := by fun_prop
  have ht : Tendsto rot (𝓝[ball 0 1] z) (𝓝[ball 0 1] (rot z)) :=
    (hcont.continuousWithinAt).tendsto_nhdsWithin hrot_ball
  have hm : rot z ∈ openArc 1 θ ↔ z ∈ openArc u θ := by
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      simpa only [one_mul, hurot] using congrArg (u * ·) hxe
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      simpa [rot, ← mul_assoc, hcu] using congrArg rot hxe
  have he := (baseArc_tendsto hθ hzrot hrot₀ hrot₁).comp ht
  simpa only [Function.comp_def, Set.indicator_apply, hm] using he

end BelgianChocolate.SlitArcIndicator
