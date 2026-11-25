import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import MarkedRealAxisSlice
import Mathlib.Tactic

namespace BelgianChocolate.ComparisonGraph

open Filter Set
open scoped Topology

noncomputable def a (θ : ℝ) : ℝ := Real.sqrt (θ * (Real.pi - θ))

noncomputable def realCoordinate (θ : ℝ) : ℝ := Real.artanh (Real.cos θ / Real.cosh (a θ))

noncomputable def imagCoordinate (θ : ℝ) : ℝ := Real.arctan (Real.sin θ / Real.sinh (a θ))

private theorem a_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) : 0 < a θ :=
  Real.sqrt_pos.2 (mul_pos hθ.1 (sub_pos.2 hθ.2))

private theorem ratio_nonneg {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    0 ≤ Real.sin θ / Real.sinh (a θ) :=
  div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le)
    (Real.sinh_pos_iff.mpr (a_pos hθ)).le

theorem imagCoordinate_nonneg {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    0 ≤ imagCoordinate θ :=
  Real.arctan_nonneg.mpr (ratio_nonneg hθ)

private theorem ratio_le_sqrt_div {s t n : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hn : n ≤ s) : n / Real.sinh (Real.sqrt (s * t)) ≤ Real.sqrt s / Real.sqrt t := by
  have hroot : 0 < Real.sqrt (s * t) := Real.sqrt_pos.2 (mul_pos hs ht)
  have hbound : Real.sqrt (s * t) ≤ Real.sinh (Real.sqrt (s * t)) :=
    le_of_not_gt (fun h => (not_lt_of_ge hroot.le) (Real.sinh_lt_self_iff.mp h))
  calc
    n / Real.sinh (Real.sqrt (s * t)) ≤ s / Real.sinh (Real.sqrt (s * t)) :=
      div_le_div_of_nonneg_right hn (Real.sinh_pos_iff.mpr hroot).le
    _ ≤ s / Real.sqrt (s * t) := div_le_div_of_nonneg_left hs.le hroot hbound
    _ = Real.sqrt s / Real.sqrt t := by
      rw [Real.sqrt_mul hs.le]
      have hsr := Real.sqrt_pos.2 hs
      have htr := Real.sqrt_pos.2 ht
      field_simp
      nlinarith [Real.sq_sqrt hs.le]

private theorem sin_le_self (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x := by
  calc
    Real.sin x ≤ |Real.sin x| := le_abs_self _
    _ ≤ |x| := Real.abs_sin_le_abs
    _ = x := abs_of_nonneg hx

private theorem tendsto_ratio_zero :
    Tendsto (fun θ => Real.sin θ / Real.sinh (a θ)) (𝓝[Ioo 0 Real.pi] 0) (𝓝 0) := by
  have hupper : ContinuousAt (fun θ : ℝ => Real.sqrt θ / Real.sqrt (Real.pi - θ)) 0 := by
    fun_prop (disch := simpa using (Real.sqrt_ne_zero'.2 Real.pi_pos))
  have hlimit := hupper.continuousWithinAt (s := Ioo 0 Real.pi)
  simp only [ContinuousWithinAt, Real.sqrt_zero, zero_div] at hlimit
  apply squeeze_zero' ?_ ?_ hlimit
  · filter_upwards [self_mem_nhdsWithin] with θ hθ using ratio_nonneg hθ
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact ratio_le_sqrt_div hθ.1 (sub_pos.2 hθ.2) (sin_le_self θ hθ.1.le)

private theorem tendsto_ratio_pi :
    Tendsto (fun θ => Real.sin θ / Real.sinh (a θ)) (𝓝[Ioo 0 Real.pi] Real.pi) (𝓝 0) := by
  have hupper : ContinuousAt (fun θ : ℝ => Real.sqrt (Real.pi - θ) / Real.sqrt θ) Real.pi := by
    fun_prop (disch := positivity)
  have hlimit := hupper.continuousWithinAt (s := Ioo 0 Real.pi)
  simp only [ContinuousWithinAt, sub_self, Real.sqrt_zero, zero_div] at hlimit
  apply squeeze_zero' ?_ ?_ hlimit
  · filter_upwards [self_mem_nhdsWithin] with θ hθ using ratio_nonneg hθ
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hsin : Real.sin θ ≤ Real.pi - θ := by
      rw [← Real.sin_pi_sub θ]
      exact sin_le_self _ (sub_nonneg.2 hθ.2.le)
    simpa only [a, mul_comm θ] using ratio_le_sqrt_div (sub_pos.2 hθ.2) hθ.1 hsin

theorem tendsto_imagCoordinate_zero :
    Tendsto imagCoordinate (𝓝[Ioo 0 Real.pi] 0) (𝓝 0) := by
  unfold imagCoordinate
  simpa [Function.comp_def] using
    Real.continuous_arctan.continuousAt.tendsto.comp tendsto_ratio_zero

theorem tendsto_imagCoordinate_pi :
    Tendsto imagCoordinate (𝓝[Ioo 0 Real.pi] Real.pi) (𝓝 0) := by
  unfold imagCoordinate
  simpa [Function.comp_def] using
    Real.continuous_arctan.continuousAt.tendsto.comp tendsto_ratio_pi

private noncomputable def cosRatio (θ : ℝ) : ℝ := Real.cos θ / Real.cosh (a θ)

private theorem cosRatio_reflect (θ : ℝ) : cosRatio (Real.pi - θ) = -cosRatio θ := by
  have ha : a (Real.pi - θ) = a θ := by
    unfold a
    congr 1
    ring
  simp [cosRatio, ha, Real.cos_pi_sub, neg_div]

private theorem cosRatio_decreases_left {x y : ℝ}
    (hx : 0 ≤ x) (hy : y ≤ Real.pi / 2) (hxy : x < y) :
    cosRatio y < cosRatio x := by
  have hy0 : 0 ≤ y := hx.trans hxy.le
  have hyp : y ≤ Real.pi := by linarith [Real.pi_pos]
  have hxp : x ≤ Real.pi := hxy.le.trans hyp
  have hcos := Real.strictAntiOn_cos (show x ∈ Icc 0 Real.pi from ⟨hx, hxp⟩)
    (show y ∈ Icc 0 Real.pi from ⟨hy0, hyp⟩) hxy
  have hcosy : 0 ≤ Real.cos y := by
    rw [← Real.cos_pi_div_two]
    exact Real.strictAntiOn_cos.antitoneOn
      (show y ∈ Icc 0 Real.pi from ⟨hy0, hyp⟩)
      (show Real.pi / 2 ∈ Icc 0 Real.pi from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) hy
  have ha : a x ≤ a y := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg (show 0 ≤ y - x by linarith)
      (show 0 ≤ Real.pi - x - y by linarith)]
  have hcosh : Real.cosh (a x) ≤ Real.cosh (a y) :=
    Real.cosh_le_cosh.2 (by
      simpa only [a, abs_of_nonneg (Real.sqrt_nonneg _)] using ha)
  calc
    cosRatio y ≤ Real.cos y / Real.cosh (a x) :=
      div_le_div_of_nonneg_left hcosy (Real.cosh_pos _) hcosh
    _ < cosRatio x :=
      div_lt_div_of_pos_right hcos (Real.cosh_pos _)

private theorem cosRatio_decreases_right {x y : ℝ}
    (hx : Real.pi / 2 ≤ x) (hy : y ≤ Real.pi) (hxy : x < y) :
    cosRatio y < cosRatio x := by
  have h := cosRatio_decreases_left (x := Real.pi - y) (y := Real.pi - x)
    (by linarith) (by linarith) (by linarith)
  rw [cosRatio_reflect, cosRatio_reflect] at h
  linarith

private theorem cosRatio_decreases : StrictAntiOn cosRatio (Icc 0 Real.pi) := by
  intro x hx y hy hxy
  by_cases hyl : y ≤ Real.pi / 2
  · exact cosRatio_decreases_left hx.1 hyl hxy
  by_cases hxr : Real.pi / 2 ≤ x
  · exact cosRatio_decreases_right hxr hy.2 hxy
  · exact (cosRatio_decreases_right (x := Real.pi / 2) le_rfl hy.2 (lt_of_not_ge hyl)).trans
      (cosRatio_decreases_left (y := Real.pi / 2) hx.1 le_rfl (lt_of_not_ge hxr))

private theorem cosRatio_zero : cosRatio 0 = 1 := by simp [cosRatio, a]

private theorem cosRatio_pi : cosRatio Real.pi = -1 := by simp [cosRatio, a]

private theorem cosRatio_mem {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    cosRatio θ ∈ Ioo (-1) 1 := by
  have hl := cosRatio_decreases (show θ ∈ Icc 0 Real.pi from ⟨hθ.1.le, hθ.2.le⟩)
    (show Real.pi ∈ Icc 0 Real.pi from ⟨Real.pi_pos.le, le_rfl⟩) hθ.2
  have hu := cosRatio_decreases (show 0 ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show θ ∈ Icc 0 Real.pi from ⟨hθ.1.le, hθ.2.le⟩) hθ.1
  exact ⟨by simpa only [cosRatio_pi] using hl, by simpa only [cosRatio_zero] using hu⟩

theorem realCoordinate_strictAntiOn : StrictAntiOn realCoordinate (Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  exact Real.strictMonoOn_artanh (cosRatio_mem hy) (cosRatio_mem hx)
    (cosRatio_decreases ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy)

theorem realCoordinate_surjOn : SurjOn realCoordinate (Ioo 0 Real.pi) univ := by
  intro u hu
  obtain ⟨v, hv, huv⟩ := Real.artanh_surjOn hu
  have hcont : Continuous cosRatio := by
    unfold cosRatio a
    fun_prop (disch := intro x; exact (Real.cosh_pos _).ne')
  have hIcc : v ∈ Icc (cosRatio Real.pi) (cosRatio 0) := by
    rw [cosRatio_pi, cosRatio_zero]
    exact ⟨hv.1.le, hv.2.le⟩
  obtain ⟨θ, hθ, hval⟩ := intermediate_value_Icc' Real.pi_pos.le hcont.continuousOn hIcc
  have h0 : θ ≠ 0 := by
    intro he
    rw [he, cosRatio_zero] at hval
    exact hv.2.ne hval.symm
  have hpi : θ ≠ Real.pi := by
    intro he
    rw [he, cosRatio_pi] at hval
    exact hv.1.ne hval
  refine ⟨θ, ⟨lt_of_le_of_ne hθ.1 h0.symm, lt_of_le_of_ne hθ.2 hpi⟩, ?_⟩
  change Real.artanh (cosRatio θ) = u
  rw [hval, huv]

theorem tendsto_realCoordinate_zero :
    Tendsto realCoordinate (𝓝[Ioo 0 Real.pi] 0) atTop := by
  refine tendsto_atTop.2 (fun u => ?_)
  obtain ⟨θ, hθ, hval⟩ := realCoordinate_surjOn (show u ∈ (univ : Set ℝ) from mem_univ u)
  have hnear : Iio θ ∈ 𝓝[Ioo 0 Real.pi] (0 : ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hθ.1)
  filter_upwards [self_mem_nhdsWithin, hnear] with x hx hlt
  rw [← hval]
  exact (realCoordinate_strictAntiOn hx hθ hlt).le

theorem tendsto_realCoordinate_pi :
    Tendsto realCoordinate (𝓝[Ioo 0 Real.pi] Real.pi) atBot := by
  refine tendsto_atBot.2 (fun u => ?_)
  obtain ⟨θ, hθ, hval⟩ := realCoordinate_surjOn (show u ∈ (univ : Set ℝ) from mem_univ u)
  have hnear : Ioi θ ∈ 𝓝[Ioo 0 Real.pi] Real.pi :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hθ.2)
  filter_upwards [self_mem_nhdsWithin, hnear] with x hx hlt
  rw [← hval]
  exact (realCoordinate_strictAntiOn hθ hx hlt).le

noncomputable def edgePoint (θ : ℝ) : ℂ :=
  (Real.exp (-a θ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

private theorem edgePoint_re (θ : ℝ) : (edgePoint θ).re = Real.exp (-a θ) * Real.cos θ := by
  simp only [edgePoint, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, add_zero, Real.exp_zero, one_mul]

private theorem edgePoint_im (θ : ℝ) : (edgePoint θ).im = Real.exp (-a θ) * Real.sin θ := by
  simp only [edgePoint, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.exp_im, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, Real.exp_zero, one_mul]

/-- Real and imaginary coordinates of the logarithmic Cayley transform on the curved edge. -/
theorem log_edgePoint_coordinates {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    (Complex.log ((1 + edgePoint θ) / (1 - edgePoint θ))).re = realCoordinate θ ∧
    (Complex.log ((1 + edgePoint θ) / (1 - edgePoint θ))).im = imagCoordinate θ := by
  let r := Real.exp (-a θ)
  let w := edgePoint θ
  let z := (1 + w) / (1 - w)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (a_pos hθ))
  have hwre : w.re = r * Real.cos θ := edgePoint_re θ
  have hwim : w.im = r * Real.sin θ := edgePoint_im θ
  have hwSq : Complex.normSq w = r ^ 2 := by
    rw [Complex.normSq_apply, hwre, hwim]
    linear_combination (norm := ring_nf) r^2 * Real.sin_sq_add_cos_sq θ
  have hm : Complex.normSq (1 - w) = 1 + r ^ 2 - 2 * r * Real.cos θ := by
    rw [Complex.normSq_apply] at hwSq ⊢
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hwre, hwim] at *
    linear_combination hwSq
  have hp : Complex.normSq (1 + w) = 1 + r ^ 2 + 2 * r * Real.cos θ := by
    rw [Complex.normSq_apply] at hwSq ⊢
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, hwre, hwim] at *
    linear_combination hwSq
  have hone : 1 - r^2 > 0 := by nlinarith [mul_pos (sub_pos.mpr hr1) (show 0 < 1 + r by positivity)]
  have hd : 0 < Complex.normSq (1 - w) := by
    apply Complex.normSq_pos.mpr
    intro h
    have h' : w = 1 := (sub_eq_zero.mp h).symm
    rw [h', Complex.normSq_one] at hwSq
    linarith
  have hzre : z.re = (1 - r^2) / Complex.normSq (1 - w) := by
    dsimp [z]
    rw [Complex.div_re, ← add_div]
    apply congrArg (fun x : ℝ => x / Complex.normSq (1 - w))
    rw [Complex.normSq_apply] at hwSq
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    linear_combination -hwSq
  have hzim : z.im = (2 * r * Real.sin θ) / Complex.normSq (1 - w) := by
    dsimp [z]
    rw [Complex.div_im, ← sub_div]
    apply congrArg (fun x : ℝ => x / Complex.normSq (1 - w))
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, hwim]
    ring
  have hsinh : 2 * r * Real.sinh (a θ) = 1 - r^2 := by
    rw [Real.sinh_eq]
    have he : r * Real.exp (a θ) = 1 := by
      simp [r, ← Real.exp_add]
    change 2 * r * ((Real.exp (a θ) - r) / 2) = 1 - r ^ 2
    linear_combination he
  have hcosh : 2 * r * Real.cosh (a θ) = 1 + r^2 := by
    rw [Real.cosh_eq]
    have he : r * Real.exp (a θ) = 1 := by
      simp [r, ← Real.exp_add]
    change 2 * r * ((Real.exp (a θ) + r) / 2) = 1 + r ^ 2
    linear_combination he
  change z.log.re = realCoordinate θ ∧ z.log.im = imagCoordinate θ
  constructor
  · have hc : Real.cosh (a θ) ≠ 0 := (Real.cosh_pos _).ne'
    calc
      z.log.re = Real.log (Complex.normSq z) / 2 := by
        rw [Complex.log_re, Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
      _ = _ := by
        have hmem := cosRatio_mem hθ
        change Real.cos θ / Real.cosh (a θ) ∈ Ioo (-1) 1 at hmem
        rw [realCoordinate, Real.artanh_eq_half_log
          (show Real.cos θ / Real.cosh (a θ) ∈ Icc (-1) 1 from ⟨hmem.1.le, hmem.2.le⟩)]
        rw [show 1 / 2 * Real.log ((1 + Real.cos θ / Real.cosh (a θ)) /
            (1 - Real.cos θ / Real.cosh (a θ))) =
            Real.log ((1 + Real.cos θ / Real.cosh (a θ)) /
            (1 - Real.cos θ / Real.cosh (a θ))) / 2 by ring]
        congr 2
        have hsub : Real.cosh (a θ) - Real.cos θ ≠ 0 := by
          have hlt := (div_lt_iff₀ (Real.cosh_pos (a θ))).mp hmem.2
          simp only [one_mul] at hlt
          exact (sub_pos.mpr hlt).ne'
        rw [show Complex.normSq z = Complex.normSq (1 + w) / Complex.normSq (1 - w) from
          Complex.normSq_div _ _, hm, hp, ← hcosh]
        field_simp
  · have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (hzre ▸ div_pos hone hd) : 0 < z.re ∨ z = 0))
    rw [Complex.log_im, ← Real.arctan_tan harg.1 harg.2, Complex.tan_arg,
      hzre, hzim, imagCoordinate, ← hsinh]
    have hs : Real.sinh (a θ) ≠ 0 := (Real.sinh_pos_iff.mpr (a_pos hθ)).ne'
    congr 1
    field_simp

theorem curvedEdge_log_coordinates {w : ℂ} (hw : w ∈ MarkedRealAxis.curvedEdge) :
    ∃ θ ∈ Ioo 0 Real.pi,
      (Complex.log ((1 + w) / (1 - w))).re = realCoordinate θ ∧
      (Complex.log ((1 + w) / (1 - w))).im = imagCoordinate θ := by
  obtain ⟨θ, hθ, rfl⟩ := hw
  exact ⟨θ, hθ, log_edgePoint_coordinates hθ⟩

/-- Equal real coordinates on the image of the curved edge force equal imaginary coordinates. -/
theorem curvedEdge_log_same_real {w₀ w₁ : ℂ}
    (hw₀ : w₀ ∈ MarkedRealAxis.curvedEdge) (hw₁ : w₁ ∈ MarkedRealAxis.curvedEdge)
    (hre : (Complex.log ((1 + w₀) / (1 - w₀))).re =
      (Complex.log ((1 + w₁) / (1 - w₁))).re) :
    (Complex.log ((1 + w₀) / (1 - w₀))).im =
      (Complex.log ((1 + w₁) / (1 - w₁))).im := by
  obtain ⟨θ₀, hθ₀, hre₀, him₀⟩ := curvedEdge_log_coordinates hw₀
  obtain ⟨θ₁, hθ₁, hre₁, him₁⟩ := curvedEdge_log_coordinates hw₁
  have hθ : θ₀ = θ₁ := realCoordinate_strictAntiOn.injOn hθ₀ hθ₁
    (hre₀.symm.trans (hre.trans hre₁))
  rw [him₀, him₁, hθ]

theorem curvedEdge_log_im_nonneg {w : ℂ} (hw : w ∈ MarkedRealAxis.curvedEdge) :
    0 ≤ (Complex.log ((1 + w) / (1 - w))).im := by
  obtain ⟨θ, hθ, _, him⟩ := curvedEdge_log_coordinates hw
  rw [him]
  exact imagCoordinate_nonneg hθ

private theorem arg_edgePoint {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    (edgePoint θ).arg = θ := by
  rw [edgePoint, Complex.arg_real_mul _ (Real.exp_pos _), Complex.arg_exp_mul_I,
    toIocMod_eq_self]
  constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]

private theorem arg_mem_of_curvedEdge {w : ℂ} (hw : w ∈ MarkedRealAxis.curvedEdge) :
    w.arg ∈ Ioo 0 Real.pi := by
  obtain ⟨θ, hθ, rfl⟩ := hw
  change (edgePoint θ).arg ∈ _
  rwa [arg_edgePoint hθ]

private theorem log_im_eq_imagCoordinate_arg {w : ℂ} (hw : w ∈ MarkedRealAxis.curvedEdge) :
    (Complex.log ((1 + w) / (1 - w))).im = imagCoordinate w.arg := by
  obtain ⟨θ, hθ, rfl⟩ := hw
  change (Complex.log ((1 + edgePoint θ) / (1 - edgePoint θ))).im =
    imagCoordinate (edgePoint θ).arg
  rw [arg_edgePoint hθ]
  exact (log_edgePoint_coordinates hθ).2

/-- The imaginary coordinate tends to zero along the curved edge at its endpoint `1`. -/
theorem tendsto_curvedEdge_log_im_one :
    Tendsto (fun w : ℂ => (Complex.log ((1 + w) / (1 - w))).im)
      (𝓝[MarkedRealAxis.curvedEdge] 1) (𝓝 0) := by
  have harg : Tendsto Complex.arg (𝓝[MarkedRealAxis.curvedEdge] 1) (𝓝[Ioo 0 Real.pi] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt Complex.arg 1 := Complex.continuousAt_arg (by simp)
      simpa only [ContinuousWithinAt, Complex.arg_one] using hc.continuousWithinAt (s := MarkedRealAxis.curvedEdge)
    · filter_upwards [self_mem_nhdsWithin] with w hw using arg_mem_of_curvedEdge hw
  apply (tendsto_imagCoordinate_zero.comp harg).congr'
  filter_upwards [self_mem_nhdsWithin] with w hw using (log_im_eq_imagCoordinate_arg hw).symm

/-- The imaginary coordinate tends to zero along the curved edge at its endpoint `-1`. -/
theorem tendsto_curvedEdge_log_im_neg_one :
    Tendsto (fun w : ℂ => (Complex.log ((1 + w) / (1 - w))).im)
      (𝓝[MarkedRealAxis.curvedEdge] (-1)) (𝓝 0) := by
  have harg : Tendsto Complex.arg (𝓝[MarkedRealAxis.curvedEdge] (-1)) (𝓝[Ioo 0 Real.pi] Real.pi) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt Complex.arg 1 := Complex.continuousAt_arg (by simp)
      have hneg : Tendsto (fun w : ℂ => -w) (𝓝[MarkedRealAxis.curvedEdge] (-1)) (𝓝 1) := by
        have hcont : ContinuousAt (fun w : ℂ => -w) (-1) := by fun_prop
        simpa only [ContinuousWithinAt, neg_neg] using hcont.continuousWithinAt (s := MarkedRealAxis.curvedEdge)
      have hshift : Tendsto (fun w : ℂ => (-w).arg + Real.pi)
          (𝓝[MarkedRealAxis.curvedEdge] (-1)) (𝓝 Real.pi) := by
        have hzero : Tendsto (fun w : ℂ => (-w).arg)
            (𝓝[MarkedRealAxis.curvedEdge] (-1)) (𝓝 0) := by
          simpa only [Complex.arg_one, Function.comp_def] using hc.tendsto.comp hneg
        simpa only [zero_add] using hzero.add tendsto_const_nhds
      apply hshift.congr'
      filter_upwards [self_mem_nhdsWithin] with w hw
      have him : 0 < w.im := by
        obtain ⟨θ, hθ, rfl⟩ := hw
        change 0 < (edgePoint θ).im
        rw [edgePoint_im]
        exact
          mul_pos (Real.exp_pos (-a θ)) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
      rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him, sub_add_cancel]
    · filter_upwards [self_mem_nhdsWithin] with w hw using arg_mem_of_curvedEdge hw
  apply (tendsto_imagCoordinate_pi.comp harg).congr'
  filter_upwards [self_mem_nhdsWithin] with w hw using (log_im_eq_imagCoordinate_arg hw).symm

end BelgianChocolate.ComparisonGraph

