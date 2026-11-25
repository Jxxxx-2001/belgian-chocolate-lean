import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic

/-! Hyperbolic displacement of a full annulus turn in logarithmic strip coordinates. -/

namespace BelgianChocolate.FirstAnnulus

open Complex

/-- The strip chart for a strip of width `L`. -/
noncomputable def stripChart (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.pi / L : ℝ) * I * z)

private theorem argument_im (L : ℝ) (z : ℂ) :
    (((Real.pi / L : ℝ) : ℂ) * I * z).im = (Real.pi / L) * z.re := by
  simp [Complex.mul_im, Complex.mul_re]

private theorem argument_re (L : ℝ) (z : ℂ) :
    (((Real.pi / L : ℝ) : ℂ) * I * z).re = -(Real.pi / L) * z.im := by
  simp [Complex.mul_im, Complex.mul_re]

theorem stripChart_im_pos {L : ℝ} {z : ℂ} (hx : 0 < z.re) (hxL : z.re < L) :
    0 < (stripChart L z).im := by
  have hL := hx.trans hxL
  rw [stripChart, Complex.exp_im, argument_im]
  apply mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi (by positivity) _)
  calc
    Real.pi / L * z.re < Real.pi / L * L := by gcongr
    _ = Real.pi := div_mul_cancel₀ _ hL.ne'

/-- The point of height `t` on the center line of the strip, in upper half-plane coordinates. -/
noncomputable def stripCenter (L t : ℝ) (hL : 0 < L) : UpperHalfPlane :=
  ⟨stripChart L ⟨L / 2, t⟩, stripChart_im_pos (by change 0 < L/2; linarith)
    (by change L/2 < L; linarith)⟩

private theorem center_angle {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (((Real.pi / L : ℝ) : ℂ) * I * (⟨L / 2, t⟩ : ℂ)).im = Real.pi / 2 := by
  rw [argument_im]
  change Real.pi / L * (L / 2) = Real.pi / 2
  field_simp

@[simp] theorem stripCenter_re {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (stripCenter L t hL).re = 0 := by
  change (Complex.exp _).re = 0
  rw [Complex.exp_re, center_angle hL, Real.cos_pi_div_two, mul_zero]

@[simp] theorem stripCenter_im {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (stripCenter L t hL).im = Real.exp (-(Real.pi / L) * t) := by
  change (Complex.exp _).im = _
  rw [Complex.exp_im, center_angle hL, Real.sin_pi_div_two, mul_one, argument_re]

theorem stripCenter_period_dist {R : ℝ} (hR : 1 < R) (t : ℝ) :
    dist (stripCenter (Real.log R) t (Real.log_pos hR))
      (stripCenter (Real.log R) (t + 2 * Real.pi) (Real.log_pos hR)) =
      2 * Real.pi ^ 2 / Real.log R := by
  have hlog : 0 < Real.log R := Real.log_pos hR
  rw [UpperHalfPlane.dist_of_re_eq (by simp), Real.dist_eq]
  simp only [stripCenter_im, Real.log_exp]
  rw [show -(Real.pi / Real.log R) * t -
      -(Real.pi / Real.log R) * (t + 2 * Real.pi) = 2 * Real.pi ^ 2 / Real.log R by ring,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi ^ 2 / Real.log R)]

open scoped ComplexConjugate
open Metric Set


/-- The half-plane Cayley coordinate centered at `p`. -/
private noncomputable def centeredCayley (p z : ℂ) : ℂ := (z-p)/(z-conj p)

private noncomputable def centeredCayleyInv (p w : ℂ) : ℂ := (p-w*conj p)/(1-w)

private theorem sub_conj_ne_zero {p z : ℂ} (hp : 0 < p.im) (hz : 0 < z.im) :
    z - conj p ≠ 0 := by
  intro h
  have hi := congrArg Complex.im (sub_eq_zero.mp h)
  simp at hi
  linarith

private theorem norm_sub_lt_iff {p z : ℂ} (hp : 0 < p.im) :
    ‖z-p‖ < ‖z-conj p‖ ↔ 0 < z.im := by
  have hs : ‖z-conj p‖^2 - ‖z-p‖^2 = 4*p.im*z.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.conj_re,
      Complex.sub_im, Complex.conj_im]
    ring
  have hn := norm_nonneg (z-p)
  have hm := norm_nonneg (z-conj p)
  constructor
  · intro h
    have hh : 0 < ‖z-conj p‖^2 - ‖z-p‖^2 := sub_pos.mpr (by gcongr)
    rw [hs] at hh
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4*p.im)).mp hh
  · intro h
    have hh : 0 < 4*p.im*z.im := by positivity
    nlinarith

private theorem centeredCayley_norm_lt {p z : ℂ} (hp : 0 < p.im) (hz : 0 < z.im) :
    ‖centeredCayley p z‖ < 1 := by
  rw [centeredCayley, norm_div, div_lt_one (norm_pos_iff.mpr (sub_conj_ne_zero hp hz))]
  exact (norm_sub_lt_iff hp).mpr hz

private theorem disc_denom {w : ℂ} (hw : ‖w‖ < 1) : 1-w ≠ 0 := by
  rintro h
  have he := (sub_eq_zero.mp h).symm
  simp [he] at hw

private theorem centeredCayleyInv_im_pos {p w : ℂ} (hp : 0 < p.im) (hw : ‖w‖ < 1) :
    0 < (centeredCayleyInv p w).im := by
  apply (norm_sub_lt_iff hp).mp
  have h := disc_denom hw
  have he : centeredCayleyInv p w - p = w * (centeredCayleyInv p w - conj p) := by
    unfold centeredCayleyInv
    field_simp
    ring
  have hne : centeredCayleyInv p w - conj p ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact sub_conj_ne_zero hp hp (by rwa [sub_eq_zero.mp he] at hz)
  rw [he, norm_mul]
  simpa using mul_lt_mul_of_pos_right hw (norm_pos_iff.mpr hne)

private theorem centeredCayleyInv_apply {p z : ℂ} (hp : 0 < p.im) (hz : 0 < z.im) :
    centeredCayleyInv p (centeredCayley p z) = z := by
  have h := sub_conj_ne_zero hp hz
  have h' := disc_denom (centeredCayley_norm_lt hp hz)
  unfold centeredCayleyInv
  apply (div_eq_iff h').mpr
  unfold centeredCayley
  field_simp
  ring

/-- Schwarz–Pick for an upper half-plane self-map in the standard curvature `-1` metric. -/
theorem halfPlane_dist_map_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (hm : MapsTo f {z | 0 < z.im} {z | 0 < z.im}) (p z : UpperHalfPlane) :
    dist (⟨f z, hm z.im_pos⟩ : UpperHalfPlane) ⟨f p, hm p.im_pos⟩ ≤ dist z p := by
  let g : ℂ → ℂ := fun w => centeredCayley (f p) (f (centeredCayleyInv p w))
  have hInv : MapsTo (centeredCayleyInv p) (ball 0 1) {z | 0 < z.im} := by
    intro w hw
    exact centeredCayleyInv_im_pos p.im_pos (mem_ball_zero_iff.mp hw)
  have hDiffInv : DifferentiableOn ℂ (centeredCayleyInv p) (ball 0 1) := by
    intro w hw
    unfold centeredCayleyInv
    fun_prop (disch := exact disc_denom (mem_ball_zero_iff.mp hw))
  have hDiffC : DifferentiableOn ℂ (centeredCayley (f p)) {z | 0 < z.im} := by
    intro v hv
    unfold centeredCayley
    fun_prop (disch := exact sub_conj_ne_zero (hm p.im_pos) hv)
  have hDiffG : DifferentiableOn ℂ g (ball 0 1) :=
    hDiffC.comp (hf.comp hDiffInv hInv) (hm.comp hInv)
  have hMaps : MapsTo g (ball 0 1) (closedBall 0 1) := by
    intro w hw
    exact mem_closedBall_zero_iff.mpr (centeredCayley_norm_lt (hm p.im_pos) (hm (hInv hw))).le
  have hZero : g 0 = 0 := by simp [g, centeredCayley, centeredCayleyInv]
  have hh := Complex.norm_le_norm_of_mapsTo_ball hDiffG hMaps hZero
    (centeredCayley_norm_lt p.im_pos z.im_pos)
  change ‖centeredCayley (f p) (f (centeredCayleyInv p (centeredCayley p z)))‖ ≤ _ at hh
  rw [centeredCayleyInv_apply p.im_pos z.im_pos] at hh
  have ht : Real.tanh (dist (⟨f z, hm z.im_pos⟩ : UpperHalfPlane) ⟨f p, hm p.im_pos⟩ / 2) ≤
      Real.tanh (dist z p / 2) := by
    simpa only [UpperHalfPlane.tanh_half_dist, Complex.dist_eq, centeredCayley, norm_div] using hh
  have htmono : StrictMono Real.tanh := by
    intro a b hab
    simp only [Real.tanh_eq_sinh_div_cosh]
    apply (div_lt_div_iff₀ (Real.cosh_pos a) (Real.cosh_pos b)).mpr
    have hs : 0 < Real.sinh (b - a) := by positivity
    rw [Real.sinh_sub] at hs
    linarith
  exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mp (htmono.le_iff_le.mp ht)

/-- The displacement of a holomorphic lift across one turn, after strip uniformization. -/
theorem strip_period_image_dist_le {R : ℝ} (hR : 1 < R) (t : ℝ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (hm : MapsTo f {z | 0 < z.im} {z | 0 < z.im}) :
    let p := stripCenter (Real.log R) t (Real.log_pos hR)
    let z := stripCenter (Real.log R) (t + 2 * Real.pi) (Real.log_pos hR)
    dist (⟨f z, hm z.im_pos⟩ : UpperHalfPlane) ⟨f p, hm p.im_pos⟩ ≤
      2 * Real.pi ^ 2 / Real.log R := by
  dsimp only
  exact (halfPlane_dist_map_le hf hm _ _).trans
    ((dist_comm _ _).trans (stripCenter_period_dist hR t)).le


/-- The logarithmic covering strip of modulus `L`. -/
def logStrip (L : ℝ) : Set ℂ := {z | 0 < z.re ∧ z.re < L}

/-- Inverse of the strip chart, using the principal logarithm on the upper half-plane. -/
noncomputable def stripChartInv (L : ℝ) (w : ℂ) : ℂ :=
  -(L / Real.pi : ℝ) * I * Complex.log w

theorem stripChartInv_mapsTo {L : ℝ} (hL : 0 < L) :
    MapsTo (stripChartInv L) {w | 0 < w.im} (logStrip L) := by
  intro w hw
  change 0 < w.im at hw
  have harg : 0 < w.arg :=
    (Complex.arg_nonneg_iff.mpr hw.le).lt_of_ne (by
      intro h
      have := Complex.norm_mul_sin_arg w
      rw [← h, Real.sin_zero, mul_zero] at this
      linarith)
  have harg' := Complex.arg_lt_pi_iff.mpr (Or.inr hw.ne')
  have hReal : (stripChartInv L w).re = (L / Real.pi) * w.arg := by
    simp [stripChartInv, Complex.mul_re, Complex.mul_im, Complex.log_im]
  change 0 < (stripChartInv L w).re ∧ (stripChartInv L w).re < L
  rw [hReal]
  refine ⟨by positivity, ?_⟩
  calc
    L / Real.pi * w.arg < L / Real.pi * Real.pi := by gcongr
    _ = L := div_mul_cancel₀ _ Real.pi_ne_zero

theorem differentiableOn_stripChartInv (L : ℝ) :
    DifferentiableOn ℂ (stripChartInv L) {w | 0 < w.im} := by
  intro w hw
  change 0 < w.im at hw
  have hs : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hw.ne')
  unfold stripChartInv
  exact ((Complex.differentiableAt_log hs).const_mul _).differentiableWithinAt

private theorem chart_scalar_inv {L : ℝ} (hL : 0 < L) :
    (-((L / Real.pi : ℝ) : ℂ) * I) * (((Real.pi / L : ℝ) : ℂ) * I) = 1 := by
  rw [show ∀ (a b : ℂ), (-a * I) * (b * I) = a*b by
    intro a b
    linear_combination -a*b*Complex.I_mul_I]
  norm_cast
  field_simp [Real.pi_ne_zero, hL.ne']

theorem stripChartInv_leftInv {L : ℝ} {z : ℂ} (hz : z ∈ logStrip L) :
    stripChartInv L (stripChart L z) = z := by
  obtain ⟨hx,hxL⟩ := hz
  have hL := hx.trans hxL
  have him : (((Real.pi / L : ℝ) : ℂ) * I * z).im = Real.pi / L * z.re := by
    simp [Complex.mul_im, Complex.mul_re]
  have habove : 0 < Real.pi / L * z.re := by positivity
  have hbelow : Real.pi / L * z.re < Real.pi := by
    calc
      Real.pi / L * z.re < Real.pi / L * L := by gcongr
      _ = Real.pi := div_mul_cancel₀ _ hL.ne'
  unfold stripChartInv stripChart
  rw [Complex.log_exp (by rw [him]; linarith [Real.pi_pos]) (by rw [him]; exact hbelow.le)]
  push_cast
  push_cast at *
  have hc := chart_scalar_inv hL
  push_cast at hc
  rw [← mul_assoc, hc, one_mul]

theorem stripChartInv_rightInv {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : 0 < w.im) :
    stripChart L (stripChartInv L w) = w := by
  have hw0 : w ≠ 0 := fun he => by simp [he] at hw
  unfold stripChart stripChartInv
  have hc := chart_scalar_inv hL
  rw [mul_comm] at hc
  push_cast at *
  rw [← mul_assoc, hc, one_mul, Complex.exp_log hw0]

/-- Schwarz–Pick on a logarithmic strip, evaluated at the endpoints of one deck turn. -/
theorem logStrip_period_dist_le {R : ℝ} (hR : 1 < R) (t : ℝ) {F : ℂ → ℂ}
    (hf : DifferentiableOn ℂ F (logStrip (Real.log R)))
    (hm : MapsTo F (logStrip (Real.log R)) {w | 0 < w.im}) :
    let L := Real.log R
    let p : ℂ := ⟨L/2,t⟩
    let z : ℂ := ⟨L/2,t + 2*Real.pi⟩
    let hp : p ∈ logStrip L := ⟨by change 0 < Real.log R/2; linarith [Real.log_pos hR],
      by change Real.log R/2 < Real.log R; linarith [Real.log_pos hR]⟩
    let hz : z ∈ logStrip L := ⟨by change 0 < Real.log R/2; linarith [Real.log_pos hR],
      by change Real.log R/2 < Real.log R; linarith [Real.log_pos hR]⟩
    dist (⟨F z, hm hz⟩ : UpperHalfPlane) ⟨F p, hm hp⟩ ≤ 2 * Real.pi^2 / L := by
  dsimp only
  have hL := Real.log_pos hR
  have hmap := stripChartInv_mapsTo hL
  have h := strip_period_image_dist_le hR t (hf.comp (differentiableOn_stripChartInv _) hmap)
    (hm.comp hmap)
  dsimp only [Function.comp_apply, stripCenter] at h
  simpa only [stripChartInv_leftInv (z := (⟨_,_⟩ : ℂ))
    (show (⟨Real.log R/2, _⟩ : ℂ) ∈ logStrip (Real.log R) from
      ⟨by change 0 < Real.log R/2; linarith [Real.log_pos hR], by change Real.log R/2 < Real.log R; linarith⟩)] using h

open UpperHalfPlane
open scoped MatrixGroups

/-- The physical displacement of a point bounds the translation length computed from the trace. -/
theorem real_matrix_trace_length_le (g : SL(2, ℝ)) (p : UpperHalfPlane) :
    2 * Real.arcosh (|(g : Matrix (Fin 2) (Fin 2) ℝ).trace| / 2) ≤ dist (g • p) p := by
  let D : ℂ := (g 1 0 : ℝ) * (p : ℂ) + (g 1 1 : ℝ)
  let A : ℂ := (g 0 0 : ℝ) * (p : ℂ) + (g 0 1 : ℝ)
  have hD : D ≠ 0 := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) p
  have hDp := norm_pos_iff.mpr hD
  have hp := p.im_pos
  have hact : ((g • p : UpperHalfPlane) : ℂ) = A / D := by
    simpa [A,D] using (coe_specialLinearGroup_apply g p)
  have him : (g • p).im = p.im / ‖D‖^2 := by
    rw [MulAction.compHom_smul_def, im_smul_eq_div_normSq]
    simp [D, denom, Complex.normSq_eq_norm_sq]
  have hN : (A - conj (p : ℂ)*D).im = (g 0 0 + g 1 1)*p.im := by
    simp [A,D,Complex.sub_im,Complex.mul_re,Complex.mul_im]
    ring
  have hsqrt : Real.sqrt ((g • p).im * p.im) = p.im / ‖D‖ := by
    rw [him, show p.im / ‖D‖^2 * p.im = (p.im / ‖D‖)^2 by ring, Real.sqrt_sq (by positivity)]
  have hnum : ‖((g • p : UpperHalfPlane) : ℂ) - conj (p : ℂ)‖ =
      ‖A - conj (p : ℂ)*D‖ / ‖D‖ := by
    rw [hact, div_sub' hD, mul_comm D, norm_div]
  have hnp := Complex.abs_im_le_norm (A - conj (p : ℂ)*D)
  rw [hN, abs_mul, abs_of_pos hp] at hnp
  have hle : |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|/2 ≤ Real.cosh (dist (g • p) p / 2) := by
    rw [cosh_half_dist, Complex.dist_eq, hnum, hsqrt, Matrix.trace_fin_two]
    field_simp
    linarith
  by_cases ht : (g : Matrix (Fin 2) (Fin 2) ℝ).trace = 0
  · simp [ht, Real.arcosh, Real.sqrt_eq_zero_of_nonpos (by norm_num : (-1:ℝ) ≤ 0)]
  have := (Real.arcosh_le_arcosh (by positivity) (Real.cosh_pos _)).2 hle
  rw [Real.arcosh_cosh (by positivity)] at this
  linarith

/-- A strip lift whose two endpoint values differ by `g` satisfies the annulus length bound. -/
theorem logStrip_trace_length_le {R : ℝ} (hR : 1 < R) (t : ℝ) {F : ℂ → ℂ}
    (hf : DifferentiableOn ℂ F (logStrip (Real.log R)))
    (hm : Set.MapsTo F (logStrip (Real.log R)) {w | 0 < w.im})
    (g : SL(2, ℝ)) (p : UpperHalfPlane)
    (hstart : (p : ℂ) = F ⟨Real.log R/2, t⟩)
    (hend : ((g • p : UpperHalfPlane) : ℂ) = F ⟨Real.log R/2, t + 2*Real.pi⟩) :
    2 * Real.arcosh (|(g : Matrix (Fin 2) (Fin 2) ℝ).trace| / 2) ≤
      2 * Real.pi^2 / Real.log R := by
  apply (real_matrix_trace_length_le g p).trans
  have hs := logStrip_period_dist_le hR t hf hm
  dsimp only at hs
  convert hs using 1
  congr 1 <;> apply UpperHalfPlane.ext
  · exact hend
  · exact hstart

open scoped Topology


/-- The complex exponential takes the logarithmic strip exactly to this annulus. -/
def radialAnnulus (R : ℝ) : Set ℂ := {w | 1 < ‖w‖ ∧ ‖w‖ < R}

theorem exp_preimage_annulus {R : ℝ} (hR : 1 < R) :
    Complex.exp ⁻¹' radialAnnulus R = logStrip (Real.log R) := by
  ext z
  change (1 < ‖Complex.exp z‖ ∧ ‖Complex.exp z‖ < R) ↔ 0 < z.re ∧ z.re < Real.log R
  rw [Complex.norm_exp, Real.one_lt_exp_iff, Real.lt_log_iff_exp_lt (by linarith)]

theorem exp_covers_annulus (R : ℝ) : IsCoveringMapOn Complex.exp (radialAnnulus R) := by
  apply Complex.isCoveringMapOn_exp.mono
  intro z hz
  obtain ⟨hz, _⟩ := hz
  rintro (rfl : z = 0)
  norm_num at hz

private theorem isOpen_logStrip (L : ℝ) : IsOpen (logStrip L) :=
  (isOpen_lt (continuous_const (y := (0:ℝ))) Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re (continuous_const (y := L)))

private theorem convex_logStrip (L : ℝ) : Convex ℝ (logStrip L) :=
  (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt L)

/-- A normalized continuous lift of an annulus map exists on its logarithmic strip,
provided the specified target projection is a covering over the image. -/
theorem existsUnique_strip_continuousLift {R : ℝ} (hR : 1 < R)
    {X : Set ℂ} {P : UpperHalfPlane → ℂ} (hP : IsCoveringMapOn P X)
    {b : ℂ → ℂ} (hb : ContinuousOn b (radialAnnulus R)) (hbX : MapsTo b (radialAnnulus R) X)
    (z₀ : logStrip (Real.log R)) (p₀ : UpperHalfPlane) (hbase : P p₀ = b (Complex.exp z₀)) :
    ∃! H : C(logStrip (Real.log R), UpperHalfPlane),
      H z₀ = p₀ ∧ ∀ z, P (H z) = b (Complex.exp z) := by
  let S := logStrip (Real.log R)
  let : ContractibleSpace S := (convex_logStrip _).contractibleSpace ⟨_, z₀.property⟩
  let : LocallyPathConnectedSpace S := (isOpen_logStrip _).locallyPathConnectedSpace
  have he : MapsTo Complex.exp S (radialAnnulus R) := by
    intro z hz
    exact show z ∈ Complex.exp ⁻¹' radialAnnulus R from exp_preimage_annulus hR ▸ hz
  let f : C(S,ℂ) :=
    ⟨fun z => b (Complex.exp z), continuousOn_iff_continuous_domRestrict.mp
      (hb.comp Complex.continuous_exp.continuousOn he)⟩
  obtain ⟨H, ⟨h₀,hH⟩,huniq⟩ := hP.existsUnique_continuousMap_lifts f hbase
    (fun z => hbX (he z.property))
  refine ⟨H, ⟨h₀, fun z => congrFun hH z⟩, ?_⟩
  intro G hG
  exact huniq G ⟨hG.1, funext hG.2⟩

/-- A covering projection with nonvanishing complex derivative makes the normalized strip
lift of every holomorphic annulus map holomorphic. The covering hypothesis is explicit. -/
theorem exists_strip_holomorphicLift {R : ℝ} (hR : 1 < R)
    {X : Set ℂ} {P : ℂ → ℂ}
    (hP : IsCoveringMapOn (fun p : UpperHalfPlane => P p) X)
    (hder : ∀ p : UpperHalfPlane, DifferentiableAt ℂ P p ∧ deriv P p ≠ 0)
    {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b (radialAnnulus R))
    (hbX : MapsTo b (radialAnnulus R) X)
    (z₀ : logStrip (Real.log R)) (p₀ : UpperHalfPlane) (hbase : P p₀ = b (Complex.exp z₀)) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (logStrip (Real.log R)) ∧
      MapsTo F (logStrip (Real.log R)) {w | 0 < w.im} ∧ F z₀ = p₀ ∧
      ∀ z ∈ logStrip (Real.log R), P (F z) = b (Complex.exp z) := by
  classical
  obtain ⟨H, ⟨h₀,hH⟩, _⟩ := existsUnique_strip_continuousLift hR hP hb.continuousOn hbX z₀ p₀ hbase
  let S := logStrip (Real.log R)
  let F : ℂ → ℂ := fun z => if hz : z ∈ S then (H ⟨z,hz⟩ : ℂ) else 0
  have heq (z : S) : F z = (H z : ℂ) := by simp [F, z.property]
  have hcont : ContinuousOn F S := continuousOn_iff_continuous_domRestrict.mpr
    ((UpperHalfPlane.continuous_coe.comp H.continuous).congr (fun z => (heq z).symm))
  have hmaps : MapsTo F S {w | 0 < w.im} := fun z hz => by
    change 0 < (F z).im
    rw [heq ⟨z,hz⟩]
    exact (H ⟨z,hz⟩).im_pos
  have hproj : ∀ z ∈ S, P (F z) = b (Complex.exp z) := fun z hz => by
    rw [heq ⟨z,hz⟩]
    exact hH ⟨z,hz⟩
  refine ⟨F, ?_, hmaps, (heq z₀).trans (congrArg UpperHalfPlane.coe h₀), hproj⟩
  intro z hz
  have hnh := (isOpen_logStrip _).mem_nhds hz
  have hfcont := (hcont z hz).continuousAt hnh
  have hp := hder (⟨F z, hmaps hz⟩ : UpperHalfPlane)
  have hann : IsOpen (radialAnnulus R) :=
    (isOpen_lt (continuous_const (y := (1:ℝ))) (continuous_norm (E := ℂ))).inter
      (isOpen_lt continuous_norm (continuous_const (y := R)))
  have he : Complex.exp z ∈ radialAnnulus R := by
    exact show z ∈ Complex.exp ⁻¹' radialAnnulus R from exp_preimage_annulus hR ▸ hz
  have hbc := ((hb (Complex.exp z) he).differentiableAt (hann.mem_nhds he)).hasDerivAt.comp z
    (Complex.hasDerivAt_exp z)
  exact (HasDerivAt.of_comp_left hfcont hp.1.hasDerivAt hbc hp.2
    (Filter.mem_of_superset hnh hproj)).differentiableAt.differentiableWithinAt

open scoped MatrixGroups

/-- If the covering fibers are orbits of a matrix group, a center loop admits a deck
representative with the annulus trace bound. The lifted endpoint is recorded explicitly. -/
theorem exists_matrix_for_annulus_center_loop {R : ℝ} (hR : 1 < R) (t : ℝ)
    {X : Set ℂ} {P : ℂ → ℂ}
    (hP : IsCoveringMapOn (fun p : UpperHalfPlane => P p) X)
    (hder : ∀ p : UpperHalfPlane, DifferentiableAt ℂ P p ∧ deriv P p ≠ 0)
    (G : Subgroup (SL(2, ℝ)))
    (horbit : ∀ p q : UpperHalfPlane, P q = P p → ∃ g ∈ G, g • p = q)
    {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b (radialAnnulus R))
    (hbX : MapsTo b (radialAnnulus R) X) (p : UpperHalfPlane)
    (hbase : P p = b (Complex.exp ⟨Real.log R/2, t⟩)) :
    ∃ (F : ℂ → ℂ) (g : SL(2, ℝ)), g ∈ G ∧
      DifferentiableOn ℂ F (logStrip (Real.log R)) ∧
      MapsTo F (logStrip (Real.log R)) {w | 0 < w.im} ∧
      (∀ z ∈ logStrip (Real.log R), P (F z) = b (Complex.exp z)) ∧
      (p : ℂ) = F ⟨Real.log R/2, t⟩ ∧
      ((g • p : UpperHalfPlane) : ℂ) = F ⟨Real.log R/2, t + 2*Real.pi⟩ ∧
      2 * Real.arcosh (|(g : Matrix (Fin 2) (Fin 2) ℝ).trace|/2) ≤
        2*Real.pi^2/Real.log R := by
  let z (y : ℝ) : ℂ := ⟨Real.log R/2, y⟩
  have hz (y : ℝ) : z y ∈ logStrip (Real.log R) := by
    change 0 < Real.log R / 2 ∧ Real.log R / 2 < Real.log R
    constructor <;> linarith [Real.log_pos hR]
  obtain ⟨F, hd, hm, h₀, hF⟩ := exists_strip_holomorphicLift hR hP hder hb hbX
    ⟨z t,hz t⟩ p hbase
  let q : UpperHalfPlane := ⟨F (z (t + 2*Real.pi)), hm (hz _)⟩
  have he : z (t + 2*Real.pi) = z t + 2*(Real.pi : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [z, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hfiber : P q = P p := by
    change P (F (z (t + 2*Real.pi))) = P p
    rw [hF _ (hz _), he, Complex.exp_periodic, hbase]
  obtain ⟨g,hg,heq⟩ := horbit p q hfiber
  have hfinish := congrArg UpperHalfPlane.coe heq
  exact ⟨F,g,hg,hd,hm,hF,h₀.symm,hfinish,logStrip_trace_length_le hR t hd hm g p h₀.symm hfinish⟩

end BelgianChocolate.FirstAnnulus

