import SlitRadialDomain
import SlitSquareRoot
import ModularLambdaCuspMarked
import CuspSectorSign

/-! The modular cusp coordinate near the upper prime end over minus one. -/

namespace BelgianChocolate.SlitBoundaryGeometry

open Complex Filter Metric Set
open scoped Topology
open BelgianChocolate.ModularLambdaRatio

/-- The upper part of the physical radial domain. Removing the real slit
does not change this sector. -/
def upperCuspSector : Set ℂ := radialDomain ∩ {w : ℂ | 0 < w.im}

/-- The inverse of the marked modular cusp coordinate, using the principal
logarithm of `-w` near one. -/
noncomputable def candidateCuspTau (w : ℂ) : ℂ := -(Real.pi*I)/Complex.log (-w)

private theorem log_nonzero_in_disk {w : ℂ} (h0 : w ≠ 0) (hw : ‖w‖ < 1) :
    Complex.log (-w) ≠ 0 := by
  have hlog := Real.log_neg (norm_pos_iff.mpr h0) hw
  intro he
  have hre := congrArg Complex.re he
  simp only [Complex.log_re, norm_neg, Complex.zero_re] at hre
  linarith

private theorem upper_log_nonzero {w : ℂ} (hw : w ∈ upperCuspSector) :
    Complex.log (-w) ≠ 0 :=
  log_nonzero_in_disk (by rintro rfl; simpa using hw.2)
    (mem_ball_zero_iff.mp (radialDomain_subset_ball hw.1))

private theorem tau_coordinates {w : ℂ} (him : 0 < w.im) :
    (candidateCuspTau w).re = Real.pi*(Real.pi-w.arg) / Complex.normSq (Complex.log (-w)) ∧
    (candidateCuspTau w).im = -(Real.pi*Real.log ‖w‖) / Complex.normSq (Complex.log (-w)) ∧
    Complex.normSq (Complex.log (-w)) = (Real.log ‖w‖)^2+(w.arg-Real.pi)^2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [candidateCuspTau, Complex.div_re, Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]
    ring
  · simp [candidateCuspTau, Complex.div_im, Complex.log_re]
  · simp [Complex.normSq_apply, Complex.log_re, Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos him, pow_two]

/-- On the entire upper radial domain the logarithmic inverse lies in the
open modular strip between the two marked vertical lines. -/
theorem candidateCuspTau_strip {w : ℂ} (hw : w ∈ upperCuspSector) :
    0 < (candidateCuspTau w).re ∧ (candidateCuspTau w).re < 1 ∧
    0 < (candidateCuspTau w).im := by
  have him := hw.2
  change 0 < w.im at him
  have h0 : w ≠ 0 := by rintro rfl; simp at him
  have hn : ‖w‖ < Real.exp (-Real.sqrt (w.arg*(Real.pi-w.arg))) := by
    have h := hw.1
    change ‖w‖ < radialRadius w at h
    rwa [radialRadius_eq_norm_upperPoint him, norm_upperPoint] at h
  have hlog := (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr h0)).mpr hn
  have hθn := Complex.arg_nonneg_iff.mpr him.le
  have hθlt := Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')
  have hb := sub_pos.mpr hθlt
  have hs := Real.sq_sqrt (mul_nonneg hθn hb.le)
  have hsq : w.arg*(Real.pi-w.arg) < (Real.log ‖w‖)^2 := by
    have h := mul_self_lt_mul_self (Real.sqrt_nonneg (w.arg*(Real.pi-w.arg)))
      (show Real.sqrt (w.arg*(Real.pi-w.arg)) < -Real.log ‖w‖ by linarith)
    nlinarith
  have hd := Complex.normSq_pos.mpr (upper_log_nonzero hw)
  obtain ⟨hr, hi, hden⟩ := tau_coordinates him
  rw [hr, hi]
  refine ⟨div_pos (mul_pos Real.pi_pos hb) hd, (div_lt_one hd).mpr ?_, div_pos ?_ hd⟩
  · rw [hden]
    nlinarith
  · have hneg : Real.log ‖w‖ < 0 := by linarith [Real.sqrt_nonneg (w.arg*(Real.pi-w.arg))]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg Real.pi_pos hneg)

/-- The physical cusp is recovered from this strip coordinate. -/
theorem markedCusp_candidateCuspTau {w : ℂ} (h0 : w ≠ 0) :
    MarkedRealAxis.cusp (candidateCuspTau w) = w := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : -(Real.pi*I) / (-(Real.pi*I)/Complex.log (-w)) = Complex.log (-w) := by
    rw [div_div_eq_mul_div]
    field_simp [hπ, I_ne_zero]
  rw [MarkedRealAxis.cusp, candidateCuspTau, e, Complex.exp_log (neg_ne_zero.mpr h0), neg_neg]

/-- Along the upper approach to the physical endpoint, the modular coordinate
goes to infinite height. -/
theorem candidateCuspTau_im_tendsto :
    Tendsto (fun w => (candidateCuspTau w).im) (𝓝[upperCuspSector] (-1 : ℂ)) atTop := by
  have hneg : Tendsto (fun w : ℂ => -w) (𝓝[upperCuspSector] (-1 : ℂ)) (𝓝 1) := by
    simpa using (continuous_neg.continuousAt (x := (-1 : ℂ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := upperCuspSector))
  have hlog : Tendsto (fun w : ℂ => ‖Complex.log (-w)‖) (𝓝[upperCuspSector] (-1 : ℂ)) (𝓝 0) := by
    simpa only [Complex.log_one, norm_zero, Function.comp_def] using
      (continuousAt_clog (show (1 : ℂ) ∈ slitPlane by simp)).norm.tendsto.comp hneg
  apply Filter.tendsto_atTop.2
  intro b
  let B : ℝ := |b|+2
  have hp : 0 < B := by dsimp [B]; positivity
  filter_upwards [self_mem_nhdsWithin (s := upperCuspSector),
    hlog.eventually (gt_mem_nhds (div_pos Real.pi_pos hp))] with w hw hsmall
  have hd := norm_pos_iff.mpr (upper_log_nonzero hw)
  have hbn : B < ‖candidateCuspTau w‖ := by
    rw [candidateCuspTau, norm_div, norm_neg, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    apply (lt_div_iff₀ hd).mpr
    linarith [(lt_div_iff₀ hp).mp hsmall]
  obtain ⟨hr, hr', hi⟩ := candidateCuspTau_strip hw
  have hnorm := Complex.norm_le_abs_re_add_abs_im (candidateCuspTau w)
  rw [abs_of_pos hr, abs_of_pos hi] at hnorm
  dsimp [B] at hbn
  linarith [le_abs_self b]

/-- The actual covering projection has the required zero limit and a
positive imaginary part on the physical upper side of the split endpoint. -/
theorem cuspU_upper_sector :
    Tendsto cuspU (𝓝[upperCuspSector] (-1 : ℂ)) (𝓝 0) ∧
      ∀ᶠ w in 𝓝[upperCuspSector] (-1 : ℂ), 0 < (cuspU w).im := by
  let τ := fun w => UpperHalfPlane.ofComplex (candidateCuspTau w)
  have hτ {w : ℂ} (hw : w ∈ upperCuspSector) : (τ w : ℂ) = candidateCuspTau w := by
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos, (candidateCuspTau_strip hw).2.2]
  have hhigh : Tendsto τ (𝓝[upperCuspSector] (-1 : ℂ)) UpperHalfPlane.atImInfty := by
    apply Filter.tendsto_comap_iff.mpr
    apply candidateCuspTau_im_tendsto.congr'
    filter_upwards [self_mem_nhdsWithin (s := upperCuspSector)] with w hw
    exact (congrArg Complex.im (hτ hw)).symm
  have he {w : ℂ} (hw : w ∈ upperCuspSector) : cuspU w = lambdaRatio (τ w) := by
    have h0 : w ≠ 0 := by rintro rfl; simpa using hw.2
    rw [← cuspU_markedCusp, hτ hw, markedCusp_candidateCuspTau h0]
  constructor
  · have hq : Tendsto (fun σ : UpperHalfPlane => (cuspNomeDisc σ : ℂ))
        UpperHalfPlane.atImInfty (𝓝 0) :=
      UpperHalfPlane.qParam_tendsto_atImInfty (h := 2) (by norm_num)
    have hl := cuspLambda_hasDerivAt_zero.continuousAt.tendsto.comp (hq.comp hhigh)
    rw [cuspLambda_zero] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin (s := upperCuspSector)] with w hw
    exact (cuspLambda_nome _).trans (he hw).symm
  · filter_upwards [self_mem_nhdsWithin (s := upperCuspSector),
      hhigh.eventually CuspSectorSign.lambdaRatio_im_pos_at_cusp] with w hw hp
    rw [he hw]
    apply hp
    · change 0 < (τ w : ℂ).re
      rw [hτ hw]; exact (candidateCuspTau_strip hw).1
    · change (τ w : ℂ).re < 1
      rw [hτ hw]; exact (candidateCuspTau_strip hw).2.1

open BelgianChocolate.SlitSquareRoot

/-- An approach to the upper unfolded endpoint eventually lies above the
physical slit, where the projection tends to zero with positive imaginary
part. The physical-side condition follows from the marked unfolded limit. -/
theorem cuspU_of_unfolded_upper_endpoint {X : Type*} {l : Filter X} {Φ : X → ℂ}
    {α : ℝ} (hα : -1 < α) (hmem : ∀ᶠ z in l, Φ z ∈ candidateSlit α)
    (hP : Tendsto (fun z => unfolding α (Φ z)) l (𝓝 ((Real.sqrt (1+α) : ℂ)*I))) :
    Tendsto (fun z => cuspU (Φ z)) l (𝓝 0) ∧ ∀ᶠ z in l, 0 < (cuspU (Φ z)).im := by
  have hp : 0 < 1+α := by linarith
  have hsq : ((Real.sqrt (1+α) : ℂ))^2 = 1+(α : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  have hlim : Tendsto Φ l (𝓝 (-1)) := by
    have h := ((differentiable_folding α).continuous.tendsto _).comp hP
    have he : folding α ((Real.sqrt (1+α) : ℂ)*I) = -1 := by
      rw [folding, mul_pow, Complex.I_sq, hsq]; ring
    simpa only [Function.comp_def, folding_unfolding, he] using h
  have hi : ∀ᶠ z in l, 0 < (unfolding α (Φ z)).im := by
    have h := continuous_im.continuousAt.tendsto.comp hP
    exact h.eventually (lt_mem_nhds (by simpa using Real.sqrt_pos.2 hp))
  have hs : Tendsto Φ l (𝓝[upperCuspSector] (-1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨hlim, ?_⟩
    filter_upwards [hmem, hi] with z hz hzi
    have hzr := unfolding_re_pos_on_finiteSlit radialDomain_subset_ball hz
    refine ⟨hz.1, ?_⟩
    change 0 < (Φ z).im
    rw [← folding_unfolding α (Φ z), folding, pow_two, add_im, ofReal_im, add_zero, mul_im]
    nlinarith [mul_pos hzr hzi]
  exact ⟨cuspU_upper_sector.1.comp hs, hs.eventually cuspU_upper_sector.2⟩

end BelgianChocolate.SlitBoundaryGeometry
