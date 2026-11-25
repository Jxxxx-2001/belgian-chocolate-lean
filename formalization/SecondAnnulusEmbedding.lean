import SourceDiskPaths
import FirstAnnulusEmbedding
import Mathlib.Topology.EMetricSpace.BoundedVariation
import FirstAnnulusMonodromyLength
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! The second Joukowski annulus and the actual center circle of its logarithmic strip. -/

namespace BelgianChocolate.SecondAnnulus

open Complex Set Metric Topology
open BelgianChocolate.FirstAnnulus

/-- The source map in the manuscript's original unit disk. -/
noncomputable def sourceEmbedding (t : ℝ) (w : ℂ) : ℂ := Complex.I * joukowski t w

/-- The same map in the normalized coordinate `s = i z / t`. -/
noncomputable def normalizedEmbedding (w : ℂ) : ℂ := -joukowski 1 w

theorem sourceEmbedding_formula (t : ℝ) (w : ℂ) :
    sourceEmbedding t w = Complex.I * t / 2 * (w+w⁻¹) := by
  simp only [sourceEmbedding, joukowski, ofReal_div, ofReal_ofNat]
  ring

theorem sourceEmbedding_eq_unscale_formula (t : ℝ) (w : ℂ) :
    sourceEmbedding t w = -(t : ℂ) * Complex.I * normalizedEmbedding w := by
  simp [sourceEmbedding, normalizedEmbedding, joukowski]
  ring

theorem normalizedEmbedding_differentiableOn :
    DifferentiableOn ℂ normalizedEmbedding (radialAnnulus 19) :=
  fun _ hw => (joukowski_differentiableAt (κ := 1) hw.1).neg.differentiableWithinAt

theorem normalizedEmbedding_injOn : InjOn normalizedEmbedding (radialAnnulus 19) := by
  intro w hw u hu h
  exact joukowski_injOn (κ := 1) (by norm_num) hw.1 hu.1 (neg_injective h)

private theorem input_ne_zero {w : ℂ} (hw : 1 < ‖w‖) : w ≠ 0 := by
  rintro rfl
  norm_num at hw

/-- Exact limiting major semiaxis of the outer ellipse in normalized coordinates. -/
theorem normalizedEmbedding_norm_lt {w : ℂ} (hw : w ∈ radialAnnulus 19) :
    ‖normalizedEmbedding w‖ < 181/19 := by
  obtain ⟨hr,hR⟩ := hw
  let r := ‖w‖
  have hpos : 0 < r := zero_lt_one.trans hr
  have hrad : r + r⁻¹ < 19 + (19:ℝ)⁻¹ := by
    have hp : 0 < (19-r)*(19*r-1) := mul_pos (by linarith) (by linarith)
    field_simp
    nlinarith
  calc
    ‖normalizedEmbedding w‖ = (1/2:ℝ)*‖w+w⁻¹‖ := by
      simp [normalizedEmbedding,joukowski]
    _ ≤ (1/2:ℝ)*(r+r⁻¹) := by
      gcongr
      simpa [r] using norm_add_le w w⁻¹
    _ < 181/19 := by linarith

theorem sourceEmbedding_norm_lt {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {w : ℂ} (hw : w ∈ radialAnnulus 19) : ‖sourceEmbedding t w‖ < 181/190 := by
  rw [sourceEmbedding_eq_unscale_formula, norm_mul, norm_mul, norm_neg, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  calc
    t*‖normalizedEmbedding w‖ < t*(181/19) := mul_lt_mul_of_pos_left (normalizedEmbedding_norm_lt hw) ht
    _ ≤ 181/190 := by linarith

/-- The whole image avoids the real segment containing all three marked points. -/
theorem normalizedEmbedding_avoids_slit {w : ℂ} (hw : 1 < ‖w‖) :
    normalizedEmbedding w ∉ slit 1 := by
  intro h
  apply joukowski_notMem_slit (κ := 1) (by norm_num) hw
  rcases h with ⟨him,hre⟩
  exact ⟨by simpa [normalizedEmbedding] using him, by simpa [normalizedEmbedding] using hre⟩

theorem sourceEmbedding_differentiableOn (t : ℝ) :
    DifferentiableOn ℂ (sourceEmbedding t) (radialAnnulus 19) :=
  fun _ hw => ((joukowski_differentiableAt (κ := t) hw.1).const_mul Complex.I).differentiableWithinAt

theorem sourceEmbedding_injOn {t : ℝ} (ht : 0 < t) :
    InjOn (sourceEmbedding t) (radialAnnulus 19) := by
  intro w hw u hu h
  exact joukowski_injOn ht hw.1 hu.1 (mul_left_cancel₀ Complex.I_ne_zero h)

private theorem open_annulus : IsOpen (radialAnnulus 19) :=
  (isOpen_lt (continuous_const (y := (1:ℝ))) (continuous_norm (E := ℂ))).inter
    (isOpen_lt continuous_norm (continuous_const (y := (19:ℝ))))

private theorem joukowski_strict_deriv (t : ℝ) {w : ℂ} (hw : 1 < ‖w‖) :
    HasStrictDerivAt (joukowski t) (((t/2:ℝ):ℂ)*(1 - (w^2)⁻¹)) w := by
  have h := (hasStrictDerivAt_id w).add (hasStrictDerivAt_inv (input_ne_zero hw))
  unfold joukowski
  simpa only [Pi.add_apply, id_eq, sub_eq_add_neg] using h.const_mul ((t/2:ℝ):ℂ)

private theorem outer_deriv_ne_zero {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : 1 < ‖w‖) :
    ((t/2:ℝ):ℂ)*(1 - (w^2)⁻¹) ≠ 0 := by
  apply mul_ne_zero (by exact_mod_cast (by positivity : t/2 ≠ 0))
  intro he
  have he' : w^2 = 1 := by simpa using congrArg Inv.inv (sub_eq_zero.mp he).symm
  have hnorm := congrArg norm he'
  rw [norm_pow,norm_one] at hnorm
  nlinarith

/-- The source map is an open embedding on the annulus. -/
theorem sourceEmbedding_isOpenEmbedding {t : ℝ} (ht : 0 < t) :
    IsOpenEmbedding (fun w : radialAnnulus 19 => sourceEmbedding t w) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (sourceEmbedding_differentiableOn t).continuousOn.domRestrict
    (fun a b h => Subtype.ext (sourceEmbedding_injOn ht a.property b.property h))
  apply isOpenMap_iff_nhds_le.mpr
  intro w
  have h := ((joukowski_strict_deriv t w.property.1).const_mul Complex.I).map_nhds_eq
    (mul_ne_zero Complex.I_ne_zero (outer_deriv_ne_zero ht w.property.1))
  change 𝓝 (sourceEmbedding t (w:ℂ)) ≤ Filter.map
    (sourceEmbedding t ∘ (Subtype.val : radialAnnulus 19 → ℂ)) (𝓝 w)
  rw [← Filter.map_map,
    open_annulus.isOpenEmbedding_subtypeVal.map_nhds_eq]
  exact h.ge

open BelgianChocolate.SourceDiskPaths

/-- The normalized image avoids all three source punctures as well as the unit-disk boundary. -/
theorem normalizedEmbedding_mapsTo {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    MapsTo normalizedEmbedding (radialAnnulus 19) (scaledDisk t) := by
  intro w hw
  have hR : 10 ≤ 1/t := (le_div_iff₀ ht).mpr (by linarith)
  have h := normalizedEmbedding_avoids_slit hw.1
  have hne (a : ℂ) (ha : a ∈ slit 1) : normalizedEmbedding w ≠ a := fun he => h (he ▸ ha)
  refine ⟨by linarith [normalizedEmbedding_norm_lt hw], hne 0 ?_, hne (-1) ?_, hne 1 ?_⟩ <;>
    norm_num [slit]

theorem sourceEmbedding_eq_unscale (t : ℝ) (w : ℂ) :
    sourceEmbedding t w = unscale t (normalizedEmbedding w) :=
  sourceEmbedding_eq_unscale_formula t w

theorem scale_sourceEmbedding {t : ℝ} (ht : 0 < t) (w : ℂ) :
    FirstAnnulusPaths.scale t (sourceEmbedding t w) = normalizedEmbedding w := by
  rw [sourceEmbedding_eq_unscale, scale_unscale ht]

/-- The physical embedding omits the three marked preimages in the unit disk. -/
theorem sourceEmbedding_mapsTo {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    MapsTo (sourceEmbedding t) (radialAnnulus 19) (sourceDisk t) := by
  intro w hw
  rw [sourceEmbedding_eq_unscale]
  exact unscale_mapsTo ht (normalizedEmbedding_mapsTo ht ht' hw)

theorem source_embedding {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    DifferentiableOn ℂ (sourceEmbedding t) (radialAnnulus 19) ∧
    IsOpenEmbedding (fun w : radialAnnulus 19 => sourceEmbedding t w) ∧
    MapsTo (sourceEmbedding t) (radialAnnulus 19) (sourceDisk t) :=
  ⟨sourceEmbedding_differentiableOn t, sourceEmbedding_isOpenEmbedding ht, sourceEmbedding_mapsTo ht ht'⟩

/-- A genuine parameterization of the middle circle before applying Joukowski. -/
noncomputable def centerParameter (ζ : Circle) : ℂ := (Real.sqrt 19:ℂ)*(ζ:ℂ)

private theorem sqrt19_bounds : 4 < Real.sqrt 19 ∧ Real.sqrt 19 < 5 :=
  ⟨Real.lt_sqrt_of_sq_lt (by norm_num), (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)⟩

theorem centerParameter_mem (ζ : Circle) : centerParameter ζ ∈ radialAnnulus 19 := by
  change 1 < ‖_‖ ∧ ‖_‖ < 19
  simp only [centerParameter,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  constructor <;> linarith [sqrt19_bounds.1,sqrt19_bounds.2]

/-- The normalized center ellipse in the complete three-puncture source disk. -/
noncomputable def stripCenterCircle {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    C(Circle, scaledDisk t) where
  toFun ζ := ⟨normalizedEmbedding (centerParameter ζ), normalizedEmbedding_mapsTo ht ht' (centerParameter_mem _)⟩
  continuous_toFun := Continuous.subtype_mk
    (normalizedEmbedding_differentiableOn.continuousOn.comp_continuous
      (show Continuous centerParameter by unfold centerParameter; fun_prop) centerParameter_mem) _

theorem exp_logCenterSegment_zero (u : unitInterval) :
    Complex.exp (logCenterSegment (Real.log 19) 0 u) = centerParameter (positiveCircleLoop u) := by
  change Complex.exp ⟨Real.log 19/2,0+2*Real.pi*(u:ℝ)⟩ =
    (Real.sqrt 19 : ℂ) * Complex.exp (((2*Real.pi*(u:ℝ):ℝ):ℂ)*Complex.I)
  rw [zero_add, Complex.mk_eq_add_mul_I, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_half,
    Real.exp_log (by norm_num : (0:ℝ)<19)]

/-- The path used by the strip estimate is the actual positive annulus center in the source. -/
theorem stripCenterCircle_positiveLoop {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (u : unitInterval) :
    ((positiveCircleLoop.map (stripCenterCircle ht ht').continuous u : scaledDisk t):ℂ) =
      normalizedEmbedding (Complex.exp (logCenterSegment (Real.log 19) 0 u)) := by
  rw [exp_logCenterSegment_zero]
  rfl

/-- Exact source hyperbolic length consumed by a positive turn. -/
theorem stripCenter_period_dist :
    dist (stripCenter (Real.log 19) 0 (Real.log_pos (by norm_num)))
      (stripCenter (Real.log 19) (0+2*Real.pi) (Real.log_pos (by norm_num))) =
      2*Real.pi^2/Real.log 19 :=
  FirstAnnulus.stripCenter_period_dist (by norm_num) 0

/-- The metric variation of the entire lifted center path equals its endpoint distance.
This measures the full hyperbolic arc for the actual positive R19 turn. -/
theorem stripCenter_curve_length :
    eVariationOn
      (fun u : ℝ => stripCenter (Real.log 19) (2*Real.pi*u) (Real.log_pos (by norm_num)))
      (Icc 0 1) = ENNReal.ofReal (2*Real.pi^2/Real.log 19) := by
  let k : ℝ := 2*Real.pi^2/Real.log 19
  let c : ℝ → UpperHalfPlane := fun u => stripCenter (Real.log 19) (2*Real.pi*u) (Real.log_pos (by norm_num))
  let l : ℝ → ℝ := fun u => k*u
  have h (u v : ℝ) : dist (c u) (c v) = dist (l u) (l v) := by
    change dist (stripCenter _ _ _) (stripCenter _ _ _) = _
    rw [UpperHalfPlane.dist_of_re_eq (by simp), Real.dist_eq, Real.dist_eq]
    simp only [FirstAnnulus.stripCenter_im, Real.log_exp, l, k]
    rw [show -(Real.pi/Real.log 19) * (2*Real.pi*u) -
        -(Real.pi/Real.log 19) * (2*Real.pi*v) =
        -(2*Real.pi^2/Real.log 19*u - 2*Real.pi^2/Real.log 19*v) by ring,abs_neg]
  have he (u v : ℝ) : edist (c u) (c v) = edist (l u) (l v) := by
    rw [edist_dist, edist_dist, h]
  have hv : eVariationOn c (Icc 0 1) = eVariationOn l (Icc 0 1) := by
    simp only [eVariationOn, he]
  have hk : 0 ≤ k := by
    have hL : 0 < Real.log 19 := Real.log_pos (by norm_num)
    dsimp [k]; positivity
  have hm : MonotoneOn l Set.univ := fun _ _ _ _ huv => mul_le_mul_of_nonneg_left huv hk
  have hl := hm.eVariationOn_eq (a := 0) (b := 1) (by simp) (by simp)
  exact hv.trans (by simpa [l,k] using hl)

end BelgianChocolate.SecondAnnulus

