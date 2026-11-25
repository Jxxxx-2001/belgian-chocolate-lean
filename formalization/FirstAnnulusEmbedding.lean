import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Tactic
import ComparisonCayley
import FirstAnnulusPaths
import FirstAnnulusTransport
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Subpath
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Homotopy.Basic

/-! The explicit elliptic annulus used to encircle the first two marked points. -/

namespace BelgianChocolate.FirstAnnulus

open Complex Metric Set

/-- Fourth root of the rational number obtained from the two slit endpoints. -/
noncomputable def ell : ℝ := Real.sqrt (Real.sqrt (202 / 81))

noncomputable def kappa : ℝ := (ell - 1) / (ell + 1)

def annulus17 : Set ℂ := {w | 1 < ‖w‖ ∧ ‖w‖ < 17}

/-- The closed horizontal segment with endpoints `-κ` and `κ`. -/
def slit (κ : ℝ) : Set ℂ := {z | z.im = 0 ∧ |z.re| ≤ κ}

noncomputable def joukowski (κ : ℝ) (w : ℂ) : ℂ := (κ / 2 : ℝ) * (w + w⁻¹)

theorem ell_bounds : 1 < ell ∧ ell < 81/64 := by
  have h₁ := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 202/81)
  have h₂ : ell^2 = Real.sqrt (202/81) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hpos : 0 ≤ ell := Real.sqrt_nonneg _
  have h₄ : ell^4 = 202/81 := by rw [show ell^4 = (ell^2)^2 by ring, h₂, h₁]
  constructor
  · by_contra! h
    have := pow_le_pow_left₀ hpos h 4
    norm_num at this
    linarith
  · by_contra! h
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 81/64) h 4
    norm_num at this
    linarith

theorem kappa_bounds : 0 < kappa ∧ kappa < 17/145 := by
  have hl := ell_bounds
  have hd : 0 < ell + 1 := by linarith [hl.1]
  refine ⟨div_pos (by linarith [hl.1]) hd, (div_lt_iff₀ hd).mpr ?_⟩
  linarith [hl.2]

private theorem ne_zero_of_outer {w : ℂ} (hw : 1 < ‖w‖) : w ≠ 0 := by
  intro h
  norm_num [h] at hw

theorem joukowski_differentiableAt {κ : ℝ} {w : ℂ} (hw : 1 < ‖w‖) :
    DifferentiableAt ℂ (joukowski κ) w :=
  (differentiableAt_id.add (differentiableAt_id.inv (ne_zero_of_outer hw))).const_mul _

theorem joukowski_injOn {κ : ℝ} (hκ : 0 < κ) :
    InjOn (joukowski κ) {w : ℂ | 1 < ‖w‖} := by
  intro w hw v hv he
  have hw' := ne_zero_of_outer hw
  have hv' := ne_zero_of_outer hv
  have hk : ((κ / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : κ / 2 ≠ 0)
  have he' : w + w⁻¹ = v + v⁻¹ := mul_left_cancel₀ hk he
  have hf : (w-v)*(w*v-1) = 0 := by
    field_simp [hw', hv'] at he'
    linear_combination he'
  rcases mul_eq_zero.mp hf with hh | hh
  · exact sub_eq_zero.mp hh
  · have hn := congrArg norm (sub_eq_zero.mp hh)
    rw [norm_mul, norm_one] at hn
    have hgt : 1 < ‖w‖*‖v‖ := by
      change 1 < ‖v‖ at hv
      change 1 < ‖w‖ at hw
      nlinarith [mul_pos (sub_pos.mpr hw) (sub_pos.mpr hv)]
    linarith

/-- Uniform radius estimate for the entire open annulus, including its
outer limiting ellipse. -/
theorem joukowski_norm_lt_one {κ : ℝ} (hκ : 0 < κ) (hκ' : κ < 17/145)
    {w : ℂ} (hw : w ∈ annulus17) : ‖joukowski κ w‖ < 1 := by
  obtain ⟨hr,hR⟩ := hw
  let r := ‖w‖
  have hpos : 0 < r := lt_trans zero_lt_one hr
  have hrad : r + r⁻¹ < 17 + (17 : ℝ)⁻¹ := by
    have hprod : 0 < (17-r)*(17*r-1) := mul_pos (by linarith) (by linarith)
    field_simp
    nlinarith
  calc
    ‖joukowski κ w‖ = (κ/2)*‖w+w⁻¹‖ := by
      simp [joukowski, abs_of_pos hκ]
    _ ≤ (κ/2)*(r+r⁻¹) := by
      gcongr
      simpa [r] using norm_add_le w w⁻¹
    _ < (17/145 : ℝ)/2 * (17 + (17:ℝ)⁻¹) := by
      nlinarith [mul_pos (sub_pos.mpr hκ') (show 0 < r+r⁻¹ by positivity)]
    _ = 1 := by norm_num

theorem joukowski_im {κ : ℝ} {w : ℂ} :
    (joukowski κ w).im = (κ/2) * w.im * (1 - (normSq w)⁻¹) := by
  simp [joukowski, mul_im, Complex.inv_im, div_eq_mul_inv]
  ring

private theorem factor_pos {w : ℂ} (hw : 1 < ‖w‖) : 0 < 1 - (normSq w)⁻¹ := by
  have hn : 1 < normSq w := by rw [← Complex.sq_norm]; nlinarith [sq_nonneg (‖w‖-1)]
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hn)

theorem joukowski_notMem_slit {κ : ℝ} (hκ : 0 < κ) {w : ℂ} (hw : 1 < ‖w‖) :
    joukowski κ w ∉ slit κ := by
  rintro ⟨him,hre⟩
  rw [joukowski_im] at him
  have hi : w.im = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by positivity)
    · exact False.elim ((factor_pos hw).ne' h)
  have he : (w.re : ℂ) = w := by apply Complex.ext <;> simp [hi]
  have hnorm : 1 < |w.re| := by
    have ha : 1 < ‖(w.re : ℂ)‖ := by rw [he]; exact hw
    simpa only [Complex.norm_real, Real.norm_eq_abs] using ha
  have hreal : (joukowski κ w).re = (κ/2)*(w.re+w.re⁻¹) := by
    conv_lhs => rw [← he]
    simp [joukowski, ← ofReal_inv, ← ofReal_add]
  rw [hreal] at hre
  rcases lt_or_gt_of_ne (show w.re ≠ 0 by intro h; norm_num [h] at hnorm) with hneg | hpos
  · rw [abs_of_neg hneg] at hnorm
    have hsum : w.re+w.re⁻¹ < -2 := by
      have hs : 0 < (w.re+1)^2 := sq_pos_of_ne_zero (by linarith)
      calc
        w.re + w.re⁻¹ = (w.re^2+1)/w.re := by field_simp
        _ < -2 := (div_lt_iff_of_neg hneg).mpr (by nlinarith)
    have := (abs_le.mp hre).1
    nlinarith [mul_neg_of_pos_of_neg hκ (by linarith : w.re+w.re⁻¹+2 < 0)]
  · rw [abs_of_pos hpos] at hnorm
    have hsum : 2 < w.re+w.re⁻¹ := by
      have hs : 0 < (w.re-1)^2 := sq_pos_of_pos (by linarith)
      field_simp
      nlinarith
    have := (abs_le.mp hre).2
    nlinarith [mul_pos hκ (by linarith : 0 < w.re+w.re⁻¹-2)]

/-- The concrete Joukowski subembedding into the slit unit disk. -/
theorem joukowski17 :
    DifferentiableOn ℂ (joukowski kappa) annulus17 ∧
    InjOn (joukowski kappa) annulus17 ∧
    MapsTo (joukowski kappa) annulus17 (ball 0 1 \ slit kappa) := by
  refine ⟨fun _ hw ↦ (joukowski_differentiableAt hw.1).differentiableWithinAt,
    (joukowski_injOn kappa_bounds.1).mono (fun _ hw ↦ hw.1), ?_⟩
  intro w hw
  exact ⟨mem_ball_zero_iff.mpr (joukowski_norm_lt_one kappa_bounds.1 kappa_bounds.2 hw),
    joukowski_notMem_slit kappa_bounds.1 hw.1⟩

open Complex Metric Set

/-- Values of the half-plane coordinate at the two real punctures. -/
noncomputable def leftV : ℝ := Real.sqrt (6561/8080)
noncomputable def rightV : ℝ := Real.sqrt (81/40)
noncomputable def scaleV : ℝ := rightV / ell

private theorem ell_pos : 0 < ell := zero_lt_one.trans ell_bounds.1

theorem ell_fourth : ell^4 = 202/81 := by
  rw [show ell^4 = (ell^2)^2 by ring, ell, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt (by norm_num)]

theorem leftV_sq : leftV^2 = 6561/8080 := Real.sq_sqrt (by norm_num)
theorem rightV_sq : rightV^2 = 81/40 := Real.sq_sqrt (by norm_num)
theorem leftV_pos : 0 < leftV := Real.sqrt_pos.mpr (by norm_num)
theorem rightV_pos : 0 < rightV := Real.sqrt_pos.mpr (by norm_num)
theorem scaleV_pos : 0 < scaleV := div_pos rightV_pos ell_pos

theorem scaleV_endpoints :
    scaleV * (1+kappa)/(1-kappa) = rightV ∧ scaleV * (1-kappa)/(1+kappa) = leftV := by
  have h0 : ell ≠ 0 := ell_pos.ne'
  have h1 : ell+1 ≠ 0 := by linarith [ell_pos]
  have hk := kappa_bounds
  have hp : 1+kappa ≠ 0 := by linarith [hk.1]
  have hm : 1-kappa ≠ 0 := by linarith [hk.2]
  have hkp : 1+kappa = 2*ell/(ell+1) := by unfold kappa; field_simp; ring
  have hkm : 1-kappa = 2/(ell+1) := by unfold kappa; field_simp; ring
  have hratio : rightV / ell^2 = leftV := by
    apply (sq_eq_sq₀ (div_nonneg rightV_pos.le (sq_nonneg _)) leftV_pos.le).mp
    rw [div_pow, rightV_sq, leftV_sq, ← pow_mul, show 2*2=4 by norm_num, ell_fourth]
    norm_num
  constructor
  · rw [hkp, hkm, scaleV]
    field_simp
  · rw [hkp, hkm, scaleV, ← hratio]
    field_simp

theorem scaleV_eq_sqrt_product : scaleV = Real.sqrt (leftV * rightV) := by
  have h := scaleV_endpoints
  have hk := kappa_bounds
  have hp : 1+kappa ≠ 0 := by linarith [hk.1]
  have hm : 1-kappa ≠ 0 := by linarith [hk.2]
  apply (sq_eq_sq₀ scaleV_pos.le (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (mul_nonneg leftV_pos.le rightV_pos.le), ← h.1, ← h.2]
  field_simp


open Complex Metric Set
open BelgianChocolate.HarmonicComparison

private theorem nz_of_re_pos {v : ℂ} (h : 0 < v.re) : v ≠ 0 := by
  intro e
  simp [e] at h

noncomputable def radicand (v : ℂ) : ℂ := v^2 / (1+v^2)

noncomputable def inverseU (v : ℂ) : ℂ := (radicand v).sqrt

private theorem one_add_sq_ne {v : ℂ} (hv : 0 < v.re) : 1 + v^2 ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  have hr := congrArg Complex.re he
  simp [pow_two, mul_re, mul_im] at hi hr
  have : v.im = 0 := by
    by_contra hh
    exact (mul_ne_zero hv.ne' hh) (by linarith)
  nlinarith [sq_nonneg v.re]

theorem radicand_im (v : ℂ) : (radicand v).im = 2*v.re*v.im / normSq (1+v^2) := by
  rw [radicand, Complex.div_im, ← sub_div]
  congr 1
  simp [pow_two, mul_im, mul_re]
  ring

theorem radicand_mem_slit {v : ℂ} (hv : 0 < v.re) : radicand v ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : v.im = 0
  · left
    have he : (v.re : ℂ) = v := by apply Complex.ext <;> simp [hi]
    have hval : radicand (v.re : ℂ) = ((v.re^2/(1+v.re^2) : ℝ) : ℂ) := by
      simp [radicand]
    rw [← he, hval, Complex.ofReal_re]
    positivity
  · right
    rw [radicand_im]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hv.ne') hi)
      (Complex.normSq_pos.mpr (one_add_sq_ne hv)).ne'

private theorem sq_principal_sqrt (z : ℂ) : z.sqrt ^ 2 = z := by
  by_cases hz : z = 0
  · simp [hz]
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul]
  convert Complex.exp_log hz using 2
  push_cast
  ring

theorem inverseU_sq (v : ℂ) : (inverseU v)^2 = radicand v := sq_principal_sqrt _

private theorem sqrt_re_pos_of_slit {z : ℂ} (hz : z ∈ slitPlane) : 0 < z.sqrt.re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re, Real.sqrt_pos]
  have hn : 0 ≤ ‖z‖ := norm_nonneg z
  rcases Complex.mem_slitPlane_iff.mp hz with hr | hi
  · linarith
  · have h₂ := Complex.sq_norm z
    rw [Complex.normSq_apply] at h₂
    nlinarith [sq_pos_of_ne_zero hi, (abs_le.mp (Complex.abs_re_le_norm z)).1]

theorem inverseU_re_pos {v : ℂ} (hv : 0 < v.re) : 0 < (inverseU v).re :=
  sqrt_re_pos_of_slit (radicand_mem_slit hv)

theorem inverseU_differentiableAt {v : ℂ} (hv : 0 < v.re) : DifferentiableAt ℂ inverseU v := by
  have hrad : DifferentiableAt ℂ radicand v := by
    unfold radicand
    fun_prop (disch := exact one_add_sq_ne hv)
  exact (Complex.differentiableAt_sqrt (radicand_mem_slit hv)).comp v hrad

theorem inverseU_injOn : InjOn inverseU {v : ℂ | 0 < v.re} := by
  intro v hv w hw he
  have hs := congrArg (fun z : ℂ ↦ z^2) he
  change (inverseU v)^2 = (inverseU w)^2 at hs
  rw [inverseU_sq, inverseU_sq, radicand, radicand, div_eq_div_iff (one_add_sq_ne hv)
    (one_add_sq_ne hw)] at hs
  have hp : (v-w)*(v+w) = 0 := by linear_combination hs
  rcases mul_eq_zero.mp hp with h | h
  · exact sub_eq_zero.mp h
  · exact False.elim ((nz_of_re_pos (show 0 < (v+w).re from add_pos hv hw)) h)

noncomputable def inverseS (u : ℂ) : ℂ := 10 * ((11*u-9)/(11*u+9))

private theorem denomS_ne {u : ℂ} (hu : 0 < u.re) : 11*u+9 ≠ 0 := by
  apply nz_of_re_pos
  simp [Complex.mul_re]
  linarith

theorem inverseS_norm_lt {u : ℂ} (hu : 0 < u.re) : ‖inverseS u‖ < 10 := by
  have hd := denomS_ne hu
  have hsq : normSq (11*u-9) < normSq (11*u+9) := by
    simp [Complex.normSq_apply, mul_re, mul_im]
    linarith
  rw [← Complex.sq_norm, ← Complex.sq_norm] at hsq
  have hn : ‖11*u-9‖ < ‖11*u+9‖ := by nlinarith [norm_nonneg (11*u-9), norm_nonneg (11*u+9)]
  have hq : ‖11*u-9‖/‖11*u+9‖ < 1 := (div_lt_one (norm_pos_iff.mpr hd)).mpr hn
  rw [inverseS, norm_mul, norm_div]
  norm_num
  linarith

theorem inverseS_differentiableAt {u : ℂ} (hu : 0 < u.re) : DifferentiableAt ℂ inverseS u := by
  unfold inverseS
  fun_prop (disch := exact denomS_ne hu)

theorem inverseS_injOn : InjOn inverseS {u : ℂ | 0 < u.re} := by
  intro u hu v hv he
  have hq : (11*u-9)/(11*u+9) = (11*v-9)/(11*v+9) := mul_left_cancel₀ (by norm_num : (10:ℂ) ≠ 0) he
  have hh := (div_eq_div_iff (denomS_ne hu) (denomS_ne hv)).mp hq
  linear_combination (1/198 : ℂ)*hh

noncomputable def inverseV (a : ℝ) (ξ : ℂ) : ℂ := a * comparisonQuotient ξ

theorem inverseV_re_pos {a : ℝ} (ha : 0 < a) {ξ : ℂ} (hξ : ‖ξ‖ < 1) : 0 < (inverseV a ξ).re := by
  simpa [inverseV, mul_re] using mul_pos ha (comparisonQuotient_re_pos hξ)

private theorem denomV_ne {ξ : ℂ} (hξ : ‖ξ‖ < 1) : (1:ℂ)-ξ ≠ 0 := by
  intro he
  rw [← sub_eq_zero.mp he] at hξ
  simp at hξ

theorem inverseV_differentiableAt {a : ℝ} {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    DifferentiableAt ℂ (inverseV a) ξ := by
  unfold inverseV comparisonQuotient
  fun_prop (disch := exact denomV_ne hξ)

theorem inverseV_injOn {a : ℝ} (ha : 0 < a) : InjOn (inverseV a) (ball (0:ℂ) 1) := by
  intro x hx y hy he
  have hq := mul_left_cancel₀ (show (a:ℂ) ≠ 0 by exact_mod_cast ha.ne') he
  change (1+x)/(1-x) = (1+y)/(1-y) at hq
  have hcross := (div_eq_div_iff (denomV_ne (mem_ball_zero_iff.mp hx)) (denomV_ne (mem_ball_zero_iff.mp hy))).mp hq
  linear_combination (1/2 : ℂ)*hcross


open Complex Metric Set

noncomputable def realV (x : ℝ) := scaleV*(1+x)/(1-x)
noncomputable def realU (v : ℝ) := Real.sqrt (v^2/(1+v^2))
noncomputable def realS (u : ℝ) := 10*((11*u-9)/(11*u+9))
noncomputable def realInverse (x : ℝ) := realS (realU (realV x))

private theorem realV_pos {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : 0 < realV x :=
  div_pos (mul_pos scaleV_pos (by linarith [hx.1])) (by linarith [hx.2])

private theorem realV_mono : StrictMonoOn realV (Ioo (-1:ℝ) 1) := by
  intro x hx y hy hxy
  apply (div_lt_div_iff₀ (by linarith [hx.2]) (by linarith [hy.2])).mpr
  nlinarith [mul_pos scaleV_pos (sub_pos.mpr hxy)]

private theorem realU_pos {v : ℝ} (hv : 0 < v) : 0 < realU v :=
  Real.sqrt_pos.mpr (by positivity)

private theorem realU_mono : StrictMonoOn realU (Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  apply Real.sqrt_lt_sqrt (by positivity)
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_lt_sq' (by linarith [show 0 < x from hx]) hxy]

private theorem realS_mono : StrictMonoOn realS (Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 10)
  apply (div_lt_div_iff₀ (by linarith [show 0 < x from hx]) (by linarith [show 0 < y from hy])).mpr
  nlinarith

theorem realInverse_mono : StrictMonoOn realInverse (Ioo (-1:ℝ) 1) := by
  intro x hx y hy hxy
  exact realS_mono (realU_pos (realV_pos hx)) (realU_pos (realV_pos hy))
    (realU_mono (realV_pos hx) (realV_pos hy) (realV_mono hx hy hxy))

theorem realInverse_lt_one {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : realInverse x < 1 := by
  let v := realV x
  let u := realU v
  have hv : 0 < v := realV_pos hx
  have hu : 0 < u := realU_pos hv
  have h1 : u < 1 := by
    apply (Real.sqrt_lt' zero_lt_one).mpr
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  change 10 * ((11*u-9)/(11*u+9)) < 1
  rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0 < 11*u+9)]
  linarith


open Complex Metric Set
open BelgianChocolate.HarmonicComparison

/-- Inverse of the three changes of variable in the slit disk. -/
noncomputable def slitDiskInverse (ξ : ℂ) : ℂ := inverseS (inverseU (inverseV scaleV ξ))

private theorem vpos {ξ : ℂ} (hξ : ‖ξ‖ < 1) : 0 < (inverseV scaleV ξ).re :=
  inverseV_re_pos scaleV_pos hξ

theorem slitDiskInverse_differentiableAt {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    DifferentiableAt ℂ slitDiskInverse ξ := by
  change DifferentiableAt ℂ (inverseS ∘ inverseU ∘ inverseV scaleV) ξ
  apply DifferentiableAt.comp (f := inverseU ∘ inverseV scaleV) (g := inverseS) ξ
  · exact inverseS_differentiableAt (inverseU_re_pos (vpos hξ))
  · apply DifferentiableAt.comp (f := inverseV scaleV) (g := inverseU) ξ
    · exact inverseU_differentiableAt (vpos hξ)
    · exact inverseV_differentiableAt hξ

theorem slitDiskInverse_injOn : InjOn slitDiskInverse (ball (0:ℂ) 1) := by
  intro ξ hξ η hη he
  have hvξ := vpos (mem_ball_zero_iff.mp hξ)
  have hvη := vpos (mem_ball_zero_iff.mp hη)
  exact inverseV_injOn scaleV_pos hξ hη (inverseU_injOn hvξ hvη
    (inverseS_injOn (inverseU_re_pos hvξ) (inverseU_re_pos hvη) he))

theorem slitDiskInverse_norm_lt {ξ : ℂ} (hξ : ‖ξ‖ < 1) : ‖slitDiskInverse ξ‖ < 10 :=
  inverseS_norm_lt (inverseU_re_pos (vpos hξ))

private theorem inverseU_real {v : ℝ} (hv : 0 < v) :
    inverseU (v : ℂ) = ((Real.sqrt (v^2/(1+v^2)) : ℝ) : ℂ) := by
  have hr : radicand (v:ℂ) = ((v^2/(1+v^2) : ℝ) : ℂ) := by simp [radicand]
  have hn : 0 ≤ v^2/(1+v^2) := by positivity
  rw [inverseU, hr, Complex.sqrt_of_nonneg (by exact_mod_cast hn), Complex.ofReal_re]

private theorem inverseV_real (a x : ℝ) :
    inverseV a (x : ℂ) = ((a * (1+x)/(1-x) : ℝ) : ℂ) := by
  simp [inverseV, comparisonQuotient, mul_div_assoc]

private theorem inverseS_real (x : ℝ) :
    inverseS (x : ℂ) = ((10*((11*x-9)/(11*x+9)) : ℝ) : ℂ) := by simp [inverseS]

theorem slitDiskInverse_real {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    slitDiskInverse (x : ℂ) = ((realInverse x : ℝ) : ℂ) := by
  have hp : 0 < scaleV*(1+x)/(1-x) :=
    div_pos (mul_pos scaleV_pos (by linarith [hx.1])) (by linarith [hx.2])
  rw [slitDiskInverse, inverseV_real, inverseU_real hp, inverseS_real]
  rfl

theorem slitDiskInverse_endpoints :
    slitDiskInverse (-kappa : ℝ) = -1 ∧ slitDiskInverse (kappa : ℝ) = 0 := by
  have hL : Real.sqrt (leftV^2/(1+leftV^2)) = 81/121 := by
    rw [leftV_sq]; norm_num
  have hR : Real.sqrt (rightV^2/(1+rightV^2)) = 9/11 := by
    rw [rightV_sq]; norm_num
  constructor
  · change inverseS (inverseU (inverseV scaleV ((-kappa : ℝ) : ℂ))) = -1
    rw [inverseV_real, show 1 + -kappa = 1-kappa by ring, sub_neg_eq_add,
      scaleV_endpoints.2, inverseU_real leftV_pos, hL, inverseS_real]
    norm_num
  · change inverseS (inverseU (inverseV scaleV (kappa : ℂ))) = 0
    rw [inverseV_real, scaleV_endpoints.1, inverseU_real rightV_pos, hR, inverseS_real]
    norm_num

/-- The missing radial slit starts at 1.  Its initial endpoint has no inverse image. -/
theorem slitDiskInverse_ne_one {ξ : ℂ} (hξ : ‖ξ‖ < 1) : slitDiskInverse ξ ≠ 1 := by
  let v := inverseV scaleV ξ
  let u := inverseU v
  have hv : 0 < v.re := vpos hξ
  have hu : 0 < u.re := inverseU_re_pos hv
  have hd : 11*u+9 ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp [mul_re] at this
    linarith
  intro he
  change 10*((11*u-9)/(11*u+9)) = 1 at he
  field_simp [hd] at he
  have hu1 : u = 1 := by linear_combination (1/99:ℂ)*he
  have hs := inverseU_sq v
  change u^2 = v^2/(1+v^2) at hs
  by_cases hdv : 1+v^2 = 0
  · simp [hu1, hdv] at hs
  · rw [hu1, one_pow, eq_div_iff hdv] at hs
    exact one_ne_zero (by linear_combination hs : (1:ℂ) = 0)

/-- Holomorphic injection of the explicit annulus into the normalized punctured
disk. The three omitted values are the normalized source marks. -/
theorem normalized_embedding :
    DifferentiableOn ℂ (slitDiskInverse ∘ joukowski kappa) annulus17 ∧
    InjOn (slitDiskInverse ∘ joukowski kappa) annulus17 ∧
    MapsTo (slitDiskInverse ∘ joukowski kappa) annulus17
      {s : ℂ | ‖s‖ < 10 ∧ s ≠ -1 ∧ s ≠ 0 ∧ s ≠ 1} := by
  have hmaps : MapsTo (joukowski kappa) annulus17 (ball 0 1) :=
    fun w hw ↦ (joukowski17.2.2 hw).1
  have hκ : |kappa| < 1 := by rw [abs_of_pos kappa_bounds.1]; linarith [kappa_bounds.2]
  have hL : ((-kappa:ℝ):ℂ) ∈ ball 0 1 := by simpa [mem_ball_zero_iff] using hκ
  have hR : (kappa:ℂ) ∈ ball 0 1 := by simpa [mem_ball_zero_iff] using hκ
  have hLs : ((-kappa:ℝ):ℂ) ∈ slit kappa := by simp [slit, abs_of_pos kappa_bounds.1]
  have hRs : (kappa:ℂ) ∈ slit kappa := by simp [slit, abs_of_pos kappa_bounds.1]
  refine ⟨(fun w hw ↦ ((slitDiskInverse_differentiableAt
    (mem_ball_zero_iff.mp (hmaps hw))).comp w (joukowski_differentiableAt hw.1)).differentiableWithinAt),
    slitDiskInverse_injOn.comp joukowski17.2.1 hmaps, ?_⟩
  intro w hw
  have hξ := hmaps hw
  have hs := (joukowski17.2.2 hw).2
  refine ⟨slitDiskInverse_norm_lt (mem_ball_zero_iff.mp hξ), ?_, ?_,
    slitDiskInverse_ne_one (mem_ball_zero_iff.mp hξ)⟩
  · intro he
    exact hs ((slitDiskInverse_injOn hξ hL (he.trans slitDiskInverse_endpoints.1.symm)) ▸ hLs)
  · intro he
    exact hs ((slitDiskInverse_injOn hξ hR (he.trans slitDiskInverse_endpoints.2.symm)) ▸ hRs)


open Complex Metric Set
open BelgianChocolate.HarmonicComparison

/-- The affine return to the original source disk, with its three marked points. -/
noncomputable def sourceEmbedding (t : ℝ) (w : ℂ) : ℂ :=
  (-I*(t:ℂ)) * slitDiskInverse (joukowski kappa w)

theorem source_embedding {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    DifferentiableOn ℂ (sourceEmbedding t) annulus17 ∧ InjOn (sourceEmbedding t) annulus17 ∧
      MapsTo (sourceEmbedding t) annulus17
        {z : ℂ | ‖z‖ < 1 ∧ z ≠ 0 ∧ z ≠ I*(t:ℂ) ∧ z ≠ -(I*(t:ℂ))} := by
  let c := -I*(t:ℂ)
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast ht.ne')
  have hcn : ‖c‖ = t := by simp [c, abs_of_pos ht]
  have hinj := normalized_embedding.2.1
  refine ⟨normalized_embedding.1.const_mul c, ?_, ?_⟩
  · intro w hw v hv he
    exact hinj hw hv (mul_left_cancel₀ hc he)
  · intro w hw
    let s := slitDiskInverse (joukowski kappa w)
    have hs : ‖s‖ < 10 ∧ s ≠ -1 ∧ s ≠ 0 ∧ s ≠ 1 := normalized_embedding.2.2 hw
    change ‖c*s‖ < 1 ∧ c*s ≠ 0 ∧ c*s ≠ I*(t:ℂ) ∧ c*s ≠ -(I*(t:ℂ))
    refine ⟨?_, mul_ne_zero hc hs.2.2.1, ?_, ?_⟩
    · rw [norm_mul, hcn]
      have h := mul_lt_mul_of_pos_left hs.1 ht
      linarith
    · intro he
      exact hs.2.1 (mul_left_cancel₀ hc (he.trans (by dsimp [c]; ring : I*(t:ℂ) = c*(-1))))
    · intro he
      exact hs.2.2.2 (mul_left_cancel₀ hc (he.trans (by dsimp [c]; ring : -(I*(t:ℂ)) = c*1)))

private theorem inverseS_im (u : ℂ) :
    (inverseS u).im = (1980/normSq (11*u+9)) * u.im := by
  unfold inverseS
  simp only [Complex.mul_im, Complex.div_im]
  norm_num
  ring

private theorem inverseU_im_factor {v : ℂ} (hv : 0 < v.re) :
    ∃ c : ℝ, 0 < c ∧ (inverseU v).im = c*v.im := by
  have hu := inverseU_re_pos hv
  have h := congrArg Complex.im (inverseU_sq v)
  simp only [pow_two, mul_im, radicand_im] at h
  have hd : 0 < normSq (1+v^2) := by
    apply Complex.normSq_pos.mpr
    intro he
    have hi := congrArg Complex.im he
    have hr := congrArg Complex.re he
    simp [pow_two, mul_re, mul_im] at hi hr
    have h0 : v.im = 0 := by
      by_contra hh
      exact (mul_ne_zero hv.ne' hh) (by linarith)
    nlinarith [sq_nonneg v.re]
  refine ⟨v.re / ((inverseU v).re*normSq (1+v^2)), by positivity, ?_⟩
  field_simp at h ⊢
  linarith

/-- The inverse conformal coordinate preserves the sign of the imaginary part. -/
theorem slitDiskInverse_im_factor {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    ∃ c : ℝ, 0 < c ∧ (slitDiskInverse ξ).im = c*ξ.im := by
  let v := inverseV scaleV ξ
  let u := inverseU v
  have hv : 0 < v.re := inverseV_re_pos scaleV_pos hξ
  have hu : 0 < u.re := inverseU_re_pos hv
  obtain ⟨c,hc,hui⟩ := inverseU_im_factor hv
  have hd : 0 < normSq (11*u+9) := by
    apply Complex.normSq_pos.mpr
    intro he
    have hr := congrArg Complex.re he
    simp [mul_re] at hr
    linarith
  have hξd : 0 < normSq (1-ξ) := by
    apply Complex.normSq_pos.mpr
    intro he
    rw [← sub_eq_zero.mp he] at hξ
    simp at hξ
  have hvi : v.im = scaleV*(2*ξ.im/normSq (1-ξ)) := by
    simp [v, inverseV, mul_im, comparisonQuotient_im]
  refine ⟨(1980/normSq (11*u+9))*c*(scaleV*2/normSq (1-ξ)),
    by have := scaleV_pos; positivity, ?_⟩
  change (inverseS u).im = _
  rw [inverseS_im, show u.im = c*v.im from hui, hvi]
  ring


open Complex Metric Set

/-- The constants coincide with the two original real images in the slit
coordinate, for `β = (9/11)^2`. -/
theorem slit_endpoints_beta :
    let β : ℝ := 81/121
    leftV = β / Real.sqrt (1-β^2) ∧ rightV = Real.sqrt (β/(1-β)) := by
  dsimp
  constructor
  · apply (sq_eq_sq₀ leftV_pos.le (by positivity)).mp
    rw [leftV_sq, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  · unfold rightV
    congr 1
    norm_num

theorem ell_eq_sqrt_ratio : ell = Real.sqrt (rightV/leftV) := by
  apply (sq_eq_sq₀ (le_of_lt (lt_trans zero_lt_one ell_bounds.1))
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (div_nonneg rightV_pos.le leftV_pos.le)]
  apply (sq_eq_sq₀ (sq_nonneg _) (div_nonneg rightV_pos.le leftV_pos.le)).mp
  rw [← pow_mul, show 2*2=4 by norm_num, ell_fourth, div_pow, rightV_sq, leftV_sq]
  norm_num

open Complex Metric Set

/-- The positively oriented core in the normalized source plane. -/
noncomputable def normalizedCore (θ : ℝ) : ℂ :=
  slitDiskInverse (joukowski kappa (circleMap 0 2 θ))

theorem core_mem_annulus (θ : ℝ) : circleMap 0 2 θ ∈ annulus17 := by
  change 1 < ‖circleMap 0 2 θ‖ ∧ ‖circleMap 0 2 θ‖ < 17
  norm_num [norm_circleMap_zero]

theorem normalizedCore_mem (θ : ℝ) : ‖normalizedCore θ‖ < 10 ∧
    normalizedCore θ ≠ -1 ∧ normalizedCore θ ≠ 0 ∧ normalizedCore θ ≠ 1 :=
  normalized_embedding.2.2 (core_mem_annulus θ)

/-- The normalized R17 annulus avoids the full real cut starting at 1. -/
theorem slitDiskInverse_re_lt_one_of_im_eq_zero {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (hi : (slitDiskInverse ξ).im = 0) : (slitDiskInverse ξ).re < 1 := by
  obtain ⟨c,hc,he⟩ := slitDiskInverse_im_factor hξ
  have hξi := (mul_eq_zero.mp (he.symm.trans hi)).resolve_left hc.ne'
  have heξ : (ξ.re : ℂ) = ξ := by apply Complex.ext <;> simp [hξi]
  have hnorm : ‖(ξ.re : ℂ)‖ < 1 := by rw [heξ]; exact hξ
  have hr : ξ.re ∈ Ioo (-1:ℝ) 1 := by simpa [Real.norm_eq_abs, abs_lt] using hnorm
  rw [← heξ, slitDiskInverse_real hr, Complex.ofReal_re]
  exact realInverse_lt_one hr

theorem normalizedCore_re_crossings :
    (normalizedCore 0).im = 0 ∧ (normalizedCore 0).re ∈ Ioo (0:ℝ) 1 ∧
    (normalizedCore Real.pi).im = 0 ∧ (normalizedCore Real.pi).re ∈ Ioo (-10:ℝ) (-1) := by
  let x := (5/4:ℝ)*kappa
  have hk := kappa_bounds
  have hx₀ : kappa < x := by dsimp [x]; linarith [hk.1]
  have hx₁ : x < 1 := by dsimp [x]; linarith [hk.2]
  have hx : x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hk.1],hx₁⟩
  have hmx : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,by linarith [hk.1]⟩
  have hκ : kappa ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hmκ : -kappa ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hk.2], by linarith [hk.1]⟩
  have hzero : realInverse kappa = 0 := by
    have h := slitDiskInverse_endpoints.2
    rw [slitDiskInverse_real hκ] at h
    exact_mod_cast h
  have hneg : realInverse (-kappa) = -1 := by
    have h := slitDiskInverse_endpoints.1
    rw [slitDiskInverse_real hmκ] at h
    exact_mod_cast h
  have hjR : joukowski kappa (2:ℂ) = (x:ℂ) := by
    push_cast [joukowski,x]
    ring
  have hjL : joukowski kappa (-2:ℂ) = ((-x:ℝ):ℂ) := by
    push_cast [joukowski,x]
    ring
  have hR : normalizedCore 0 = (realInverse x : ℂ) := by
    simpa [normalizedCore, circleMap_zero, hjR] using slitDiskInverse_real hx
  have hL : normalizedCore Real.pi = (realInverse (-x) : ℂ) := by
    simpa [normalizedCore, circleMap_zero, Complex.exp_pi_mul_I, hjL] using slitDiskInverse_real hmx
  have hLnorm := (normalizedCore_mem Real.pi).1
  rw [hL, Complex.norm_real, Real.norm_eq_abs, abs_lt] at hLnorm
  rw [hR,hL]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  exact ⟨⟨hzero ▸ realInverse_mono hκ hx hx₀, realInverse_lt_one hx⟩,
    ⟨hLnorm.1,hneg ▸ realInverse_mono hmx hmκ (neg_lt_neg hx₀)⟩⟩

/-- At every core parameter the imaginary part is a positive multiple of sine. -/
theorem normalizedCore_im_factor (θ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ (normalizedCore θ).im = c * Real.sin θ := by
  let w := circleMap 0 2 θ
  have hw : w ∈ annulus17 := core_mem_annulus θ
  have hξ := joukowski_norm_lt_one kappa_bounds.1 kappa_bounds.2 hw
  obtain ⟨c,hc,h⟩ := slitDiskInverse_im_factor hξ
  have hwi : w.im = 2*Real.sin θ := by simp [w, circleMap_zero, mul_im, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  have hnorm : normSq w = 4 := by
    rw [← Complex.sq_norm]
    norm_num [w,norm_circleMap_zero]
  refine ⟨c*(kappa/2)*2*(1-(4:ℝ)⁻¹), by have := kappa_bounds.1; positivity, ?_⟩
  change (slitDiskInverse (joukowski kappa w)).im = _
  rw [h, joukowski_im, hnorm, hwi]
  ring

theorem normalizedCore_upper {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    0 < (normalizedCore θ).im := by
  obtain ⟨c,hc,h⟩ := normalizedCore_im_factor θ
  rw [h]
  exact mul_pos hc (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

theorem normalizedCore_lower {θ : ℝ} (hθ : θ ∈ Ioo Real.pi (2*Real.pi)) :
    (normalizedCore θ).im < 0 := by
  obtain ⟨c,hc,h⟩ := normalizedCore_im_factor θ
  have hs := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hθ.2] : θ-2*Real.pi < 0)
      (by linarith [hθ.1] : -Real.pi < θ-2*Real.pi)
  rw [Real.sin_sub_two_pi] at hs
  rw [h]
  exact mul_neg_of_pos_of_neg hc hs

open Complex Metric Set unitInterval
open BelgianChocolate.FirstAnnulusPaths

/-- Core and comparison circle, parametrized by the same oriented unit circle. -/
noncomputable def coreValue (ζ : Circle) : ℂ := slitDiskInverse (joukowski kappa (2*(ζ:ℂ)))
noncomputable def referenceValue (ζ : Circle) : ℂ := -(1/2:ℂ) + (3/4:ℂ)*(ζ:ℂ)

private theorem twice_mem (ζ : Circle) : (2:ℂ)*(ζ:ℂ) ∈ annulus17 := by
  change 1 < ‖(2:ℂ)*(ζ:ℂ)‖ ∧ ‖(2:ℂ)*(ζ:ℂ)‖ < 17
  norm_num [norm_mul]

private theorem continuous_coreValue : Continuous coreValue := by
  apply continuous_iff_continuousAt.mpr
  intro ζ
  have hw := twice_mem ζ
  have hξ := joukowski_norm_lt_one kappa_bounds.1 kappa_bounds.2 hw
  have h₁ : Continuous (fun η : Circle ↦ (2:ℂ)*(η:ℂ)) := by fun_prop
  have h₂ : ContinuousAt (joukowski kappa) (2*(ζ:ℂ)) := (joukowski_differentiableAt hw.1).continuousAt
  have h₃ := (slitDiskInverse_differentiableAt hξ).continuousAt
  change ContinuousAt ((slitDiskInverse ∘ joukowski kappa) ∘ (fun η : Circle ↦ (2:ℂ)*(η:ℂ))) ζ
  apply ContinuousAt.comp (f := fun η : Circle ↦ (2:ℂ)*(η:ℂ)) (g := slitDiskInverse ∘ joukowski kappa)
  · exact h₃.comp h₂
  · exact h₁.continuousAt

private theorem continuous_referenceValue : Continuous referenceValue := by unfold referenceValue; fun_prop

private theorem coreValue_im_factor (ζ : Circle) :
    ∃ c : ℝ, 0 < c ∧ (coreValue ζ).im = c*(ζ:ℂ).im := by
  let w : ℂ := 2*(ζ:ℂ)
  have hw := twice_mem ζ
  have hξ := joukowski_norm_lt_one kappa_bounds.1 kappa_bounds.2 hw
  obtain ⟨c,hc,h⟩ := slitDiskInverse_im_factor hξ
  have hwi : w.im = 2*(ζ:ℂ).im := by simp [w, mul_im]
  have hnorm : normSq w = 4 := by rw [← Complex.sq_norm]; norm_num [w,norm_mul]
  refine ⟨c*(kappa/2)*2*(1-(4:ℝ)⁻¹), by have := kappa_bounds.1; positivity, ?_⟩
  change (slitDiskInverse (joukowski kappa w)).im = _
  rw [h, joukowski_im, hnorm, hwi]
  ring

private theorem circle_real_cases (ζ : Circle) (h : (ζ:ℂ).im = 0) :
    (ζ:ℂ) = 1 ∨ (ζ:ℂ) = -1 := by
  have hs := Complex.sq_norm (ζ:ℂ)
  rw [Circle.norm_coe, one_pow, Complex.normSq_apply, h] at hs
  have hf : ((ζ:ℂ).re-1)*((ζ:ℂ).re+1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with hr | hr
  · left
    apply Complex.ext <;> simp [h, sub_eq_zero.mp hr]
  · right
    have hv : (ζ:ℂ).re = -1 := by linarith
    apply Complex.ext <;> simp [h,hv]

noncomputable def coreBlend (a : ℝ) (ζ : Circle) : ℂ :=
  (1-a) • coreValue ζ + a • referenceValue ζ

private theorem coreBlend_gates (a : unitInterval) (ζ : Circle) (hi : (coreBlend a ζ).im = 0) :
    (coreBlend a ζ).re ∈ Ioo (0:ℝ) 1 ∨ (coreBlend a ζ).re ∈ Ioo (-10:ℝ) (-1) := by
  obtain ⟨c,hc,hci⟩ := coreValue_im_factor ζ
  have hai : 0 ≤ (a:ℝ) := a.2.1
  have ha : 0 ≤ 1-(a:ℝ) := sub_nonneg.mpr a.2.2
  have hcoef : 0 < (1-(a:ℝ))*c + (a:ℝ)*(3/4) := by
    by_cases h : (a:ℝ) = 1
    · rw [h]; norm_num
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (lt_of_le_of_ne a.2.2 h)) hc)
        (mul_nonneg hai (by norm_num))
  have href : (referenceValue ζ).im = (3/4)*(ζ:ℂ).im := by simp [referenceValue,mul_im]
  have him : (coreBlend a ζ).im = ((1-(a:ℝ))*c + (a:ℝ)*(3/4))*(ζ:ℂ).im := by
    simp only [coreBlend, Complex.add_im, Complex.smul_im, hci, href, smul_eq_mul]
    ring
  have hzi := (mul_eq_zero.mp (him.symm.trans hi)).resolve_left hcoef.ne'
  have hgate {l r : ℝ} (h₁ : (coreValue ζ).re ∈ Ioo l r) (h₂ : (referenceValue ζ).re ∈ Ioo l r) :
      (coreBlend a ζ).re ∈ Ioo l r := by
    simpa only [coreBlend, Complex.add_re, Complex.smul_re, smul_eq_mul] using
      (convex_Ioo l r h₁ h₂ ha hai (by ring))
  rcases circle_real_cases ζ hzi with hζ | hζ
  · left
    apply hgate
    · have he : coreValue ζ = normalizedCore 0 := by simp [coreValue,normalizedCore,circleMap_zero,hζ]
      exact he ▸ normalizedCore_re_crossings.2.1
    · norm_num [referenceValue,hζ]
  · right
    apply hgate
    · have he : coreValue ζ = normalizedCore Real.pi := by
        simp [coreValue,normalizedCore,circleMap_zero,hζ,Complex.exp_pi_mul_I]
      exact he ▸ normalizedCore_re_crossings.2.2.2
    · norm_num [referenceValue,hζ]

theorem coreBlend_mem_cut {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    (a : unitInterval) (ζ : Circle) : coreBlend a ζ ∈ cutDomain t := by
  have hR : 10 ≤ 1/t := (le_div_iff₀ ht).mpr (by linarith)
  have hc : coreValue ζ ∈ ball (0:ℂ) 10 := mem_ball_zero_iff.mpr
    (normalized_embedding.2.2 (twice_mem ζ)).1
  have hr : referenceValue ζ ∈ ball (0:ℂ) 10 := by
    apply mem_ball_zero_iff.mpr
    calc
      ‖referenceValue ζ‖ ≤ ‖-(1/2:ℂ)‖ + ‖(3/4:ℂ)*(ζ:ℂ)‖ := norm_add_le _ _
      _ < 10 := by norm_num [norm_div,norm_mul]
  have hb : coreBlend a ζ ∈ ball (0:ℂ) 10 := (convex_ball (0:ℂ) 10) hc hr
    (sub_nonneg.mpr a.2.2) a.2.1 (by ring)
  refine ⟨(mem_ball_zero_iff.mp hb).trans_le hR, ?_, ?_, ?_⟩
  · rintro ⟨hi,hre,_⟩
    rcases coreBlend_gates a ζ hi with h | h <;> linarith [h.2]
  · intro he
    have hi : (coreBlend a ζ).im = 0 := by rw [he]; simp
    rcases coreBlend_gates a ζ hi with h | h <;> norm_num [he] at h
  · intro he
    have hi : (coreBlend a ζ).im = 0 := by rw [he]; simp
    rcases coreBlend_gates a ζ hi with h | h <;> norm_num [he] at h

private theorem continuous_blend : Continuous (fun q : unitInterval × Circle ↦ coreBlend q.1 q.2) := by
  unfold coreBlend
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_coreValue.comp continuous_snd) |>.add
      ((continuous_subtype_val.comp continuous_fst).smul (continuous_referenceValue.comp continuous_snd))

noncomputable def coreCircle (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1/10) : C(Circle, cutDomain t) where
  toFun ζ := ⟨coreValue ζ, by simpa [coreBlend] using coreBlend_mem_cut ht ht' 0 ζ⟩
  continuous_toFun := continuous_coreValue.subtype_mk _

noncomputable def referenceCircle (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1/10) : C(Circle, cutDomain t) where
  toFun ζ := ⟨referenceValue ζ, by simpa [coreBlend] using coreBlend_mem_cut ht ht' 1 ζ⟩
  continuous_toFun := continuous_referenceValue.subtype_mk _

/-- A concrete free homotopy in the full slit and punctured source domain.
At the positive starting point the basepoint moves along the right real gate. -/
noncomputable def coreToReferenceHomotopy (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1/10) :
    (coreCircle t ht ht').Homotopy (referenceCircle t ht ht') where
  toFun q := ⟨coreBlend q.1 q.2, coreBlend_mem_cut ht ht' _ _⟩
  continuous_toFun := continuous_blend.subtype_mk _
  map_zero_left ζ := Subtype.ext (by simp [coreCircle,coreBlend])
  map_one_left ζ := Subtype.ext (by simp [referenceCircle,coreBlend])

open Complex Metric Set unitInterval
open BelgianChocolate.FirstAnnulusPaths

/-- One positive turn, with the starting point at the right real crossing. -/
noncomputable def positiveCircleLoop : Path (1:Circle) 1 where
  toFun s := Circle.exp ((2*Real.pi)*(s:ℝ))
  continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by simp

theorem coreValue_positiveLoop (s : unitInterval) :
    coreValue (positiveCircleLoop s) = normalizedCore ((2*Real.pi)*(s:ℝ)) := by
  unfold coreValue normalizedCore
  rw [circleMap_zero]
  rfl

theorem referenceValue_positiveLoop (s : unitInterval) :
    referenceValue (positiveCircleLoop s) =
      -(1/2:ℂ)+(3/4:ℂ)*Complex.exp ((((2*Real.pi)*(s:ℝ):ℝ):ℂ)*Complex.I) := rfl

/-- The actual positive core, after moving the basepoint along the right-hand
gate, has the same based homotopy class as the positive reference circle. -/
theorem core_reference_tailed {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    let H := coreToReferenceHomotopy t ht ht'
    (((H.evalAt 1).trans (positiveCircleLoop.map (referenceCircle t ht ht').continuous)).trans
      (H.evalAt 1).symm).Homotopic (positiveCircleLoop.map (coreCircle t ht ht').continuous) :=
  BelgianChocolate.FirstAnnulusTransport.free_homotopy_tailed_homotopy
    (coreToReferenceHomotopy t ht ht') positiveCircleLoop

open Complex Metric Set unitInterval
open BelgianChocolate.FirstAnnulusPaths

/-- The explicit reference loop starts at the right gate and is traversed counterclockwise. -/
noncomputable def referenceLoop {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :=
  positiveCircleLoop.map (referenceCircle t ht ht').continuous

noncomputable def halfTurn : unitInterval := ⟨1/2, by constructor <;> norm_num⟩

theorem referenceLoop_formula {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (s : unitInterval) :
    (((referenceLoop ht ht') s : cutDomain t):ℂ) =
      -(1/2:ℂ)+(3/4:ℂ)*Complex.exp ((((2*Real.pi)*(s:ℝ):ℝ):ℂ)*Complex.I) := rfl

theorem referenceLoop_im {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (s : unitInterval) :
    (((referenceLoop ht ht') s : cutDomain t):ℂ).im = (3/4)*Real.sin (2*Real.pi*(s:ℝ)) := by
  have he (u : ℝ) : (Complex.exp ((u:ℂ)*Complex.I)).im = Real.sin u := by
    simp [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [referenceLoop_formula]
  generalize 2*Real.pi*(s:ℝ) = θ
  simp only [Complex.add_im, Complex.neg_im, Complex.mul_im]
  norm_num [he]

theorem referenceLoop_gate_values {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    (((referenceLoop ht ht') 0 : cutDomain t):ℂ) = 1/4 ∧
    (((referenceLoop ht ht') halfTurn : cutDomain t):ℂ) = -5/4 ∧
    (((referenceLoop ht ht') 1 : cutDomain t):ℂ) = 1/4 := by
  have hz : (((referenceLoop ht ht') 0 : cutDomain t):ℂ) = 1/4 := by
    rw [referenceLoop_formula]
    norm_num
  refine ⟨hz, ?_, ?_⟩
  · rw [referenceLoop_formula]
    change -(1/2:ℂ)+(3/4:ℂ)*Complex.exp ((((2*Real.pi)*(1/2):ℝ):ℂ)*Complex.I) = -5/4
    rw [show (2*Real.pi)*(1/2:ℝ) = Real.pi by ring, Complex.exp_pi_mul_I]
    norm_num
  · rw [show (referenceLoop ht ht') 1 = (referenceLoop ht ht') 0 from
      (referenceLoop ht ht').target.trans (referenceLoop ht ht').source.symm]
    exact hz

/-- Upper and lower halves of the positive reference loop, with matching
endpoints represented in the same slit domain as the two marked loops. -/
theorem referenceLoop_halves {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    let γ := referenceLoop ht ht'
    ((γ.subpath 0 halfTurn).trans (γ.subpath halfTurn 1)).Homotopic
      (γ.cast γ.source γ.target) := by
  dsimp only
  rw [← Path.subpath_zero_one]
  exact Path.Homotopic.subpath_trans_subpath _ _ _ _

theorem referenceLoop_upper_im {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {s : unitInterval} (hs : (s:ℝ) ∈ Ioo 0 1) :
    0 < ((((referenceLoop ht ht').subpath 0 halfTurn s : cutDomain t):ℂ)).im := by
  change 0 < (((referenceLoop ht ht') (Icc.convexComb 0 halfTurn s) : cutDomain t):ℂ).im
  rw [referenceLoop_im, Icc.coe_convexComb]
  apply mul_pos (by norm_num)
  apply Real.sin_pos_of_pos_of_lt_pi <;> dsimp [halfTurn] <;>
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos hs.1,
      mul_pos Real.pi_pos (sub_pos.mpr hs.2)]

theorem referenceLoop_lower_im {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {s : unitInterval} (hs : (s:ℝ) ∈ Ioo 0 1) :
    ((((referenceLoop ht ht').subpath halfTurn 1 s : cutDomain t):ℂ)).im < 0 := by
  change (((referenceLoop ht ht') (Icc.convexComb halfTurn 1 s) : cutDomain t):ℂ).im < 0
  rw [referenceLoop_im, Icc.coe_convexComb]
  apply mul_neg_of_pos_of_neg (by norm_num)
  let θ := 2*Real.pi*((1-(s:ℝ))*(1/2)+(s:ℝ)*1)
  change Real.sin θ < 0
  rw [← Real.sin_sub_two_pi]
  apply Real.sin_neg_of_neg_of_neg_pi_lt <;> dsimp [θ] <;>
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos hs.1,
      mul_pos Real.pi_pos (sub_pos.mpr hs.2)]

open Complex
open BelgianChocolate.FirstAnnulusPaths

/-- Scaling the embedded source annulus gives precisely its normalized coordinate. -/
theorem scale_sourceEmbedding {t : ℝ} (ht : 0 < t) (w : ℂ) :
    scale t (sourceEmbedding t w) = slitDiskInverse (joukowski kappa w) := by
  have ht₀ : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold scale sourceEmbedding
  rw [show Complex.I * (-Complex.I * (t:ℂ) * slitDiskInverse (joukowski kappa w)) =
      (Complex.I * -Complex.I)*((t:ℂ)*slitDiskInverse (joukowski kappa w)) by ring]
  simp [ht₀, mul_div_cancel_left₀]

/-- The entire embedded annulus lies in the same cut and punctured source
domain as the based loops, for every positive source parameter up to 1/10. -/
theorem normalized_embedding_mapsTo_cut {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    MapsTo (slitDiskInverse ∘ joukowski kappa) annulus17 (cutDomain t) := by
  intro w hw
  have hs := normalized_embedding.2.2 hw
  have hξ := joukowski_norm_lt_one kappa_bounds.1 kappa_bounds.2 hw
  have hR : 10 ≤ 1/t := (le_div_iff₀ ht).mpr (by linarith)
  refine ⟨hs.1.trans_le hR, ?_, hs.2.2.1, hs.2.1⟩
  rintro ⟨hi,hr,_⟩
  exact (not_lt_of_ge hr) (slitDiskInverse_re_lt_one_of_im_eq_zero hξ hi)

end BelgianChocolate.FirstAnnulus
