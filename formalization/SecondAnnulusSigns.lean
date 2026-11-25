import ModularLambdaJ
import ModularLambdaReflection
import SecondAnnulusCentralizer
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Signs on the real source diameter and on the modular vertical lines. -/

namespace BelgianChocolate.SecondAnnulus

open Complex Set Filter UpperHalfPlane Topology
open BelgianChocolate.ModularLambdaRatio BelgianChocolate.FirstAnnulus

private theorem re_eq_zero_imp_eq_zero {z : ℂ} (hz : z = star z) (hr : z.re = 0) :
    z = 0 := by
  have hi := congrArg Complex.im hz
  apply Complex.ext
  · simpa using hr
  · simp at hi ⊢
    linarith

private theorem re_eq_one_imp_eq_one {z : ℂ} (hz : z = star z) (hr : z.re = 1) :
    z = 1 := by
  have hi := congrArg Complex.im hz
  apply Complex.ext
  · simpa using hr
  · simp at hi ⊢
    linarith

/-- Real symmetry, a positive derivative at the simple zero and the absence
of other real zeros imply the sign required at the marked basepoint. -/
theorem source_negative_at_basepoint {f : ℂ → ℂ} {d : ℝ}
    (hcont : ContinuousOn f (Metric.ball 0 1)) (hzero : f 0 = 0)
    (hder : HasDerivAt f (d : ℂ) 0) (hd : 0 < d)
    (hreal : ∀ x ∈ Ioo (-1 : ℝ) 0, f (x : ℂ) = star (f (x : ℂ)))
    (hne : ∀ x ∈ Ioo (-1 : ℝ) 0, f (x : ℂ) ≠ 0) :
    (f (-1/2)).re < 0 := by
  let g : ℝ → ℝ := fun x ↦ (f (x : ℂ)).re
  have hg : HasDerivAt g d 0 := by
    simpa [g] using (show HasDerivAt f (d : ℂ) ((0 : ℝ) : ℂ) from hder).real_of_complex
  have hg₀ : g 0 = 0 := by simp [g,hzero]
  have hsg : ∀ᶠ x in 𝓝[≠] (0:ℝ), 0 < (g x - g 0) / x := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hg).eventually (lt_mem_nhds hd)
    simpa [slope_def_field] using h
  have hsg' : ∀ᶠ x in 𝓝[<] (0:ℝ), 0 < g x / x := by
    have hs : Iio (0 : ℝ) ⊆ {0}ᶜ := fun x hx ↦ ne_of_lt hx
    simpa [hg₀] using hsg.filter_mono (nhdsWithin_mono 0 hs)
  have hh : ∀ᶠ x in 𝓝[<] (0:ℝ), (-1/2 : ℝ) < x :=
    (lt_mem_nhds (by norm_num : (-1/2 : ℝ) < 0)).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hxratio, hxB, hx0⟩ :=
    (hsg'.and (hh.and self_mem_nhdsWithin)).exists
  have hxneg : g x < 0 := by
    have he := (div_pos_iff.mp hxratio)
    rcases he with he | he
    · exact False.elim ((not_lt_of_ge he.2.le) hx0)
    · exact he.1
  by_contra! hb
  have hc : ContinuousOn g (Icc (-1/2 : ℝ) x) := by
    apply Complex.continuous_re.comp_continuousOn
    apply hcont.comp Complex.continuous_ofReal.continuousOn
    intro y hy
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hbase : 0 ≤ g (-1/2) := by simpa [g, Complex.ofReal_div] using hb
  obtain ⟨y,hy,hy0⟩ := intermediate_value_Icc' hxB.le hc ⟨hxneg.le,hbase⟩
  have hyI : y ∈ Ioo (-1:ℝ) 0 := ⟨by linarith [hy.1], hy.2.trans_lt hx0⟩
  exact hne y hyI (re_eq_zero_imp_eq_zero (hreal y hyI) hy0)

/-- Imaginary-axis points are in the interval between the punctures whenever
lambda respects real reflection. The fixed point i supplies the sign. -/
theorem lambda_imaginaryAxis_between
    (href : ∀ z : ℍ, (z : ℂ).re = 0 → lambdaRatio z = star (lambdaRatio z))
    (z : ℍ) (hz : z.re = 0) :
    0 < (lambdaRatio z).re ∧ (lambdaRatio z).re < 1 := by
  let u : ℝ → ℍ := fun y ↦ ofComplex (⟨0,y⟩ : ℂ)
  let g : ℝ → ℝ := fun y ↦ (lambdaRatio (u y)).re
  have hu {y : ℝ} (hy : 0 < y) : u y = ⟨⟨0,y⟩,hy⟩ := by simp [u,ofComplex_apply_of_im_pos,hy]
  have hGu : ContinuousOn g (Ioi (0 : ℝ)) := by
    have hu' : ContinuousOn u (Ioi (0 : ℝ)) := by
      convert UpperHalfPlane.continuousOn_ofComplex_I_mul using 2 with y
      apply congrArg UpperHalfPlane.ofComplex
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    exact Complex.continuous_re.comp_continuousOn
      (lambdaRatio_mdifferentiable.continuous.comp_continuousOn hu')
  have hg1 : g 1 = (1/2:ℝ) := by
    have hS : ModularGroup.S • (UpperHalfPlane.I) = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext
      rw [ModularGroup.coe_S_smul]
      simp [UpperHalfPlane.coe_I, Complex.div_I]
    have h := lambdaRatio_S UpperHalfPlane.I
    rw [hS] at h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re] at h'
    have hu1 : u 1 = UpperHalfPlane.I := by
      rw [hu zero_lt_one]
      rfl
    dsimp [g]
    rw [hu1]
    linarith
  have havo (y : ℝ) (hy : 0 < y) : g y ≠ 0 ∧ g y ≠ 1 := by
    have hR : ((u y : ℍ) : ℂ).re = 0 := by rw [hu hy]
    exact ⟨fun he ↦ lambdaRatio_ne_zero _ (re_eq_zero_imp_eq_zero (href _ hR) he),
      fun he ↦ lambdaRatio_ne_one _ (re_eq_one_imp_eq_one (href _ hR) he)⟩
  have hU : u z.im = z := by
    rw [hu z.im_pos]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hz.symm
    · rfl
  have hgz : g z.im = (lambdaRatio z).re := by dsimp [g]; rw [hU]
  rw [← hgz]
  have hC : IsPreconnected (g '' Ioi (0:ℝ)) := (ordConnected_Ioi.isPreconnected).image g hGu
  have hord := hC.ordConnected
  have hm1 : (1/2:ℝ) ∈ g '' Ioi (0:ℝ) := ⟨1, by norm_num, hg1⟩
  have hmz : g z.im ∈ g '' Ioi (0:ℝ) := ⟨z.im,z.im_pos,rfl⟩
  constructor
  · by_contra! hn
    have h00 : (0:ℝ) ∈ g '' Ioi (0:ℝ) :=
      hord.out hmz hm1 ⟨hn, by norm_num⟩
    obtain ⟨x,hx,he⟩ := h00
    exact (havo x hx).1 he
  · by_contra! hn
    have h11 : (1:ℝ) ∈ g '' Ioi (0:ℝ) :=
      hord.out hm1 hmz ⟨by norm_num,hn⟩
    obtain ⟨x,hx,he⟩ := h11
    exact (havo x hx).2 he

/-- The even translates of the imaginary axis cannot give a negative
modular lambda value. -/
theorem reflection_index_odd_of_negative (z : ℍ) (n : ℤ)
    (hz : z.re = n) (hneg : (lambdaRatio z).re < 0) : Odd n := by
  have haxis (w : ℍ) (hw : (w : ℂ).re = 0) :
      lambdaRatio w = star (lambdaRatio w) := by
    have h : UpperHalfPlane.J • w = w := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_J_smul]
      apply Complex.ext
      · change -(w : ℂ).re = (w : ℂ).re
        rw [hw, neg_zero]
      · simp
    change lambdaRatio w = starRingEnd ℂ (lambdaRatio w)
    simpa only [h] using BelgianChocolate.ModularLambdaReflection.lambdaRatio_J w
  by_contra hn
  have he := Int.not_odd_iff_even.mp hn
  obtain ⟨k, hk⟩ := he
  let w : ℍ := ⟨⟨0,z.im⟩, z.im_pos⟩
  have hw : translate k • w = z := by
    apply UpperHalfPlane.ext
    rw [translate_coe_smul]
    apply Complex.ext
    · rw [Complex.add_re, Complex.intCast_re]
      change (0 : ℝ) + (↑(2 * k) : ℝ) = z.re
      rw [zero_add, hz]
      exact_mod_cast (show 2 * k = n by omega)
    · simp [w]
  have hl := lambdaRatio_gammaTwo (translate_mem_gammaTwo k) w
  rw [hw] at hl
  have hpos := (lambda_imaginaryAxis_between haxis w rfl).1
  rw [← hl] at hpos
  exact (not_lt_of_ge hpos.le) hneg


end BelgianChocolate.SecondAnnulus


