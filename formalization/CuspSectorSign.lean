import ModularLambdaCuspCover
import ModularLambdaReflection
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Analytic.CPolynomialDef

namespace BelgianChocolate.CuspSectorSign
open Complex Filter Metric Set Topology
open scoped ComplexConjugate

/-- Reflection turns the strict derivative estimate into an angularly uniform
estimate: the error is measured against `im z`, even near the real axis. -/
theorem eventually_im_error_le {f : ℂ → ℂ} {d ε : ℝ}
    (hd : HasStrictDerivAt f (d : ℂ) 0)
    (hreal : ∀ᶠ z in 𝓝 (0 : ℂ), f (conj z) = conj (f z)) (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 (0 : ℂ), |(f z).im - d * z.im| ≤ ε * |z.im| := by
  have hb := (hasDerivAtFilter_iff_isLittleO.mp hd).def hε
  have ht : Tendsto (fun z : ℂ => (z, conj z)) (𝓝 0) (𝓝 (0,0)) := by
    simpa using (continuous_id.prodMk continuous_conj).continuousAt.tendsto (x := (0 : ℂ))
  filter_upwards [ht.eventually hb, hreal] with z hz hr
  simp only [smul_eq_mul] at hz
  rw [hr] at hz
  have he : f z - conj (f z) - (z - conj z) * (d : ℂ) =
      ((2 * ((f z).im - d * z.im) : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp; ring
  have he' : z - conj z = ((2 * z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp; ring
  rw [he, he'] at hz
  simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hz
  linarith

theorem eventually_im_pos {f : ℂ → ℂ} {d : ℝ}
    (hd : HasStrictDerivAt f (d : ℂ) 0)
    (hreal : ∀ᶠ z in 𝓝 (0 : ℂ), f (conj z) = conj (f z)) (hdpos : 0 < d) :
    ∀ᶠ z in 𝓝 (0 : ℂ), 0 < z.im → 0 < (f z).im := by
  filter_upwards [eventually_im_error_le hd hreal (half_pos hdpos)] with z hz him
  rw [abs_of_pos him] at hz
  have h := (abs_le.mp hz).1
  nlinarith

open BelgianChocolate.ModularLambdaRatio

/-- The actual modular cusp function commutes with conjugation on its disk. -/
theorem cuspLambda_conj {q : ℂ} (hq : ‖q‖ < 1) :
    cuspLambda (conj q) = conj (cuspLambda q) := by
  by_cases hq0 : q = 0
  · simp [hq0, cuspLambda_zero]
  obtain ⟨τ, hτ⟩ := cuspNomeDisc_surjective ⟨q, hq, hq0⟩
  have he : (cuspNomeDisc τ : ℂ) = q := congrArg Subtype.val hτ
  have he' : (cuspNomeDisc (UpperHalfPlane.J • τ) : ℂ) = conj q := by
    rw [cuspNomeDisc_coe, ← he, cuspNomeDisc_coe,
      UpperHalfPlane.coe_J_smul, ← Complex.exp_conj]
    congr 1
    simp
  rw [← he', cuspLambda_nome, ← he, cuspLambda_nome]
  exact BelgianChocolate.ModularLambdaReflection.lambdaRatio_J τ

/-- Uniform angular estimate at the concrete modular cusp. -/
theorem cuspLambda_hasStrictDerivAt_zero : HasStrictDerivAt cuspLambda (16 : ℂ) 0 := by
  have ha : AnalyticAt ℂ cuspLambda 0 := by
    apply DifferentiableOn.analyticAt (s := ball (0 : ℂ) 1)
    · intro z hz
      exact (cuspLambda_differentiableAt (mem_ball_zero_iff.mp hz)).differentiableWithinAt
    · exact ball_mem_nhds 0 (by norm_num)
  exact ha.contDiffAt.hasStrictDerivAt cuspLambda_hasDerivAt_zero
    (show (⊤ : WithTop ℕ∞) ≠ 0 by simp)

theorem cuspLambda_im_error {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝 (0 : ℂ), |(cuspLambda q).im - 16 * q.im| ≤ ε * |q.im| := by
  apply eventually_im_error_le cuspLambda_hasStrictDerivAt_zero _ hε
  filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with q hq
  exact cuspLambda_conj (mem_ball_zero_iff.mp hq)

theorem cuspLambda_im_pos_near_zero :
    ∀ᶠ q in 𝓝 (0 : ℂ), 0 < q.im → 0 < (cuspLambda q).im := by
  filter_upwards [cuspLambda_im_error (by norm_num : (0 : ℝ) < 8)] with q hq him
  rw [abs_of_pos him] at hq
  have h := (abs_le.mp hq).1
  linarith

/-- The sector used by the candidate cusp is the entire high part of the
vertical strip `0 < re τ < 1`, with one height working for all directions. -/
theorem lambdaRatio_im_pos_at_cusp :
    ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
      0 < τ.re → τ.re < 1 → 0 < (lambdaRatio τ).im := by
  have hq : Tendsto (fun τ : UpperHalfPlane => (cuspNomeDisc τ : ℂ))
      UpperHalfPlane.atImInfty (𝓝 0) := by
    exact UpperHalfPlane.qParam_tendsto_atImInfty (h := 2) (by norm_num)
  filter_upwards [hq.eventually cuspLambda_im_pos_near_zero] with τ hτ h0 h1
  rw [← cuspLambda_nome τ]
  apply hτ
  rw [cuspNomeDisc_coe, Complex.exp_im]
  apply mul_pos (Real.exp_pos _)
  have he : ((Real.pi : ℂ) * I * (τ : ℂ)).im = Real.pi * τ.re := by
    simp
  rw [he]
  exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0)
    (by nlinarith [Real.pi_pos])

/-- Composition with a cusp coordinate gives both the removable zero limit
and positivity above the source axis. -/
theorem cuspLambda_comp_cusp {q : ℂ → ℂ}
    (hq : Tendsto q (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝 0))
    (hqpos : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] 0, 0 < (q z).im) :
    Tendsto (fun z => cuspLambda (q z)) (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝 0) ∧
      ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] 0, 0 < (cuspLambda (q z)).im := by
  constructor
  · simpa only [cuspLambda_zero, Function.comp_def] using
      cuspLambda_hasDerivAt_zero.continuousAt.tendsto.comp hq
  · filter_upwards [hq.eventually cuspLambda_im_pos_near_zero, hqpos] with z hz hp
    exact hz hp

end BelgianChocolate.CuspSectorSign
