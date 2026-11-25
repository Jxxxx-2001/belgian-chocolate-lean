import SourceDiskRealNormalization
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-! The angular multiplicity argument at the real source cusp. -/

namespace BelgianChocolate.SourceDiskPaths

open Complex Filter Metric Set
open scoped ComplexConjugate Topology

set_option maxHeartbeats 800000

private theorem real_mul_im (x : ℝ) (w : ℂ) : ((x : ℂ)*w).im = x*w.im := by
  simp [Complex.mul_im]

private theorem ray_limit (w : ℂ) :
    Tendsto (fun x : ℝ => (x : ℂ)*w) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  have h : Continuous (fun x : ℝ => (x : ℂ)*w) := by fun_prop
  simpa only [ofReal_zero, zero_mul] using
    (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

private theorem leading_real {f g : ℂ → ℂ} {n : ℕ} (hg : ContinuousAt g 0)
    (hreal : ∀ᶠ z in 𝓝 (0 : ℂ), f (conj z) = conj (f z))
    (hfg : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z^n*g z) : (g 0).im = 0 := by
  have hr : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using ray_limit 1
  have hlim := (continuous_im.continuousAt.comp hg).tendsto.comp hr
  apply tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds
  filter_upwards [hr.eventually hfg, hr.eventually hreal,
    self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with x hx hconj hpos
  have he := congrArg Complex.im hconj
  simp only [conj_ofReal, conj_im, hx, ← ofReal_pow, real_mul_im] at he
  change (g (x : ℂ)).im = 0
  have hxp : 0 < x^n := pow_pos hpos n
  exact (mul_eq_zero.mp (show x^n*(g (x : ℂ)).im = 0 by linarith)).resolve_left hxp.ne'

private theorem leading_upper {f g : ℂ → ℂ} {n : ℕ} (hg : ContinuousAt g 0)
    (hfg : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z^n*g z)
    (hsign : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < z.im → 0 < (f z).im)
    {w : ℂ} (hw : 0 < w.im) : 0 ≤ (w^n*g 0).im := by
  have hlim := (continuous_im.continuousAt.comp
    (hg.const_mul (w^n))).tendsto.comp (ray_limit w)
  apply ge_of_tendsto hlim
  filter_upwards [(ray_limit w).eventually hfg, (ray_limit w).eventually hsign,
    self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with x hx hsign hxpos
  have hp : 0 < ((x : ℂ)*w).im := by rw [real_mul_im]; exact mul_pos hxpos hw
  have h := hsign hp
  rw [hx, mul_pow, ← ofReal_pow, mul_assoc, real_mul_im] at h
  exact (pos_of_mul_pos_right h (pow_pos hxpos n).le).le

private theorem leading_sin {f g : ℂ → ℂ} {n : ℕ} (hn : 0 < n) (hg : ContinuousAt g 0)
    (hfg : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z^n*g z)
    (hsign : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < z.im → 0 < (f z).im)
    (hreal : (g 0).im = 0) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < n*Real.pi) :
    0 ≤ Real.sin θ*(g 0).re := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let w := Complex.exp (((θ / n : ℝ) : ℂ)*I)
  have hw : 0 < w.im := by
    simp only [w, exp_im, mul_I_re, ofReal_im, neg_zero, Real.exp_zero, mul_I_im,
      ofReal_re, one_mul]
    exact Real.sin_pos_of_pos_of_lt_pi (div_pos hθ hn') ((div_lt_iff₀ hn').mpr (by linarith))
  have hpow : w^n = Complex.exp ((θ : ℂ)*I) := by
    change (Complex.exp (((θ / n : ℝ) : ℂ)*I))^n = _
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hn.ne']
  have hh := leading_upper (w := w) (n := n) hg hfg hsign hw
  rw [hpow, mul_im, hreal, mul_zero, zero_add] at hh
  simpa only [exp_im, mul_I_re, ofReal_im, neg_zero, Real.exp_zero, mul_I_im, ofReal_re,
    one_mul] using hh

/-- A holomorphic real-symmetric germ vanishing at the origin has a strictly
positive real derivative if its imaginary part is positive throughout the
nearby open upper half-plane. -/
theorem positive_derivative_of_upper_sign_germ {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0)
    (hreal : ∀ᶠ z in 𝓝 (0 : ℂ), f (conj z) = conj (f z))
    (hsign : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < z.im → 0 < (f z).im) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt f (d : ℂ) 0 := by
  have hnon : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 := by
    intro hz
    obtain ⟨x, hx, hh, hp⟩ := (((ray_limit I).eventually hz).and
      (((ray_limit I).eventually hsign).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ))))).exists
    have h := hh (by simpa using hp)
    simp [hx] at h
  obtain ⟨n, g, hg, hgn, heq⟩ := hf.exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hnon
  have hfg : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z^n*g z := by simpa using heq
  have hn : 0 < n := by
    by_contra! he
    have en : n = 0 := by omega
    have he₀ := mem_of_mem_nhds hfg
    change f 0 = _ at he₀
    simp [en, h0, hgn.symm] at he₀
  have hi := leading_real hg.continuousAt hreal hfg
  have hh {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < n*Real.pi) :=
    leading_sin hn hg.continuousAt hfg hsign hi hθ hθ'
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hπ := Real.pi_pos
  have hpos : 0 ≤ (g 0).re := by
    simpa using hh (θ := Real.pi/2) (by linarith) (by nlinarith)
  have hp : 0 < (g 0).re := by
    refine lt_of_le_of_ne hpos ?_
    intro e
    exact hgn (Complex.ext (by simpa using e.symm) (by simpa using hi))
  have hn₁ : n = 1 := by
    by_contra h
    have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hsin := hh (θ := Real.pi+Real.pi/2) (by linarith) (by nlinarith)
    simp only [Real.sin_add, Real.sin_pi, zero_mul, Real.cos_pi, Real.sin_pi_div_two,
      mul_one, zero_add, neg_one_mul] at hsin
    linarith
  have hder : HasDerivAt (fun z : ℂ => z*g z) (g 0) 0 := by
    simpa [Pi.mul_def] using (hasDerivAt_id (0 : ℂ)).mul hg.differentiableAt.hasDerivAt
  have he : f =ᶠ[𝓝 (0 : ℂ)] (fun z => z*g z) := by
    filter_upwards [hfg] with z hz using (by simpa [hn₁] using hz)
  have hr : ((g 0).re : ℂ) = g 0 := Complex.ext (by simp) (by simp [hi])
  exact ⟨_, hp, hr.symm ▸ hder.congr_of_eventuallyEq he⟩

theorem positive_derivative_of_upper_sign {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) (hreal : RealSymmetricOnDisk f)
    (hsign : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < z.im → 0 < (f z).im) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt f (d : ℂ) 0 := by
  apply positive_derivative_of_upper_sign_germ hf h0 _ hsign
  filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz using hreal z hz

end BelgianChocolate.SourceDiskPaths
