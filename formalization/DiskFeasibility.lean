import SourceDiskRealNormalization
import UpperHalfDiskPuncture
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Scaling the disk competitors and extending equality from the upper half-disk. -/

namespace BelgianChocolate.SourceDiskPaths

open Complex Metric Set Filter Topology
open BelgianChocolate.UpperHalfDisk

private theorem radialMapsTo {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    MapsTo (fun z : ℂ ↦ (r : ℂ) * z) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hn := mem_ball_zero_iff.mp hz
  nlinarith [mul_nonneg (sub_nonneg.mpr hr₁) (norm_nonneg z)]

/-- A feasible marked disk function gives a feasible function at each larger
parameter, preserving the original reflection and the simple multiplicities. -/
theorem disk_feasible_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {f : ℂ → ℂ} (hf : MarkedCompetitor a f) (hreal : RealSymmetricOnDisk f) :
    ∃ g : ℂ → ℂ, MarkedCompetitor b g ∧ RealSymmetricOnDisk g := by
  have hb := ha.trans_le hab
  let r := a / b
  have hr : 0 < r := div_pos ha hb
  have hr₁ : r ≤ 1 := (div_le_one hb).mpr hab
  have h₀ : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hmul' : r * b = a := div_mul_cancel₀ _ hb.ne'
  have hmul : (r : ℂ) * (b : ℂ) = (a : ℂ) := by exact_mod_cast hmul'
  have hp : (r : ℂ) * ((b : ℂ) * I) = (a : ℂ) * I := by rw [← mul_assoc, hmul]
  have hm : (r : ℂ) * (-(b : ℂ) * I) = -(a : ℂ) * I := by
    simp only [neg_mul, mul_neg, hp]
  have hD (z : ℂ) : HasDerivAt (fun w : ℂ ↦ (r : ℂ) * w) (r : ℂ) z := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul (r : ℂ)
  have hs (z : ℂ) (hex : ∃ d, HasDerivAt f d ((r : ℂ) * z) ∧ d ≠ 0) :
      ∃ d, HasDerivAt (fun w : ℂ ↦ f ((r : ℂ) * w)) d z ∧ d ≠ 0 := by
    obtain ⟨d, hd, hne⟩ := hex
    exact ⟨_, hd.comp z (hD z), mul_ne_zero hne h₀⟩
  refine ⟨fun z ↦ f ((r : ℂ) * z), ?_, ?_⟩
  · refine ⟨hf.holomorphic.comp (fun z _ ↦ (hD z).differentiableAt.differentiableWithinAt)
      (radialMapsTo hr hr₁), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      apply hf.avoids
      refine ⟨mem_ball_zero_iff.mp ((radialMapsTo hr hr₁) (mem_ball_zero_iff.mpr hz.1)),
        mul_ne_zero h₀ hz.2.1, ?_, ?_⟩
      · rw [← hp]
        exact fun h ↦ hz.2.2.1 (mul_left_cancel₀ h₀ h)
      · rw [← hm]
        exact fun h ↦ hz.2.2.2 (mul_left_cancel₀ h₀ h)
    · simpa using hf.zero_value
    · rw [hp]; exact hf.plus_value
    · rw [hm]; exact hf.minus_value
    · exact hs 0 (by simpa only [mul_zero] using hf.zero_simple)
    · exact hs _ (hp.symm ▸ hf.plus_simple)
    · exact hs _ (hm.symm ▸ hf.minus_simple)
  · intro z hz
    have h := hreal ((r : ℂ) * z) (radialMapsTo hr hr₁ hz)
    simpa only [map_mul, Complex.conj_ofReal] using h

/-- Equality of holomorphic competitors on the open upper half-disk determines
them everywhere on the original unit disk. -/
theorem disk_eqOn_of_upper_halfDisk {a b : ℝ} {f g : ℂ → ℂ}
    (hf : MarkedCompetitor a f) (hg : MarkedCompetitor b g)
    (heq : EqOn f g domain) : EqOn f g (ball 0 1) := by
  have hd : domain ⊆ ball (0 : ℂ) 1 := fun _ hz ↦ mem_ball_zero_iff.mpr hz.1
  have hz : (Complex.I / 2 : ℂ) ∈ domain := by
    constructor <;> norm_num [norm_div, Complex.div_im]
  exact (hf.holomorphic.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hg.holomorphic.analyticOnNhd isOpen_ball) (convex_ball (0 : ℂ) 1).isPreconnected
    (hd hz) (Filter.mem_of_superset (domain_isOpen.mem_nhds hz) heq)

end BelgianChocolate.SourceDiskPaths