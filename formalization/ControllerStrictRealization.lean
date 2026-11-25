import ControllerAnalyticUnits
import ControllerDiskApproximation
import SourceDiskRealNormalization

namespace BelgianChocolate.ControlWitness

open Complex Filter Metric Set
open scoped ComplexConjugate NNReal Topology
open BelgianChocolate.SourceDiskPaths

/-- Exact preimages in the full disk, including all three marked points. -/
private theorem marked_preimages {s : ℝ} {f : ℂ → ℂ} (hf : MarkedCompetitor s f)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (f z = 0 → z = 0) ∧ (f z = 1 → z = (s : ℂ)*I ∨ z = -((s : ℂ)*I)) := by
  by_cases h0 : z = 0
  · subst z
    simp [hf.zero_value]
  by_cases hp : z = (s : ℂ)*I
  · subst z
    simp [hf.plus_value]
  by_cases hm : z = -((s : ℂ)*I)
  · subst z
    simp [← neg_mul, hf.minus_value]
  have h := hf.avoids (show z ∈ sourceDisk s from
    ⟨mem_ball_zero_iff.mp hz, h0, hp, by simpa only [neg_mul] using hm⟩)
  have hn : f z ≠ 0 ∧ f z ≠ 1 := by simpa using h
  exact ⟨fun e => (hn.1 e).elim, fun e => (hn.2 e).elim⟩

/-- The identities away from the three marks determine the conjugate of the
auxiliary unit. Continuity on the punctured neighborhood supplies each
removable value. -/
private theorem marked_unit_symmetric {s : ℝ} {f g a : ℂ → ℂ}
    (hf : MarkedCompetitor s f) (hreal : RealSymmetricOnDisk f)
    (ha : ∀ z ∈ ball (0 : ℂ) 1, ContinuousAt a z)
    (hG : ∀ z ∈ ball (0 : ℂ) 1, g z*(1-f z) = 1+z^2/(s : ℂ)^2)
    (hA : ∀ z ∈ ball (0 : ℂ) 1, g z-(1+z^2/(s : ℂ)^2) = z*a z) :
    RealSymmetricOnDisk a := by
  intro z hz
  have hball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : conj w ∈ ball (0 : ℂ) 1 := by
    simpa using hw
  have h₁ : ContinuousAt (fun w => a (conj w)) z :=
    (ha _ (hball hz)).comp Complex.continuous_conj.continuousAt
  have h₂ : ContinuousAt (fun w => conj (a w)) z :=
    Complex.continuous_conj.continuousAt.comp (ha z hz)
  apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z)
    (h₁.tendsto.mono_left nhdsWithin_le_nhds) (h₂.tendsto.mono_left nhdsWithin_le_nhds)
  have hev (v : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ≠ v :=
    (eventually_cofinite_ne v).filter_mono (nhdsNE_le_cofinite z)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz),
    hev 0, hev ((s : ℂ)*I), hev (-((s : ℂ)*I))] with w hw hw0 hwp hwm
  have hfo : f w ≠ 1 := fun e =>
    ((marked_preimages hf hw).2 e).elim hwp hwm
  have hne : 1 - conj (f w) ≠ 0 := by
    simpa only [map_sub, map_one] using
      ((map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hfo.symm))
  have hg₁ := hG (conj w) (hball hw)
  rw [hreal w hw] at hg₁
  have hg₂ := congrArg (fun x : ℂ => conj x) (hG w hw)
  simp only [map_mul, map_sub, map_one, map_add, map_div₀, map_pow, conj_ofReal] at hg₂
  have hg : g (conj w) = conj (g w) := mul_right_cancel₀ hne (hg₁.trans hg₂.symm)
  have ha₁ := hA (conj w) (hball hw)
  have ha₂ := congrArg (fun x : ℂ => conj x) (hA w hw)
  simp only [map_mul, map_sub, map_one, map_add, map_div₀, map_pow, conj_ofReal] at ha₂
  rw [hg] at ha₁
  exact mul_left_cancel₀ (by simpa using hw0 : conj w ≠ 0) (ha₁.symm.trans ha₂)

/-- The two analytic nonvanishing units associated to a real marked solution
on its original open disk. -/
theorem real_units_of_marked {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    {f : ℂ → ℂ} (hf : MarkedCompetitor s f) (hreal : RealSymmetricOnDisk f) :
    ∃ g a : ℂ → ℂ, RealSymmetricOnDisk a ∧ ∀ z ∈ ball (0 : ℂ) 1,
      AnalyticAt ℂ g z ∧ AnalyticAt ℂ a z ∧ g z ≠ 0 ∧ a z ≠ 0 ∧
      g z*(1-f z) = 1+z^2/(s : ℂ)^2 ∧ g z-(1+z^2/(s : ℂ)^2) = z*a z := by
  let u : ℂ := (s : ℂ)*I
  have hu : u ≠ 0 := mul_ne_zero (by exact_mod_cast hs.ne') I_ne_zero
  have hum : -u ∈ ball (0 : ℂ) 1 := by
    simpa [u, Complex.norm_real, abs_of_pos hs] using hs'
  have hd {v : ℂ} (hv : ∃ d, HasDerivAt f d v ∧ d ≠ 0) : deriv f v ≠ 0 := by
    obtain ⟨d, h, hn⟩ := hv
    rwa [h.deriv]
  obtain ⟨g, a, h⟩ := marked_analytic_units hu hum
    (hf.holomorphic.analyticOnNhd isOpen_ball) hf.zero_value hf.plus_value
    (by simpa [u, neg_mul] using hf.minus_value)
    (hd hf.zero_simple) (hd hf.plus_simple) (hd (by simpa [u, neg_mul] using hf.minus_simple))
    (fun _ hz => (marked_preimages hf hz).1) (fun _ hz => (marked_preimages hf hz).2)
  have hP (z : ℂ) : 1-z^2/u^2 = 1+z^2/(s : ℂ)^2 := by
    simp [u, mul_pow, div_neg, sub_neg_eq_add]
  simp_rw [hP] at h
  exact ⟨g, a, marked_unit_symmetric hf hreal
    (fun z hz => (h z hz).2.1.continuousAt) (fun z hz => (h z hz).2.2.2.2.1)
    (fun z hz => (h z hz).2.2.2.2.2), h⟩

/-- Dilate the analytic units to a disk strictly larger than the closed unit
disk, then realize a real polynomial controller. -/
theorem feasible_of_marked_scale {δ s t : ℝ} (hδ : δ < 1) (hs : 0 < s)
    (hst : s < t) (ht : t < 1) (hrel : t^2*(1+δ) = 1-δ)
    {f : ℂ → ℂ} (hf : MarkedCompetitor s f) (hreal : RealSymmetricOnDisk f) :
    Feasible δ := by
  obtain ⟨g, a, hasym, h⟩ := real_units_of_marked hs (hst.trans ht) hf hreal
  let c := s/t
  have ht0 := hs.trans hst
  have hc : 0 < c := div_pos hs ht0
  have hc1 : c < 1 := (div_lt_one ht0).mpr hst
  obtain ⟨r, hr, hr'⟩ := exists_between ((one_lt_div hc).mpr hc1)
  let R : ℝ≥0 := ⟨r, by linarith⟩
  have hR : 1 < R := by exact_mod_cast hr
  have hlarge {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (R : ℝ)) :
      (c : ℂ)*z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have hzr : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
    have hrc : r*c < 1 := (lt_div_iff₀ hc).mp hr'
    linarith [mul_le_mul_of_nonneg_left hzr hc.le]
  have hsmall {z : ℂ} (hz : ‖z‖ ≤ 1) : (c : ℂ)*z ∈ ball (0 : ℂ) 1 :=
    hlarge (mem_closedBall_zero_iff.mpr (hz.trans hr.le))
  have hcn : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  apply feasible_of_analytic_disk_unit (a := fun z : ℂ => (c : ℂ)*a ((c : ℂ)*z)) hδ hR
  · intro z hz
    have hlin : DifferentiableAt ℂ (fun w : ℂ => (c : ℂ)*w) z := by fun_prop
    have hcomp := (h _ (hlarge hz)).2.1.differentiableAt.comp z hlin
    exact (hcomp.const_mul (c : ℂ)).differentiableWithinAt
  · intro z hz
    simp only [map_mul, conj_ofReal]
    simpa only [map_mul, conj_ofReal] using
      congrArg (fun w : ℂ => (c : ℂ)*w) (hasym _ (hsmall hz))
  · intro z hz
    exact mul_ne_zero hcn (h _ (hsmall hz)).2.2.2.1
  · intro z hz
    have e := (h _ (hsmall hz)).2.2.2.2.2
    have hgn := (h _ (hsmall hz)).2.2.1
    have hsn : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have htn : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hδn : 1-(δ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : 1-δ ≠ 0)
    have hrc : (t : ℂ)^2*(1+(δ : ℂ)) = 1-(δ : ℂ) := by exact_mod_cast hrel
    have hp : ((c : ℂ)*z)^2/(s : ℂ)^2 = z^2*(1+(δ : ℂ))/(1-(δ : ℂ)) := by
      dsimp [c]
      push_cast
      field_simp [hsn, htn, hδn]
      linear_combination -z^2*hrc
    rw [hp] at e
    convert hgn using 1
    linear_combination -e

/-- A real-symmetric marked disk solution strictly below the natural disk
parameter yields a finite real strictly stabilizing controller. -/
theorem feasible_of_strict_marked {δ tₛ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) (hs : 0 < tₛ)
    (hst : tₛ < Real.sqrt ((1-δ)/(1+δ))) {f : ℂ → ℂ}
    (hf : MarkedCompetitor tₛ f) (hreal : RealSymmetricOnDisk f) : Feasible δ := by
  let t := Real.sqrt ((1-δ)/(1+δ))
  have hden : 0 < 1+δ := by linarith
  have hr : 0 < (1-δ)/(1+δ) := div_pos (by linarith) hden
  have ht : t^2 = (1-δ)/(1+δ) := Real.sq_sqrt hr.le
  have hr1 : (1-δ)/(1+δ) < 1 := (div_lt_one hden).mpr (by linarith)
  apply feasible_of_marked_scale hδ' hs hst (show t < 1 by nlinarith) _ hf hreal
  change t^2*(1+δ) = 1-δ
  rw [ht, div_mul_cancel₀ _ hden.ne']

end BelgianChocolate.ControlWitness
