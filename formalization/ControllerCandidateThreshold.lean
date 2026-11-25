import ControllerStrictRealization
import ControllerBoundaryRegular
import MarkedBoundaryObstruction

/-! The original finite-control feasibility threshold from the concrete candidate data. -/

namespace BelgianChocolate.ControlWitness

open Complex Metric Set
open BelgianChocolate.SourceDiskPaths BelgianChocolate.HarmonicComparison
open BelgianChocolate.MarkedAxisSlit BelgianChocolate.ModularLambdaRatio

/-- The original Cayley parameter expressed in the normalized disk parameter. -/
noncomputable def controllerParameter (t : ℝ) : ℝ := (1 - t^2) / (1 + t^2)

theorem controllerParameter_mem_Ioo {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    controllerParameter t ∈ Ioo 0 1 := by
  have hd : 0 < 1 + t^2 := by positivity
  refine ⟨div_pos (by nlinarith [sq_nonneg (1-t)]) hd, (div_lt_one hd).mpr ?_⟩
  nlinarith

theorem controllerParameter_sq_relation (t : ℝ) :
    t^2 * (1 + controllerParameter t) = 1 - controllerParameter t := by
  unfold controllerParameter
  field_simp
  ring

theorem controllerParameter_lt_iff {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    δ < controllerParameter t ↔ t < Real.sqrt ((1-δ)/(1+δ)) := by
  have hd : 0 < 1 + δ := by linarith
  have htden : 0 < 1 + t^2 := by positivity
  have hr : 0 ≤ (1-δ)/(1+δ) := div_nonneg (by linarith) hd.le
  have h := Real.sq_sqrt hr
  rw [controllerParameter, lt_div_iff₀ htden]
  constructor
  · intro hh
    have hsq : t^2 < (1-δ)/(1+δ) := (lt_div_iff₀ hd).mpr (by nlinarith only [hh])
    by_contra! hn
    have hnon := mul_nonneg (sub_nonneg.mpr hn) (add_nonneg ht (Real.sqrt_nonneg ((1-δ)/(1+δ))))
    nlinarith only [h,hsq,hnon]
  · intro hh
    have hpos := mul_pos (sub_pos.mpr hh) (add_pos_of_nonneg_of_pos ht
      (ht.trans_lt hh))
    have hsq : t^2 < (1-δ)/(1+δ) := by nlinarith only [h,hpos]
    have hh' := (lt_div_iff₀ hd).mp hsq
    nlinarith only [hh']

/-- Every actual finite controller at the marked candidate's parameter would
lift to its cusp boundary contact, contradicting the regular value at i. -/
theorem controller_endpoint_excluded_of_candidate {ts : ℝ}
    (hts : 0 < ts) (hts₁ : ts < 1) (hsmall : ts ≤ 1/10)
    {Φ : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ) :
    ¬ Feasible (controllerParameter ts) := by
  intro hctrl
  obtain ⟨x,y,hx,hy,_,hq⟩ := hctrl
  let δ := controllerParameter ts
  let f := diskController δ x y
  have hδ : 0 < δ := (controllerParameter_mem_Ioo hts hts₁).1
  have hq' : StrictlyStable (closedLoop δ x y) := hq
  have hf : MarkedCompetitor ts f :=
    controller_to_marked hδ hts hts₁ (controllerParameter_sq_relation ts) hx hy hq'
  have hreal : RealSymmetricOnDisk f := fun z _ ↦ diskController_conj δ x y z
  obtain ⟨g, d, hg, hgm, hgr, hgd, him, hpos⟩ := exists_positive_source_derivative hf hreal
  have hgn : ContinuousAt g I ∧ g I ∈ ({0,1}ᶜ : Set ℂ) := by
    rcases hg with h|h
    · rw [h]
      exact diskController_regular_at_I hδ hx hy hq'
    · rw [h]
      exact diskController_neg_regular_at_I hδ hx hy hq'
  have hdc : (d.re : ℂ) = d := Complex.ext rfl (by simpa using him.symm)
  obtain ⟨φ, hd, hn, hU, hz, _, hneg, hpos₁⟩ :=
    exists_marked_competitor_lift hts hsmall hgm hgr (hdc.symm ▸ hgd) hpos
  obtain ⟨η, hη⟩ := exists_centered_comparisonChart hts hts₁
  have heq := (eq_parameter_and_lift_of_marked_competitor hts hts le_rfl
    hη hΦ hd hn hz hneg hpos₁).2
  exact regular_at_I_incompatible_with_candidate hts hts₁ hgm hd hn hU hΦ heq hgn.1 hgn.2

/-- Given the balanced candidate and its verified disk data, the feasible
finite real controller parameters are exactly the claimed open interval. -/
theorem controller_feasible_iff_of_candidate {ts δ : ℝ}
    (hts : 0 < ts) (hts₁ : ts < 1) (hδ : 0 < δ) (hδ₁ : δ < 1)
    {Φ fs : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ)
    (hfs : MarkedCompetitor ts fs) (hreal : RealSymmetricOnDisk fs)
    (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z) = fs z) :
    Feasible δ ↔ δ < controllerParameter ts := by
  obtain ⟨_, hsmall, hdisk, _⟩ := disk_threshold_of_certified_witness hts hts₁ hΦ hfs hreal hrep
  constructor
  · intro h
    obtain ⟨ht, ht₁, f, hf, hfr⟩ := feasible_to_disk hδ hδ₁ h
    let t := Real.sqrt ((1-δ)/(1+δ))
    have ht_mem : t ∈ Ico ts 1 := by
      rw [← hdisk]
      exact ⟨ht, ht₁, f, hf, fun z _ ↦ hfr z⟩
    by_contra! hlarge
    have hntl : ¬ ts < t := fun hl ↦ (not_lt_of_ge hlarge)
      ((controllerParameter_lt_iff hts.le hδ hδ₁).mpr hl)
    have he : t = ts := le_antisymm (le_of_not_gt hntl) ht_mem.1
    have hd : 0 < 1+δ := by linarith
    have hr : 0 ≤ (1-δ)/(1+δ) := div_nonneg (by linarith) hd.le
    have hs : ts^2 * (1+δ) = 1-δ := by
      have hh : ts^2 = (1-δ)/(1+δ) := he ▸ Real.sq_sqrt hr
      rw [hh, div_mul_cancel₀ _ hd.ne']
    have hout : δ = controllerParameter ts := by
      have hp := controllerParameter_sq_relation ts
      have hc : 0 < 1+ts^2 := by positivity
      apply (mul_right_inj' (ne_of_gt hc)).mp
      nlinarith only [hp, hs]
    exact controller_endpoint_excluded_of_candidate hts hts₁ hsmall.le hΦ (hout ▸ h)
  · intro h
    exact feasible_of_strict_marked hδ hδ₁ hts
      ((controllerParameter_lt_iff hts.le hδ hδ₁).mp h) hfs hreal

/-- The admissible finite-control threshold and its supremum, with the
balanced candidate as input. -/
theorem controller_threshold_of_candidate {ts : ℝ}
    (hts : 0 < ts) (hts₁ : ts < 1) {Φ fs : ℂ → ℂ}
    (hΦ : ComparisonCandidate ts Φ) (hfs : MarkedCompetitor ts fs)
    (hreal : RealSymmetricOnDisk fs) (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z) = fs z) :
    {δ : ℝ | 0 < δ ∧ δ < 1 ∧ Feasible δ} = Ioo 0 (controllerParameter ts) ∧
      sSup {δ : ℝ | 0 < δ ∧ δ < 1 ∧ Feasible δ} = controllerParameter ts := by
  have hg : controllerParameter ts ∈ Ioo 0 1 := controllerParameter_mem_Ioo hts hts₁
  have hs : {δ : ℝ | 0 < δ ∧ δ < 1 ∧ Feasible δ} = Ioo 0 (controllerParameter ts) := by
    ext δ
    constructor
    · rintro ⟨hδ,hδ₁,hctrl⟩
      exact ⟨hδ,(controller_feasible_iff_of_candidate hts hts₁ hδ hδ₁ hΦ hfs hreal hrep).mp hctrl⟩
    · intro hd
      have hδ₁ := hd.2.trans hg.2
      exact ⟨hd.1,hδ₁,(controller_feasible_iff_of_candidate hts hts₁ hd.1 hδ₁ hΦ hfs hreal hrep).mpr hd.2⟩
  refine ⟨hs,?_⟩
  rw [hs, csSup_Ioo hg.1]

end BelgianChocolate.ControlWitness