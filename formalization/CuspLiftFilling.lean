import ModularLambdaCuspCover
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Tactic

/-! Holomorphicity and removable singularities of lifts to the cusp disk. -/

namespace BelgianChocolate.ModularLambdaRatio

open Complex Metric Set Filter Topology

/-- The covering on the punctured disk has no critical points. -/
theorem cuspU_deriv_ne_zero {w : ℂ} (hw : ‖w‖ < 1) (h₀ : w ≠ 0) :
    deriv cuspU w ≠ 0 := by
  let W : PuncturedUnitDisc := ⟨w, hw, h₀⟩
  have hout : IsOpen {z : ℂ | ‖z‖ < 1} :=
    isOpen_lt continuous_norm continuous_const
  have hin : IsOpen {z : ℂ | ‖z‖ < 1 ∧ z ≠ 0} :=
    hout.inter isClosed_singleton.isOpen_compl
  have ha := cuspU_differentiableOn.analyticOnNhd hout w hw
  obtain ⟨N, hN, hW, hU⟩ :=
    cuspUPunctured_isCoveringMap.isLocalHomeomorph.isLocallyInjective W
  apply (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero ha).mp
  refine ⟨Subtype.val '' N, hin.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr
    (hN.mem_nhds hW), ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
  exact congrArg Subtype.val (hU hx hy (Subtype.ext he))

/-- A continuous lift of a holomorphic map through U is holomorphic wherever
the lift remains in the punctured unit disk. -/
theorem cuspLift_differentiableOn {D : Set ℂ} (hD : IsOpen D) {f φ : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hφ : ContinuousOn φ D)
    (hmap : ∀ z ∈ D, ‖φ z‖ < 1 ∧ φ z ≠ 0)
    (hcomp : ∀ z ∈ D, cuspU (φ z) = f z) :
    DifferentiableOn ℂ φ D := by
  intro z hz
  have hnh := hD.mem_nhds hz
  have hU := (cuspU_differentiableOn.differentiableAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds (hmap z hz).1)).hasDerivAt
  have hfd := (hf.differentiableAt hnh).hasDerivAt
  exact (HasDerivAt.of_comp_left ((hφ z hz).continuousAt hnh) hU hfd
    (cuspU_deriv_ne_zero (hmap z hz).1 (hmap z hz).2)
    (Filter.mem_of_superset hnh hcomp)).differentiableAt.differentiableWithinAt

/-- A holomorphic cusp lift on a punctured open connected domain of a simple
preimage of one extends there, with a simple zero and derivative divided by
the derivative of U at the cusp. -/
theorem cuspLift_fill {f φ : ℂ → ℂ} {p d : ℂ} {D : Set ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (hp : p ∈ D) (hφ : DifferentiableOn ℂ φ (D \ {p}))
    (hmap : ∀ z ∈ D \ {p}, ‖φ z‖ < 1)
    (hcomp : ∀ z ∈ D \ {p}, cuspU (φ z) = f z)
    (hf₀ : f p = 1) (hder : HasDerivAt f d p) (hd : d ≠ 0) :
    ∃ Ψ : ℂ → ℂ, EqOn Ψ φ (D \ {p}) ∧
      DifferentiableOn ℂ Ψ (D) ∧
      (∀ z ∈ D, ‖Ψ z‖ < 1) ∧
      (∀ z ∈ D, cuspU (Ψ z) = f z) ∧
      Ψ p = 0 ∧ HasDerivAt Ψ (d / 16) p ∧ d / 16 ≠ 0 := by
  classical
  let Ψ : ℂ → ℂ := Function.update φ p (limUnder (𝓝[≠] p) φ)
  have hb : BddAbove (norm ∘ φ '' (D \ {p})) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hmap z hz).le
  have hcont : DifferentiableOn ℂ Ψ (D) :=
    differentiableOn_update_limUnder_of_bddAbove (hD.mem_nhds hp) hφ hb
  have hΨ : EqOn Ψ φ (D \ {p}) := by
    intro z hz
    exact Function.update_of_ne hz.2 ..
  have hlim : Tendsto Ψ (𝓝[≠] p) (𝓝 (Ψ p)) :=
    (hcont.differentiableAt (hD.mem_nhds hp)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hball : ∀ᶠ z in 𝓝 p, z ∈ D := hD.mem_nhds hp
  have hb' : ∀ᶠ z in 𝓝[≠] p, z ∈ D \ {p} :=
    (hball.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin
  have hn : ‖Ψ p‖ ≤ 1 :=
    le_of_tendsto hlim.norm (hb'.mono fun z hz ↦ (hΨ hz).symm ▸ (hmap z hz).le)
  have hn' : ‖Ψ p‖ < 1 := by
    by_contra! he
    have heq : ‖Ψ p‖ = 1 := le_antisymm hn he
    have hmax : IsMaxOn (norm ∘ Ψ) (D) p := by
      intro z hz
      change ‖Ψ z‖ ≤ ‖Ψ p‖
      by_cases hz' : z = p
      · rw [hz']
      · rw [heq, hΨ ⟨hz,hz'⟩]
        exact (hmap z ⟨hz,hz'⟩).le
    have hconst := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
      hconn hD hcont hp hmax
    obtain ⟨z, hz, hzp⟩ := hb'.exists
    have hv := hconst hz
    change ‖Ψ z‖ = ‖Ψ p‖ at hv
    rw [heq, hΨ ⟨hz,hzp⟩] at hv
    exact (hmap z ⟨hz,hzp⟩).ne hv
  have hUcont : ContinuousAt cuspU (Ψ p) :=
    (cuspU_differentiableOn.differentiableAt
      ((isOpen_lt continuous_norm continuous_const).mem_nhds hn')).continuousAt
  have hevent : (fun z ↦ cuspU (Ψ z)) =ᶠ[𝓝[≠] p] f :=
    hb'.mono fun z hz ↦ by
      change cuspU (Ψ z) = f z
      rw [hΨ hz, hcomp z hz]
  have hfirst := hUcont.tendsto.comp hlim
  have hsecond := hder.continuousAt.tendsto.mono_left
    (show 𝓝[≠] p ≤ 𝓝 p from nhdsWithin_le_nhds)
  have hUp : cuspU (Ψ p) = 1 := (tendsto_nhds_unique hfirst (hsecond.congr' hevent.symm)).trans hf₀
  have hzero := (cuspU_eq_one_iff hn').mp hUp
  have hcom : ∀ z ∈ D, cuspU (Ψ z) = f z := by
    intro z hz
    by_cases h : z = p
    · simpa [h,hf₀] using hUp
    · rw [hΨ ⟨hz,h⟩, hcomp z ⟨hz,h⟩]
  have hΨder : HasDerivAt Ψ (deriv Ψ p) p :=
    (hcont.differentiableAt (hD.mem_nhds hp)).hasDerivAt
  have hUD : HasDerivAt cuspU (16 : ℂ) (Ψ p) := hzero.symm ▸ cuspU_hasDerivAt_zero
  have hdcomp : HasDerivAt (cuspU ∘ Ψ) (16 * deriv Ψ p) p :=
    hUD.comp p hΨder
  have hzder : 16 * deriv Ψ p = d :=
    ((hdcomp.congr_of_eventuallyEq
      (hball.mono fun z hz ↦ (hcom z hz).symm))).unique hder
  have hder' : deriv Ψ p = d / 16 := by linear_combination hzder / 16
  refine ⟨Ψ,hΨ,hcont,?_,hcom,hzero,hder' ▸ hΨder,div_ne_zero hd (by norm_num)⟩
  intro z hz
  by_cases h : z = p
  · simpa [h] using hn'
  · rw [hΨ ⟨hz,h⟩]
    exact hmap z ⟨hz,h⟩

/-- Turn a continuous lift through the actual punctured cusp covering into
a holomorphic filled lift on the same open preconnected set. -/
theorem cuspLift_fill_continuous {D : Set ℂ} {f : ℂ → ℂ} {p d : ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (hp : p ∈ D)
    (hf : DifferentiableOn ℂ f D)
    (F : C(↥(D \ {p}), PuncturedUnitDisc))
    (hF : ∀ z : ↥(D \ {p}), (cuspUPunctured (F z) : ℂ) = f z)
    (hf₀ : f p = 1) (hder : HasDerivAt f d p) (hd : d ≠ 0) :
    ∃ Ψ : ℂ → ℂ,
      (∀ z : ↥(D \ {p}), Ψ z = (F z : ℂ)) ∧
      DifferentiableOn ℂ Ψ D ∧ (∀ z ∈ D, ‖Ψ z‖ < 1) ∧
      (∀ z ∈ D, cuspU (Ψ z) = f z) ∧
      Ψ p = 0 ∧ HasDerivAt Ψ (d / 16) p ∧ d / 16 ≠ 0 := by
  classical
  let φ : ℂ → ℂ := fun z ↦ if hz : z ∈ D \ {p} then (F ⟨z, hz⟩ : ℂ) else 0
  have hφ (z) (hz : z ∈ D \ {p}) : φ z = (F ⟨z,hz⟩ : ℂ) := by simp only [φ, dite_eq_left hz]
  have hcont : ContinuousOn φ (D \ {p}) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp F.continuous).congr fun z ↦ (hφ z z.property).symm
  have hmap (z) (hz : z ∈ D \ {p}) : ‖φ z‖ < 1 ∧ φ z ≠ 0 := by
    rw [hφ z hz]
    exact (F ⟨z, hz⟩).property
  have hcomp (z) (hz : z ∈ D \ {p}) : cuspU (φ z) = f z := by
    rw [hφ z hz, ← cuspUPunctured_coe]
    exact hF ⟨z, hz⟩
  have hh := cuspLift_differentiableOn (hD.sdiff isClosed_singleton)
    (hf.mono sdiff_subset) hcont hmap hcomp
  obtain ⟨Ψ, hEq, hDiff, hnorm, hU, hzero, hder', hne⟩ :=
    cuspLift_fill hD hconn hp hh (fun z hz ↦ (hmap z hz).1) hcomp hf₀ hder hd
  exact ⟨Ψ, fun z ↦ (hEq z.property).trans (hφ z z.property),
    hDiff, hnorm, hU, hzero, hder', hne⟩

end BelgianChocolate.ModularLambdaRatio

