import MarkedCompetitorComparison
import MarkedAxisSlitBoundaryLimit

/-! The candidate's boundary contact at i excludes an ordinary value of a finite controller. -/

namespace BelgianChocolate.HarmonicComparison

open Complex Metric Set Filter Topology
open BelgianChocolate.SourceDiskPaths BelgianChocolate.MarkedAxisSlit
open BelgianChocolate.ModularLambdaRatio BelgianChocolate.ControlWitness

theorem regular_at_I_incompatible_with_candidate {t : ℝ} (ht : 0 < t) (ht₁ : t < 1)
    {f φ Φ : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hφ : DifferentiableOn ℂ φ slit) (hn : ∀ z ∈ slit, ‖φ z‖ < 1)
    (hU : ∀ z ∈ slit, cuspU (φ z) = f z)
    (hΦ : ComparisonCandidate t Φ) (hEq : EqOn φ Φ comparisonHalfDisk)
    (hreg : ContinuousAt f I) (hv : f I ∈ ({0,1}ᶜ : Set ℂ)) : False := by
  let S := slit \ {UpperHalfDisk.puncture t}
  have hφ₀ (z : Domain t) : φ z ≠ 0 := by
    intro he
    have hvz := hf.avoids (slit_subset_source ht z.property)
    rw [← hU z z.property.1, he, cuspU_zero] at hvz
    exact hvz (by simp)
  let F : C(Domain t, PuncturedUnitDisc) :=
    ⟨fun z ↦ ⟨φ z, hn z z.property.1, hφ₀ z⟩,
      ((hφ.continuousOn.mono sdiff_subset).domRestrict).subtype_mk _⟩
  have hp : Tendsto (fun z : Domain t ↦ (cuspUPunctured (F z) : ℂ))
      (comap (Subtype.val : Domain t → ℂ) (𝓝 I)) (𝓝 (f I)) := by
    have hh := hreg.tendsto.comp (show Tendsto (Subtype.val : Domain t → ℂ)
        (comap Subtype.val (𝓝 I)) (𝓝 I) from Filter.map_comap_le)
    apply hh.congr
    intro z
    rw [cuspUPunctured_coe]
    exact (hU z z.property.1).symm
  obtain ⟨e, _, he⟩ := cuspULift_tendsto_of_regular_boundary ht ht₁ F
    (by simp) (Or.inr (by simp)) hv hp
  have htφ : Tendsto φ (𝓝[S] I) (𝓝 (e : ℂ)) := by
    have h := (continuous_subtype_val.continuousAt (x := e)).tendsto.comp he
    rw [nhdsWithin, ← Filter.map_comap_setCoe_val (𝓝 I) S, Filter.tendsto_map'_iff]
    exact h
  let T := comparisonHalfDisk \ {UpperHalfDisk.puncture t}
  have hdom : comparisonHalfDisk = UpperHalfDisk.domain := comparisonHalfDisk_eq_norm
  have hTS : T ⊆ S := fun _ hz ↦ ⟨upper_subset_slit (hdom ▸ hz.1),hz.2⟩
  have hI : I ∈ comparisonOuterArc := by exact ⟨by simp, by simp⟩
  have hcI : I ∈ closure T := by
    let g : ℝ → ℂ := fun r ↦ (r : ℂ) * I
    have hg : Continuous g := by fun_prop
    have h₁ : (1 : ℝ) ∈ closure (Ioo t 1) := by
      rw [closure_Ioo ht₁.ne]
      exact ⟨ht₁.le,le_rfl⟩
    have hs : g '' Ioo t 1 ⊆ T := by
      rintro _ ⟨r, hr, rfl⟩
      have hr₀ := ht.trans hr.1
      constructor
      · rw [comparisonHalfDisk_eq_norm]
        exact ⟨by simpa [g, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀] using hr.2,
          by simpa [g] using hr₀⟩
      · intro h
        have he := congrArg Complex.im (show g r = UpperHalfDisk.puncture t from h)
        simp [g,UpperHalfDisk.puncture] at he
        linarith [hr.1]
    have hh := image_closure_subset_closure_image hg (s := Ioo t 1) ⟨1,h₁,rfl⟩
    simpa [g] using closure_mono hs hh
  have hc : I ∈ closure comparisonHalfDisk := closure_mono (sdiff_subset : T ⊆ _) hcI
  let _ := mem_closure_iff_nhdsWithin_neBot.mp hcI
  have hφlim' := htφ.mono_left (nhdsWithin_mono _ hTS)
  have hΦlim : Tendsto Φ (𝓝[T] I) (𝓝 (Φ I)) :=
    (hΦ.continuous I hc).mono (sdiff_subset.trans subset_closure)
  have heq : φ =ᶠ[𝓝[T] I] Φ :=
    Filter.mem_of_superset self_mem_nhdsWithin fun _ hz ↦ hEq hz.1
  have hval : (e : ℂ) = Φ I := tendsto_nhds_unique hφlim' (hΦlim.congr' heq.symm)
  have he₁ : ‖(e : ℂ)‖ = 1 := hval ▸ (hΦ.outer hI).1
  exact e.property.1.ne he₁

/-- A positively oriented endpoint competitor cannot have a continuous ordinary
value at the upper point of the circular boundary. -/
theorem endpoint_regular_at_I_impossible {t : ℝ} (ht : 0 < t) (ht₁ : t < 1)
    (hsmall : t ≤ 1/10) {f Φ : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hreal : RealSymmetricOnDisk f) {d : ℝ} (hd : HasDerivAt f (d : ℂ) 0)
    (hpos : 0 < d) (hΦ : ComparisonCandidate t Φ)
    (hreg : ContinuousAt f I) (hv : f I ∈ ({0,1}ᶜ : Set ℂ)) : False := by
  obtain ⟨φ, hφ, hn, hU, hz, _, hneg, hpositive⟩ :=
    exists_marked_competitor_lift ht hsmall hf hreal hd hpos
  obtain ⟨η, hη⟩ := exists_centered_comparisonChart ht ht₁
  have heq := (eq_parameter_and_lift_of_marked_competitor ht ht le_rfl hη hΦ
    hφ hn hz hneg hpositive).2
  exact regular_at_I_incompatible_with_candidate ht ht₁ hf hφ hn hU hΦ heq hreg hv

/-- For a real-symmetric endpoint competitor of either orientation, at least
one of the two antipodal boundary points fails to have an ordinary value. -/
theorem endpoint_regular_at_both_impossible {t : ℝ} (ht : 0 < t) (ht₁ : t < 1)
    (hsmall : t ≤ 1/10) {f Φ : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hreal : RealSymmetricOnDisk f) (hΦ : ComparisonCandidate t Φ)
    (hupper : ContinuousAt f I ∧ f I ∈ ({0,1}ᶜ : Set ℂ))
    (hlower : ContinuousAt f (-I) ∧ f (-I) ∈ ({0,1}ᶜ : Set ℂ)) : False := by
  obtain ⟨g, d, hg, hgm, hgr, hgd, him, hpos⟩ := exists_positive_source_derivative hf hreal
  have hdc : (d.re : ℂ) = d := Complex.ext rfl (by simpa using him.symm)
  have hr : ContinuousAt g I ∧ g I ∈ ({0,1}ᶜ : Set ℂ) := by
    rcases hg with rfl | rfl
    · exact hupper
    · exact ⟨hlower.1.comp (continuous_neg.continuousAt (x := I)), hlower.2⟩
  exact endpoint_regular_at_I_impossible ht ht₁ hsmall hgm hgr (hdc.symm ▸ hgd) hpos hΦ
    hr.1 hr.2

end BelgianChocolate.HarmonicComparison
