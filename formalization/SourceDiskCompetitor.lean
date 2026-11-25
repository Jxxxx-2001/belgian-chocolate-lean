import SourceDiskPaths
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Normalize a single source competitor for use in both annulus arguments. -/

namespace BelgianChocolate.SourceDiskPaths

open Complex Metric Set Topology
open BelgianChocolate.FirstAnnulusPaths (cutDomain)

/-- The holomorphic disk competitor with the three prescribed simple
preimages. It defines a map to the twice-punctured plane on the source disk. -/
structure MarkedCompetitor (t : ℝ) (f : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ f (ball 0 1)
  avoids : MapsTo f (sourceDisk t) ({0, 1}ᶜ : Set ℂ)
  zero_value : f 0 = 0
  plus_value : f ((t : ℂ) * Complex.I) = 1
  minus_value : f (-(t : ℂ) * Complex.I) = 1
  zero_simple : ∃ d, HasDerivAt f d 0 ∧ d ≠ 0
  plus_simple : ∃ d, HasDerivAt f d ((t : ℂ) * Complex.I) ∧ d ≠ 0
  minus_simple : ∃ d, HasDerivAt f d (-(t : ℂ) * Complex.I) ∧ d ≠ 0

noncomputable def normalized (t : ℝ) (f : ℂ → ℂ) : ℂ → ℂ :=
  f ∘ unscale t

theorem unscale_hasDerivAt (t : ℝ) (s : ℂ) :
    HasDerivAt (unscale t) (-(t : ℂ) * Complex.I) s := by
  unfold unscale
  simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (-(t : ℂ) * Complex.I)

theorem normalized_hasDerivAt {t : ℝ} {f : ℂ → ℂ} {s d : ℂ}
    (h : HasDerivAt f d (unscale t s)) :
    HasDerivAt (normalized t f) (d * (-(t : ℂ) * Complex.I)) s :=
  HasDerivAt.comp s h (unscale_hasDerivAt t s)

theorem normalized_hasDerivAt_ne_zero {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ} {s : ℂ}
    (h : ∃ d, HasDerivAt f d (unscale t s) ∧ d ≠ 0) :
    ∃ d, HasDerivAt (normalized t f) d s ∧ d ≠ 0 := by
  obtain ⟨d, hd, hne⟩ := h
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  exact ⟨_, normalized_hasDerivAt hd, mul_ne_zero hne (mul_ne_zero (neg_ne_zero.mpr htc) Complex.I_ne_zero)⟩

theorem normalized_mapsTo {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : MarkedCompetitor t f) :
    MapsTo (normalized t f) (scaledDisk t) ({0, 1}ᶜ : Set ℂ) :=
  hf.avoids.comp (unscale_mapsTo ht)

theorem normalized_cut_mapsTo {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : MarkedCompetitor t f) :
    MapsTo (normalized t f) (cutDomain t) ({0, 1}ᶜ : Set ℂ) :=
  (normalized_mapsTo ht hf).mono (cut_subset_scaledDisk t) Subset.rfl

theorem normalized_differentiableOn {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : MarkedCompetitor t f) :
    DifferentiableOn ℂ (normalized t f) (ball 0 (1 / t)) := by
  refine hf.holomorphic.comp (fun s _ => (unscale_hasDerivAt t s).differentiableAt.differentiableWithinAt) ?_
  intro s hs
  apply mem_ball_zero_iff.mpr
  rw [norm_unscale ht, mul_comm]
  exact (lt_div_iff₀ ht).mp (mem_ball_zero_iff.mp hs)

theorem normalized_cut_differentiableOn {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : MarkedCompetitor t f) : DifferentiableOn ℂ (normalized t f) (cutDomain t) :=
  (normalized_differentiableOn ht hf).mono (fun _ hs => mem_ball_zero_iff.mpr hs.1)

theorem normalized_values {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    normalized t f 0 = 0 ∧ normalized t f (-1) = 1 ∧ normalized t f 1 = 1 := by
  exact ⟨by simpa [normalized] using hf.zero_value,
    by simpa [normalized, unscale_neg_one ht] using hf.plus_value,
    by simpa [normalized, unscale_one ht] using hf.minus_value⟩

theorem normalized_simple {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    {p : ℂ} (hp : p = 0 ∨ p = -1 ∨ p = 1) :
    ∃ d, HasDerivAt (normalized t f) d p ∧ d ≠ 0 := by
  apply normalized_hasDerivAt_ne_zero ht
  rcases hp with rfl | rfl | rfl
  · simpa using hf.zero_simple
  · simpa only [unscale_neg_one ht] using hf.plus_simple
  · simpa only [unscale_one ht] using hf.minus_simple

theorem normalized_continuousOn_marked_ball {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) {p : ℂ} (hp : p = 0 ∨ p = -1 ∨ p = 1) :
    ContinuousOn (normalized t f) (ball p 1) := by
  apply (normalized_differentiableOn ht hf).continuousOn.mono
  intro s hs
  have hsp : ‖s - p‖ < 1 := by simpa [Complex.dist_eq] using hs
  have hR : 10 ≤ 1 / t := (le_div_iff₀ ht).2 (by linarith)
  have hnp : ‖p‖ ≤ 1 := by rcases hp with rfl | rfl | rfl <;> norm_num
  have hn := norm_add_le (s - p) p
  rw [sub_add_cancel] at hn
  exact mem_ball_zero_iff.mpr (by linarith)

noncomputable def sourceMap {t : ℝ} {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    C(sourceDisk t, ({0, 1}ᶜ : Set ℂ)) where
  toFun z := ⟨f z, hf.avoids z.property⟩
  continuous_toFun := by
    have hsub : sourceDisk t ⊆ ball (0 : ℂ) 1 := fun _ hz => mem_ball_zero_iff.mpr hz.1
    exact (hf.holomorphic.continuousOn.mono hsub).domRestrict.subtype_mk _

noncomputable def normalizedMap {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : MarkedCompetitor t f) : C(scaledDisk t, ({0, 1}ᶜ : Set ℂ)) :=
  (sourceMap hf).comp ⟨(scaleHomeomorph ht).symm, (scaleHomeomorph ht).symm.continuous⟩

noncomputable def normalizedCutMap {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : MarkedCompetitor t f) : C(cutDomain t, ({0, 1}ᶜ : Set ℂ)) :=
  (normalizedMap ht hf).comp (cutInclusion t)

theorem normalizedMap_apply {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (s : scaledDisk t) : (normalizedMap ht hf s : ℂ) = normalized t f s := rfl

theorem normalizedCutMap_apply {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (s : cutDomain t) : (normalizedCutMap ht hf s : ℂ) = normalized t f s := rfl

theorem normalized_image_zero_cut {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    (scaledGammaZero ht ht').map (normalizedMap ht hf).continuous =
      (FirstAnnulusPaths.gammaZero ht ht').map (normalizedCutMap ht hf).continuous := by
  ext u
  rfl

theorem normalized_image_plus_cut {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    (scaledGammaPlus ht ht').map (normalizedMap ht hf).continuous =
      (FirstAnnulusPaths.gammaPlus ht ht').map (normalizedCutMap ht hf).continuous := by
  ext u
  rfl

theorem source_image_zero_eq_normalized {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    (sourceGammaZero ht ht').map (sourceMap hf).continuous =
      (scaledGammaZero ht ht').map (normalizedMap ht hf).continuous := by
  ext u
  rfl

theorem source_image_plus_eq_normalized {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    (sourceGammaPlus ht ht').map (sourceMap hf).continuous =
      (scaledGammaPlus ht ht').map (normalizedMap ht hf).continuous := by
  ext u
  rfl

theorem source_image_minus_eq_normalized {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    (sourceGammaMinus ht ht').map (sourceMap hf).continuous =
      (scaledGammaMinus ht ht').map (normalizedMap ht hf).continuous := by
  ext u
  rfl

theorem source_image_triple_eq_normalized {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    (sourceTripleWord ht ht').map (sourceMap hf).continuous =
      (scaledTripleWord ht ht').map (normalizedMap ht hf).continuous := by
  simp only [sourceTripleWord, scaledTripleWord, Path.map_trans, source_image_zero_eq_normalized,
    source_image_plus_eq_normalized, source_image_minus_eq_normalized]
  rfl

end BelgianChocolate.SourceDiskPaths

