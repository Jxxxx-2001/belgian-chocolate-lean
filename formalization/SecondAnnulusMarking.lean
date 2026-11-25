import SecondAnnulusSigns
import SecondAnnulusWordLength
import SourceDiskR17Normalization
import SecondAnnulusMarkedReflection

/-! The actual disk competitor has common markings determined by the two annuli. -/

namespace BelgianChocolate.SecondAnnulus

open Complex Set Metric UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open BelgianChocolate.FirstAnnulus BelgianChocolate.ModularLambdaRatio
open BelgianChocolate.ModularLambdaReflection
open BelgianChocolate.SourceDiskPaths
open scoped MatrixGroups

/-- An effective deck reflection centralizing the zero cusp fixes only the
vertical line with real part equal to its translation index. -/
theorem reflection_translation_index (g : gammaTwoProjective) (e : ℍ)
    (hfix : deckReflection g e = e) (hcomm : Commute g zeroCuspDeck) :
    ∃ n : ℤ, g = congruenceLabel (translate n) (translate_mem_gammaTwo n) ∧
      e.re = (n : ℝ) ∧ g * oneCuspDeck * g⁻¹ = reflectedDeck n := by
  obtain ⟨M, hM, hproj⟩ := g.property
  have hc : Commute (sl2zToPSL2R M) (sl2zToPSL2R zeroGenerator) := by
    rw [hproj]
    exact congrArg Subtype.val hcomm.eq
  obtain ⟨n, hn⟩ := projective_centralizer_zero hM hc
  have hg : g = congruenceLabel (translate n) (translate_mem_gammaTwo n) :=
    Subtype.ext (hproj.symm.trans hn)
  have h : (translate n) • (J • e) = e := by
    change g • (J • e) = e at hfix
    rw [hg] at hfix
    change sl2zToPSL2R (translate n) • (J • e) = e at hfix
    rwa [UpperHalfPlane.sl2zToPSL2R_smul] at hfix
  refine ⟨n, hg, ?_, ?_⟩
  · have hre := congrArg (fun x : ℍ ↦ (x : ℂ).re) h
    change ((↑((translate n) • (J • e) : ℍ) : ℂ)).re = (e : ℂ).re at hre
    rw [translate_coe_smul, Complex.add_re, Complex.intCast_re,
      UpperHalfPlane.coe_J_smul] at hre
    have hre' : -(e : ℂ).re + (↑(2 * n) : ℝ) = (e : ℂ).re := by simpa using hre
    push_cast at hre'
    change (e : ℂ).re = _
    linarith
  · rw [hg]
    apply Subtype.ext
    change sl2zToPSL2R (translate n) * sl2zToPSL2R oneGenerator *
      (sl2zToPSL2R (translate n))⁻¹ = sl2zToPSL2R (reflectedGenerator n)
    simp only [reflectedGenerator, map_mul, map_inv]

theorem normalizedMap_eq_scaledCompetitor {t : ℝ} (ht : 0 < t)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    normalizedMap ht hf =
      scaledCompetitor (normalized t f)
        ((normalized_differentiableOn ht hf).mono fun _ hz ↦ mem_ball_zero_iff.mpr hz.1)
        (normalized_mapsTo ht hf) := by
  ext z
  rfl

theorem competitor_negative_at_basepoint {t : ℝ} (ht : 0 < t)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hreal : ∀ z ∈ ball (0 : ℂ) 1, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    {d : ℝ} (hder : HasDerivAt f (d : ℂ) 0) (hd : 0 < d) :
    (f (-1/2)).re < 0 := by
  have hm (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 0) : (x : ℂ) ∈ sourceDisk t := by
    have h₀ : (x : ℂ) ≠ 0 := by exact_mod_cast hx.2.ne
    have hp : (x : ℂ) ≠ (t : ℂ) * Complex.I := by
      intro h
      have he := congrArg Complex.im h
      simp at he
      linarith
    have hm : (x : ℂ) ≠ -(t : ℂ) * Complex.I := by
      intro h
      have he := congrArg Complex.im h
      simp at he
      linarith
    have hn : ‖(x : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_lt.mpr ⟨hx.1, hx.2.trans zero_lt_one⟩
    exact ⟨hn, h₀, hp, hm⟩
  apply source_negative_at_basepoint hf.holomorphic.continuousOn hf.zero_value hder hd
  · intro x hx
    have he := hreal (x : ℂ) (mem_ball_zero_iff.mpr (hm x hx).1)
    simpa using he
  · intro x hx
    have he := hf.avoids (hm x hx)
    intro h
    apply he
    rw [h]
    exact mem_insert _ _

/-- A normalized original disk competitor has an actual common lift whose
real part is one. Both annuli determine labels of loops in the source disk. -/
theorem r19_source_common_lift {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hreal : ∀ z ∈ ball (0 : ℂ) 1, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    {d : ℝ} (hder : HasDerivAt f (d : ℂ) 0) (hd : 0 < d) :
    ∃ e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')},
      (e : ℍ).re = 1 ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaZero ht ht').map (sourceMap hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaPlus ht ht').map (sourceMap hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ oneCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaMinus ht ht').map (sourceMap hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ (reflectedDeck 1) e := by
  obtain ⟨e, g, hfix, hcomm, hzero, hplus, hminus⟩ :=
    BelgianChocolate.SecondAnnulusReflection.r17_real_competitor_reflection_labels ht ht' hf hreal
  obtain ⟨n, _, hre, htlabel⟩ := reflection_translation_index g (e : ℍ) hfix hcomm
  have hval : lambdaRatio (e : ℍ) = f (-1/2) := by
    calc
      lambdaRatio (e : ℍ) = (sourceMap hf (sourceBasepoint ht ht') : ℂ) :=
        congrArg Subtype.val e.property
      _ = f (-1/2) := congrArg f (sourceBasepoint_coe ht ht')
  have hodd : Odd n := reflection_index_odd_of_negative _ n hre
    (hval ▸ competitor_negative_at_basepoint ht hf hreal hder hd)
  rw [htlabel] at hminus
  have h1 : n = 1 := by
    rw [source_image_zero_eq_normalized] at hzero
    rw [source_image_plus_eq_normalized] at hplus
    rw [source_image_minus_eq_normalized] at hminus
    exact r19_one_of_three_peripheral_labels ht ht'
      ((normalized_differentiableOn ht hf).mono fun _ hz ↦ mem_ball_zero_iff.mpr hz.1)
      (normalized_mapsTo ht hf) e hodd hminus hzero hplus
  subst n
  exact ⟨e, by simpa using hre, hzero, hplus, hminus⟩

end BelgianChocolate.SecondAnnulus