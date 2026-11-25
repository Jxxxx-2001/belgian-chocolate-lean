import SecondAnnulusReflection
import SourceDiskR17Normalization
import SourceDiskReflection

/-! The actual real-symmetric disk competitor gives a fixing reflection and
all three marked monodromies at the same normalized lift. -/
namespace BelgianChocolate.SecondAnnulusReflection

open Complex Metric Set Topology UpperHalfPlane
open BelgianChocolate.ModularLambdaRatio BelgianChocolate.ModularLambdaReflection
open BelgianChocolate.SourceDiskPaths
open scoped MatrixGroups ComplexConjugate

/-- The R17-normalized common lift of the actual disk competitor has a fixing
reflection whose correction centralizes the zero generator, and whose
conjugate of the one generator is the actual third peripheral label. -/
theorem r17_real_competitor_reflection_labels {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hreal : ∀ z ∈ ball (0 : ℂ) 1, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    ∃ (e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')})
      (g : gammaTwoProjective),
      deckReflection g (e : ℍ) = (e : ℍ) ∧ Commute g zeroCuspDeck ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaZero ht ht').map (sourceMap hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaPlus ht ht').map (sourceMap hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ oneCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaMinus ht ht').map (sourceMap hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ (g * oneCuspDeck * g⁻¹) e := by
  let b := sourceMap hf (sourceBasepoint ht ht')
  have hbase : (b : ℂ) = (starRingEnd ℂ) (b : ℂ) := by
    simpa only [Path.source] using
      reflected_source_image_apply ht ht' hf hreal (sourceGammaZero ht ht') (0 : unitInterval)
  have hb : (b : ℂ).im = 0 := by
    have h := congrArg Complex.im hbase
    simp only [Complex.conj_im] at h
    linarith
  obtain ⟨e, hzero, hplus⟩ := r17_source_common_lift ht ht' hf
  obtain ⟨g, hfix⟩ := exists_deckReflection_fixed hb e
  refine ⟨e, g, hfix, ?_, hzero, hplus, ?_⟩
  · apply correction_commutes_zero
      ((sourceGammaZero ht ht').map (sourceMap hf).continuous)
      ((reflectSourceLoop ht ht' (sourceGammaZero ht ht')).map (sourceMap hf).continuous)
      e g hfix
    · exact reflected_source_image_apply ht ht' hf hreal (sourceGammaZero ht ht')
    · simpa only [← Path.map_symm] using (sourceReflection_gammaZero ht ht').map (sourceMap hf)
    · exact hzero
  · apply third_label_of_reflection
      ((sourceGammaPlus ht ht').map (sourceMap hf).continuous)
      ((reflectSourceLoop ht ht' (sourceGammaPlus ht ht')).map (sourceMap hf).continuous)
      ((sourceGammaMinus ht ht').map (sourceMap hf).continuous) e g hfix
    · exact reflected_source_image_apply ht ht' hf hreal (sourceGammaPlus ht ht')
    · simpa only [← Path.map_symm] using (sourceReflection_gammaPlus ht ht').map (sourceMap hf)
    · exact hplus

/-- The same actual labels read in the scaled coordinate `s = iz/t`.
Physical real reflection is `s ↦ -conj s` in this coordinate. -/
theorem r17_normalized_real_competitor_reflection_labels {t : ℝ}
    (ht : 0 < t) (ht' : t ≤ 1 / 10) {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hreal : ∀ z ∈ ball (0 : ℂ) 1, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    ∃ (e : lambdaPunctured ⁻¹' {normalizedMap ht hf (scaledBasepoint ht ht')})
      (g : gammaTwoProjective),
      deckReflection g (e : ℍ) = (e : ℍ) ∧ Commute g zeroCuspDeck ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((scaledGammaZero ht ht').map (normalizedMap ht hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((scaledGammaPlus ht ht').map (normalizedMap ht hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ oneCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((scaledGammaMinus ht ht').map (normalizedMap ht hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ (g * oneCuspDeck * g⁻¹) e := by
  obtain ⟨e, g, hfix, hcomm, hzero, hplus, hminus⟩ :=
    r17_real_competitor_reflection_labels ht ht' hf hreal
  rw [source_image_zero_eq_normalized] at hzero
  rw [source_image_plus_eq_normalized] at hplus
  rw [source_image_minus_eq_normalized] at hminus
  exact ⟨e, g, hfix, hcomm, hzero, hplus, hminus⟩

#print axioms r17_real_competitor_reflection_labels
#print axioms r17_normalized_real_competitor_reflection_labels
end BelgianChocolate.SecondAnnulusReflection
