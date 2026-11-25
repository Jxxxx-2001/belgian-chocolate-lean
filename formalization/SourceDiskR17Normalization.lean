import SourceDiskCompetitor
import FirstAnnulusMarkedNormalization

/-! Apply the first-annulus normalization to the original disk competitor and
choose a common lift with the canonical first two labels. -/

namespace BelgianChocolate.SourceDiskPaths

open Complex Metric Set Topology UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open BelgianChocolate.FirstAnnulus
open BelgianChocolate.ModularLambdaRatio
open scoped MatrixGroups

theorem normalizedCutMap_eq_cutCompetitor {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : MarkedCompetitor t f) :
    normalizedCutMap ht hf =
      cutCompetitor (normalized t f) (normalized_cut_differentiableOn ht hf)
        (normalized_cut_mapsTo ht hf) := by
  ext z
  rfl

private theorem translate_mem_gammaTwo (k : ℤ) : translate k ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [translate, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_mul]
  exact Or.inl (by decide)

/-- One lift of the actual source basepoint gives the canonical positive zero
and one generators on the original marked zero and upper paths. -/
theorem r17_source_common_lift {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    ∃ e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')},
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaZero ht ht').map (sourceMap hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaPlus ht ht').map (sourceMap hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ oneCuspDeck e := by
  obtain ⟨hz, hplus, _⟩ := normalized_values ht hf
  obtain ⟨d₀, hd₀, hne₀⟩ := normalized_simple ht hf (p := 0) (Or.inl rfl)
  obtain ⟨d₁, hd₁, hne₁⟩ := normalized_simple ht hf (p := -1) (Or.inr (Or.inl rfl))
  obtain ⟨e, M, hM, hzero, hone, _, k, hk₀, hk₁⟩ :=
    r17_lambda_normalization_of_simple_preimages ht ht'
      (normalized_cut_differentiableOn ht hf) (normalized_cut_mapsTo ht hf) hz hplus
      (ε₀ := 1) (ε₁ := 1) zero_lt_one zero_lt_one
      (normalized_continuousOn_marked_ball ht ht' hf (p := 0) (Or.inl rfl))
      (normalized_continuousOn_marked_ball ht ht' hf (p := -1) (Or.inr (Or.inl rfl)))
      hd₀ hd₁ hne₀ hne₁
  let e₀ : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')} := e
  let K := congruenceLabel (translate k) (translate_mem_gammaTwo k)
  have g₀ : K * zeroDeckLabel * K⁻¹ = zeroCuspDeck := by
    apply Subtype.ext
    change sl2zToPSL2R (translate k) * sl2zToPSL2R zeroGenerator *
      (sl2zToPSL2R (translate k))⁻¹ = sl2zToPSL2R zeroGenerator
    simpa only [map_mul, map_inv] using congrArg sl2zToPSL2R hk₀
  have g₁ : K * conjugateOneDeckLabel M hM * K⁻¹ = oneCuspDeck := by
    apply Subtype.ext
    change sl2zToPSL2R (translate k) * sl2zToPSL2R (M * oneGenerator * M⁻¹) *
      (sl2zToPSL2R (translate k))⁻¹ = sl2zToPSL2R oneGenerator
    simpa only [map_mul, map_inv] using congrArg sl2zToPSL2R hk₁
  have hzero' : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((sourceGammaZero ht ht').map (sourceMap hf).continuous)) e₀ =
      lambdaPunctured_quotientCovering.toPermFiber _ zeroDeckLabel e₀ := by
    rw [source_image_zero_eq_normalized, normalized_image_zero_cut]
    exact hzero
  have hone' : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((sourceGammaPlus ht ht').map (sourceMap hf).continuous)) e₀ =
      lambdaPunctured_quotientCovering.toPermFiber _ (conjugateOneDeckLabel M hM) e₀ := by
    rw [source_image_plus_eq_normalized, normalized_image_plus_cut]
    exact hone
  refine ⟨lambdaPunctured_quotientCovering.toPermFiber _ K e₀, ?_, ?_⟩
  · simpa only [g₀] using
      FirstAnnulusTransport.deck_label_change_initial_lift lambdaPunctured_quotientCovering
        ((sourceGammaZero ht ht').map (sourceMap hf).continuous) e₀ zeroDeckLabel K hzero'
  · simpa only [g₁] using
      FirstAnnulusTransport.deck_label_change_initial_lift lambdaPunctured_quotientCovering
        ((sourceGammaPlus ht ht').map (sourceMap hf).continuous) e₀ (conjugateOneDeckLabel M hM) K hone'

theorem r17_scaled_common_lift {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    ∃ e : lambdaPunctured ⁻¹' {normalizedMap ht hf (scaledBasepoint ht ht')},
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((scaledGammaZero ht ht').map (normalizedMap ht hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((scaledGammaPlus ht ht').map (normalizedMap ht hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ oneCuspDeck e := by
  obtain ⟨e, hzero, hplus⟩ := r17_source_common_lift ht ht' hf
  rw [source_image_zero_eq_normalized] at hzero
  rw [source_image_plus_eq_normalized] at hplus
  exact ⟨e, hzero, hplus⟩

end BelgianChocolate.SourceDiskPaths

