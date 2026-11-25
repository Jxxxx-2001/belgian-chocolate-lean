import SecondAnnulusCoreComparison
import SecondAnnulusTripleWord
import SecondAnnulusCoreLength
import ModularLambdaCuspLabels

/-! Trace normalization from the marked three-letter word in the full punctured disk. -/

namespace BelgianChocolate.SecondAnnulus

open Complex Set UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups
open BelgianChocolate.FirstAnnulus (positiveCircleLoop zeroGenerator oneGenerator)
open BelgianChocolate.FirstAnnulusTransport (deck_labels_trans)
open BelgianChocolate.SourceDiskPaths
open BelgianChocolate.ModularLambdaRatio
open BelgianChocolate.SecondAnnulusTopology (referenceCircle referenceLoop)

/-- A deck label of the marked word at a chosen lift is the same label at the lift
reached by following its geometric tail to the true elliptical strip center. -/
theorem center_label_of_tailed_word {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {b : scaledDisk t} (word : Path b b) (f : C(scaledDisk t, ({0,1}ᶜ : Set ℂ)))
    (hword : ∃ q : Path b (stripCenterCircle ht ht' 1),
      ((q.trans (positiveCircleLoop.map (stripCenterCircle ht ht').continuous)).trans q.symm).Homotopic word)
    (e : lambdaPunctured ⁻¹' {f b}) (g : gammaTwoProjective)
    (hlabel : lambdaPunctured_isCoveringMap.monodromy (.mk (word.map f.continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ g e) :
    ∃ e' : lambdaPunctured ⁻¹' {f (stripCenterCircle ht ht' 1)},
      lambdaPunctured_isCoveringMap.monodromy (.mk (imageCenterLoop ht ht' f)) e' =
        lambdaPunctured_quotientCovering.toPermFiber _ g e' := by
  obtain ⟨q,hq⟩ := hword
  let r := q.map f.continuous
  let δ := imageCenterLoop ht ht' f
  let W := word.map f.continuous
  have hmap : ((r.trans δ).trans r.symm).Homotopic W := by
    simpa only [r,δ,W,imageCenterLoop,Path.map_trans,← Path.map_symm] using hq.map f
  have heq := Path.Homotopic.Quotient.eq.mpr hmap
  simp only [Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm] at heq
  have hsq := congrArg (fun z => z.trans (Path.Homotopic.Quotient.mk r)) heq
  simp only [Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl] at hsq
  let hp := lambdaPunctured_isCoveringMap
  let e' := hp.monodromy (.mk r) e
  refine ⟨e',?_⟩
  have h := congrArg (fun v => hp.monodromy v e) hsq
  simp only [hp.monodromy_trans_apply] at h
  change hp.monodromy (.mk δ) e' = _
  rw [show hp.monodromy (.mk δ) e' = hp.monodromy (.mk r) (hp.monodromy (.mk W) e) from h,
    show hp.monodromy (.mk W) e = _ from hlabel, lambdaPunctured_quotientCovering.monodromy_toPermFiber]

/-- The reflected negative source puncture, as an element of the effective deck group. -/
def reflectedDeck (n : ℤ) : gammaTwoProjective :=
  ⟨sl2zToPSL2R (reflectedGenerator n), reflectedGenerator n, reflectedGenerator_mem_gammaTwo n, rfl⟩

/-- The three peripheral labels are based at one lift and compose in source traversal order. -/
theorem scaledTripleWord_label {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    (f : C(scaledDisk t, ({0,1}ᶜ : Set ℂ)))
    (e : lambdaPunctured ⁻¹' {f (scaledBasepoint ht ht')}) (n : ℤ)
    (hm : lambdaPunctured_isCoveringMap.monodromy (.mk ((scaledGammaMinus ht ht').map f.continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ (reflectedDeck n) e)
    (hz : lambdaPunctured_isCoveringMap.monodromy (.mk ((scaledGammaZero ht ht').map f.continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e)
    (hp : lambdaPunctured_isCoveringMap.monodromy (.mk ((scaledGammaPlus ht ht').map f.continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ oneCuspDeck e) :
    lambdaPunctured_isCoveringMap.monodromy (.mk ((scaledTripleWord ht ht').map f.continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ (reflectedDeck n * zeroCuspDeck * oneCuspDeck) e := by
  have hp₁ := deck_labels_trans lambdaPunctured_quotientCovering _ _ _ _ _ hm hz
  have hp₂ := deck_labels_trans lambdaPunctured_quotientCovering _ _ _ _ _ hp₁ hp
  simpa only [scaledTripleWord,Path.map_trans] using hp₂

theorem tripleMatrix_projective (n : ℤ) : sl2zToPSL2R (tripleMatrix n) =
    ((reflectedDeck n * zeroCuspDeck * oneCuspDeck : gammaTwoProjective) : PSL(2,ℝ)) := by
  simp only [tripleMatrix, map_mul, Subgroup.coe_mul]
  rfl

/-- Derive the odd-index exclusion on the explicit Joukowski annulus using its established based
three-letter class and three individual deck labels at one lift. -/
theorem r19_one_of_three_peripheral_labels {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (scaledDisk t))
    (hm : MapsTo φ (scaledDisk t) ({0,1}ᶜ : Set ℂ))
    (e : lambdaPunctured ⁻¹' {scaledCompetitor φ hd hm (scaledBasepoint ht ht')})
    {n : ℤ} (hn : Odd n)
    (hminus : lambdaPunctured_isCoveringMap.monodromy (.mk
      ((scaledGammaMinus ht ht').map (scaledCompetitor φ hd hm).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ (reflectedDeck n) e)
    (hzero : lambdaPunctured_isCoveringMap.monodromy (.mk
      ((scaledGammaZero ht ht').map (scaledCompetitor φ hd hm).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e)
    (hplus : lambdaPunctured_isCoveringMap.monodromy (.mk
      ((scaledGammaPlus ht ht').map (scaledCompetitor φ hd hm).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ oneCuspDeck e) :
    n = 1 := by
  let f := scaledCompetitor φ hd hm
  obtain ⟨q,hq⟩ := SecondAnnulusTopology.scaledTripleWord_reference ht ht'
  have hword := stripCenter_word_of_reference_word ht ht' (scaledTripleWord ht ht') ⟨q,hq.symm⟩
  have htr := scaledTripleWord_label ht ht' f e n hminus hzero hplus
  obtain ⟨e', he'⟩ := center_label_of_tailed_word ht ht' _ f hword e _ htr
  apply r19_one_of_actual_center_monodromy ht ht' hd hm e' hn
  rw [show lambdaPunctured_isCoveringMap.monodromy (.mk (imageCenterLoop ht ht' f)) e' = _
    from he', tripleMatrix_projective]
  rfl

end BelgianChocolate.SecondAnnulus

