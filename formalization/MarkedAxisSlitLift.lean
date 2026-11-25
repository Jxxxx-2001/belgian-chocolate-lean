import UpperHalfDiskCuspLift
import MarkedAxisSlit
import SourceDiskR17Normalization

/-! Lifting the actual disk competitor on the common slit domain using its
verified one-cusp monodromy from the first annulus. -/

namespace BelgianChocolate.MarkedAxisSlit

open Complex Set UpperHalfPlane
open BelgianChocolate.SourceDiskPaths BelgianChocolate.ModularLambdaRatio
open scoped MatrixGroups

/-- Restriction of the actual competitor to the punctured slit domain. -/
noncomputable def slitSourceMap {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : MarkedCompetitor t f) : C(Domain t, ({0,1}ᶜ : Set ℂ)) :=
  (sourceMap hf).comp (inclusion ht)

/-- The canonical modular step around the upper puncture gives a unique cusp
lift on the slit domain, based at the marked projection of the same fibre point. -/
theorem existsUnique_cuspULift_of_sourceGammaPlus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')})
    (hplus : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((sourceGammaPlus ht ht').map (sourceMap hf).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ oneCuspDeck e) :
    ∃! F : C(Domain t, PuncturedUnitDisc),
      F (basepoint ht ht') = markedCuspDisc e ∧ cuspUPunctured ∘ F = slitSourceMap ht hf := by
  obtain ⟨c, T, R, hR, hmap⟩ := plus_paths ht ht'
  let v : lambdaPunctured ⁻¹' {slitSourceMap ht hf (basepoint ht ht')} := e
  have hmaps : ((T.trans R).trans T.symm).map (slitSourceMap ht hf).continuous =
      (sourceGammaPlus ht ht').map (sourceMap hf).continuous := by
    rw [← hmap]
    ext u
    rfl
  have hdeck : (lambdaPunctured_isCoveringMap.monodromy
      (.mk (((T.trans R).trans T.symm).map (slitSourceMap ht hf).continuous)) v : ℍ) =
        oneCuspDeck • (v : ℍ) := by
    rw [hmaps]
    exact congrArg Subtype.val hplus
  exact UpperHalfDisk.existsUnique_cuspULift_of_tailed_circleMap_oneCuspDeck
    (slit_star ht (by linarith)) isOpen_slit (by positivity) (sphere_subset ht ht')
    (slitSourceMap ht hf) T R Real.pi hR v hdeck

#print axioms existsUnique_cuspULift_of_sourceGammaPlus

/-- The verified first-annulus normalization supplies the based slit lift
on the same modular fibre point which carries both canonical peripheral labels. -/
theorem exists_r17_cuspULift {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    ∃ e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')},
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaZero ht ht').map (sourceMap hf).continuous)) e =
          lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((sourceGammaPlus ht ht').map (sourceMap hf).continuous)) e =
          lambdaPunctured_quotientCovering.toPermFiber _ oneCuspDeck e ∧
      (∃! F : C(Domain t, PuncturedUnitDisc),
        F (basepoint ht ht') = markedCuspDisc e ∧ cuspUPunctured ∘ F = slitSourceMap ht hf) := by
  obtain ⟨e, hzero, hplus⟩ := r17_source_common_lift ht ht' hf
  exact ⟨e, hzero, hplus, existsUnique_cuspULift_of_sourceGammaPlus ht ht' hf e hplus⟩

#print axioms exists_r17_cuspULift
end BelgianChocolate.MarkedAxisSlit

