import SecondAnnulusEmbedding
import SecondAnnulusLambdaTrace
import AnnulusLengthArithmetic

/-! The trace bound on the actual second Joukowski center for a normalized competitor. -/

namespace BelgianChocolate.SecondAnnulus

open Complex Set UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups
open BelgianChocolate.FirstAnnulus (positiveCircleLoop logCenterSegment)
open BelgianChocolate.SourceDiskPaths (scaledDisk)
open BelgianChocolate.ModularLambdaRatio

/-- A holomorphic source competitor viewed as a map into the two-puncture target. -/
noncomputable def scaledCompetitor {t : ℝ} (φ : ℂ → ℂ)
    (hd : DifferentiableOn ℂ φ (scaledDisk t))
    (hm : MapsTo φ (scaledDisk t) ({0,1}ᶜ : Set ℂ)) :
    C(scaledDisk t, ({0,1}ᶜ : Set ℂ)) where
  toFun z := ⟨φ z, hm z.property⟩
  continuous_toFun := hd.continuousOn.domRestrict.subtype_mk _

/-- Image of the genuine positive center under a normalized competitor. -/
noncomputable def imageCenterLoop {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    (f : C(scaledDisk t, ({0,1}ᶜ : Set ℂ))) :
    Path (f (stripCenterCircle ht ht' 1)) (f (stripCenterCircle ht ht' 1)) :=
  (positiveCircleLoop.map (stripCenterCircle ht ht').continuous).map f.continuous

theorem imageCenterLoop_apply {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ (scaledDisk t))
    (hm : MapsTo φ (scaledDisk t) ({0,1}ᶜ : Set ℂ)) (u : unitInterval) :
    ((imageCenterLoop ht ht' (scaledCompetitor φ hd hm) u) : ℂ) =
      φ (normalizedEmbedding (Complex.exp (logCenterSegment (Real.log 19) 0 u))) :=
  congrArg φ (stripCenterCircle_positiveLoop ht ht' u)

/-- A matrix representing the actual lambda monodromy of this center obeys the radius-19
length bound and the strict integral trace bound. -/
theorem r19_trace_bound_of_center_monodromy {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (scaledDisk t))
    (hm : MapsTo φ (scaledDisk t) ({0,1}ᶜ : Set ℂ))
    (e : lambdaPunctured ⁻¹' {scaledCompetitor φ hd hm (stripCenterCircle ht ht' 1)})
    (g : SL(2,ℤ))
    (hg : sl2zToPSL2R g • (e : UpperHalfPlane) =
      (lambdaPunctured_isCoveringMap.monodromy
        (.mk (imageCenterLoop ht ht' (scaledCompetitor φ hd hm))) e : UpperHalfPlane)) :
    2 * Real.arcosh (|(((g : Matrix (Fin 2) (Fin 2) ℤ).trace : ℤ):ℝ)|/2) ≤
        2 * Real.pi^2/Real.log 19 ∧
      |(g : Matrix (Fin 2) (Fin 2) ℤ).trace| < 38 := by
  have h := trace_le_of_lambda_center_label (by norm_num : (1:ℝ) < 19) 0
    (hd.comp normalizedEmbedding_differentiableOn (normalizedEmbedding_mapsTo ht ht'))
    (hm.comp (normalizedEmbedding_mapsTo ht ht'))
    (imageCenterLoop ht ht' (scaledCompetitor φ hd hm))
    (fun u => (imageCenterLoop_apply ht ht' φ hd hm u).symm) e g hg
  refine ⟨h,?_⟩
  exact_mod_cast BelgianChocolate.AnnulusLengthArithmetic.abs_trace_lt_thirty_eight h

/-- The manuscript's odd reflection exponent must be one when its three-letter element
represents the observed center monodromy. -/
theorem r19_one_of_actual_center_monodromy {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (scaledDisk t))
    (hm : MapsTo φ (scaledDisk t) ({0,1}ᶜ : Set ℂ))
    (e : lambdaPunctured ⁻¹' {scaledCompetitor φ hd hm (stripCenterCircle ht ht' 1)})
    {n : ℤ} (hn : Odd n)
    (hg : sl2zToPSL2R (tripleMatrix n) • (e : UpperHalfPlane) =
      (lambdaPunctured_isCoveringMap.monodromy
        (.mk (imageCenterLoop ht ht' (scaledCompetitor φ hd hm))) e : UpperHalfPlane)) :
    n = 1 :=
  one_of_odd_and_length_bound hn (r19_trace_bound_of_center_monodromy ht ht' hd hm e _ hg).1

/-- For every initial lift, the actual center loop has an integral level-two representative
with the strict trace bound. Both the representative and its label are obtained from the covering. -/
theorem r19_exists_bounded_integral_label {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (scaledDisk t))
    (hm : MapsTo φ (scaledDisk t) ({0,1}ᶜ : Set ℂ))
    (e : lambdaPunctured ⁻¹' {scaledCompetitor φ hd hm (stripCenterCircle ht ht' 1)}) :
    ∃ g : SL(2,ℤ), g ∈ CongruenceSubgroup.Gamma 2 ∧
      sl2zToPSL2R g • (e : UpperHalfPlane) =
        (lambdaPunctured_isCoveringMap.monodromy
          (.mk (imageCenterLoop ht ht' (scaledCompetitor φ hd hm))) e : UpperHalfPlane) ∧
      2 * Real.arcosh (|(((g : Matrix (Fin 2) (Fin 2) ℤ).trace : ℤ):ℝ)|/2) ≤
        2 * Real.pi^2/Real.log 19 ∧ |(g : Matrix (Fin 2) (Fin 2) ℤ).trace| < 38 := by
  let e' := lambdaPunctured_isCoveringMap.monodromy
    (.mk (imageCenterLoop ht ht' (scaledCompetitor φ hd hm))) e
  obtain ⟨k,hk⟩ := lambdaPunctured_quotientCovering.exists_toPermFiber_eq e e'
  obtain ⟨g,hg,hproj⟩ := k.property
  have hact : sl2zToPSL2R g • (e : UpperHalfPlane) = (e' : UpperHalfPlane) := by
    rw [hproj]
    exact congrArg Subtype.val hk
  exact ⟨g,hg,hact,r19_trace_bound_of_center_monodromy ht ht' hd hm e g hact⟩

end BelgianChocolate.SecondAnnulus

