import FirstAnnulusMonodromyLength
import ModularLambdaCovering
import SecondAnnulusMatrix

/-! The strip lifting and trace step for a loop with a specified actual
modular monodromy. The basepoint of the loop is the true strip center. -/

namespace BelgianChocolate.SecondAnnulus

open Complex Set UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups Manifold
open BelgianChocolate.FirstAnnulus BelgianChocolate.ModularLambdaRatio

private theorem cast_monodromy_coe {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {P : E → X} (hp : IsCoveringMap P) {p : E} {a : X} (e : P p = a) (γ : Path a a) :
    (hp.monodromy (.mk (γ.cast e e)) ⟨p,rfl⟩ : E) = (hp.monodromy (.mk γ) ⟨p,e⟩ : E) := by
  subst a
  rfl

/-- Derive the trace inequality by lifting the annulus map to the actual
upper half-plane covering of the twice-punctured plane. -/
theorem trace_le_of_lambda_center_label {R : ℝ} (hR : 1 < R) (y : ℝ)
    {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b (radialAnnulus R))
    (hbX : MapsTo b (radialAnnulus R) ({0,1}ᶜ : Set ℂ))
    {a : ({0,1}ᶜ : Set ℂ)} (γ : Path a a)
    (hγ : ∀ u : unitInterval, b (Complex.exp (logCenterSegment (Real.log R) y u)) = (γ u : ℂ))
    (e : lambdaPunctured ⁻¹' {a}) (g : SL(2,ℤ))
    (hg : sl2zToPSL2R g • (e : ℍ) =
      (lambdaPunctured_isCoveringMap.monodromy (.mk γ) e : ℍ)) :
    2*Real.arcosh (|(((g : Matrix (Fin 2) (Fin 2) ℤ).trace : ℤ):ℝ)|/2) ≤
      2*Real.pi^2/Real.log R := by
  let X : Set ℂ := {0,1}ᶜ
  let Q : ℂ → ℂ := lambdaRatio ∘ ofComplex
  have hX : IsOpen X :=
    isOpen_compl_iff.mpr ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed
  have hQ (z : ℍ) : Q z = (lambdaPunctured z : ℂ) := by simp [Q,lambdaPunctured]
  have hPmem (z : ℍ) : Q z ∈ X := hQ z ▸ (lambdaPunctured z).2
  have hsub : (fun z : ℍ ↦ (⟨Q z,hPmem z⟩ : X)) = lambdaPunctured :=
    funext fun z ↦ Subtype.ext (hQ z)
  have hcov : IsCoveringMapOn (fun z : ℍ ↦ Q z) X :=
    IsCoveringMapOn.of_isCoveringMap_subtype hX hPmem (hsub ▸ lambdaPunctured_isCoveringMap)
  have hdiff : DifferentiableOn ℂ Q upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp lambdaRatio_mdifferentiable
  have hder (z : ℍ) : DifferentiableAt ℂ Q z ∧ deriv Q z ≠ 0 :=
    ⟨hdiff.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos), lambdaRatio_deriv_ne_zero z⟩
  have hL := Real.log_pos hR
  let S := logStrip (Real.log R)
  let z₀ : S := ⟨⟨Real.log R/2,y⟩, by
    change 0 < Real.log R/2 ∧ Real.log R/2 < Real.log R
    constructor <;> linarith⟩
  have hseg (u : unitInterval) : logCenterSegment (Real.log R) y u ∈ S := by
    change 0 < Real.log R/2 ∧ Real.log R/2 < Real.log R
    constructor <;> linarith
  let p : ℍ := e
  have he : lambdaPunctured p = a := e.2
  have hb₀ : Q p = b (Complex.exp z₀) := by
    have hz : logCenterSegment (Real.log R) y 0 = (z₀ : ℂ) := by simp [z₀,logCenterSegment]
    rw [← hz, hγ, γ.source, hQ, he]
  obtain ⟨F,hF,hFm,hF₀,hFQ⟩ := exists_strip_holomorphicLift hR hcov hder hb hbX z₀ p hb₀
  let A := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g
  have htrace : 2 * Real.arcosh (|(A : Matrix (Fin 2) (Fin 2) ℝ).trace| / 2) ≤
      2 * Real.pi ^ 2 / Real.log R := by
    let γ' := γ.cast he he
    apply logStrip_trace_length_le_of_monodromy hR y hF hFm lambdaPunctured_isCoveringMap p hF₀.symm γ' _ A
    · calc
        A • p = sl2zToPSL2R g • p := by
          rw [sl2zToPSL2R_apply, UpperHalfPlane.pslMk_smul]
        _ = (lambdaPunctured_isCoveringMap.monodromy (.mk γ) e : ℍ) := hg
        _ = (lambdaPunctured_isCoveringMap.monodromy (.mk γ') ⟨p,rfl⟩ : ℍ) :=
          (cast_monodromy_coe lambdaPunctured_isCoveringMap he γ).symm
    · intro u
      apply Subtype.ext
      change (lambdaPunctured (liftCenterSegment hL y hF.continuousOn hFm u) : ℂ) = (γ u : ℂ)
      rw [← hQ]
      exact (hFQ _ (hseg u)).trans (hγ u)
  simpa [A, Matrix.trace_fin_two] using htrace

/-- The R19 length estimate forces the reflection index to be one when
the center loop has the actual three-letter matrix label and the index is odd. -/
theorem r19_one_of_center_label {n : ℤ} (hn : Odd n) (y : ℝ)
    {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b (radialAnnulus 19))
    (hbX : MapsTo b (radialAnnulus 19) ({0,1}ᶜ : Set ℂ))
    {a : ({0,1}ᶜ : Set ℂ)} (γ : Path a a)
    (hγ : ∀ u : unitInterval, b (Complex.exp (logCenterSegment (Real.log 19) y u)) = (γ u : ℂ))
    (e : lambdaPunctured ⁻¹' {a})
    (hg : sl2zToPSL2R (tripleMatrix n) • (e : ℍ) =
      (lambdaPunctured_isCoveringMap.monodromy (.mk γ) e : ℍ)) :
    n = 1 :=
  one_of_odd_and_length_bound hn
    (trace_le_of_lambda_center_label (by norm_num) y hb hbX γ hγ e _ hg)

end BelgianChocolate.SecondAnnulus

