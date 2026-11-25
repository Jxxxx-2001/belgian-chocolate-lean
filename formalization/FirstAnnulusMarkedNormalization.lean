import FirstAnnulusCenterCore
import FirstAnnulusMarkedImage
import ModularLambdaCuspLabels

/-! Identify the actual marked loops using the simple preimages supplied by
the normalized competitor, then apply the first annulus length bound. -/

namespace BelgianChocolate.FirstAnnulus

open Complex Metric Set Topology UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open BelgianChocolate.FirstAnnulusPaths
open BelgianChocolate.ModularLambdaRatio
open scoped MatrixGroups

private theorem markedImage_to_model
    {t ε : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} {p d b c : ℂ} (hp : p = 0 ∨ p = -1)
    (hε : 0 < ε) (hcont : ContinuousOn f (ball p ε))
    (hder : HasDerivAt f d p) (hd : d ≠ 0) {X : Set ℂ}
    (hX : ({f p, b}ᶜ : Set ℂ) = X)
    (F : C(cutDomain t, X)) (hF : ∀ z : cutDomain t, (F z : ℂ) = f (z : ℂ))
    (hc : c ≠ 0) (hcB : ‖c‖ < ‖b - f p‖)
    {v : X} (ψ : Path v v)
    (hψ : ∀ u : unitInterval, (ψ u : ℂ) = f p + c * positiveTurn u) :
    ∃ q : Path (F (basepoint ht)) v,
      ((q.trans ψ).trans q.symm).Homotopic ((tailedCircle ht ht' hp).map F.continuous) := by
  subst X
  let G := BelgianChocolate.translatedCircle hc hcB
  let L := positiveCircleLoop.map G.continuous
  obtain ⟨q, hq⟩ :=
    tailedCircle_image_homotopy ht ht' hp hε hcont hder hd F hF hc hcB
  have hb : v = G 1 := by
    apply Subtype.ext
    have h := hψ 0
    rw [ψ.source] at h
    change (v : ℂ) = f p + c * ((1 : Circle) : ℂ)
    simpa using h
  have hL : L.cast hb hb = ψ := by
    ext u
    change f p + c * ((positiveCircleLoop u : Circle) : ℂ) = (ψ u : ℂ)
    rw [hψ]
    have hturn : (positiveCircleLoop u : ℂ) = positiveTurn u := by
      change Complex.exp ((((2 * Real.pi * (u : ℝ)) : ℝ) : ℂ) * Complex.I) = positiveTurn u
      simp [positiveTurn]
    rw [hturn]
  let q' := q.cast rfl hb
  have hq' : q'.cast rfl hb.symm = q := by ext u; rfl
  refine ⟨q', ?_⟩
  rw [← hL, ← cast_tailed_loop q' L hb, hq']
  exact hq.symm

/-- For the normalized cut-domain competitor, simple preimages at the
two marked points give the actual peripheral labels. The R17 argument then
forces the lower-right entry of the conjugating matrix to have square one. -/
theorem r17_lambda_normalization_of_simple_preimages
    {t ε₀ ε₁ : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (cutDomain t))
    (hm : MapsTo φ (cutDomain t) ({0,1}ᶜ : Set ℂ))
    (hφ₀ : φ 0 = 0) (hφ₁ : φ (-1) = 1)
    (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁)
    (hcont₀ : ContinuousOn φ (ball 0 ε₀)) (hcont₁ : ContinuousOn φ (ball (-1) ε₁))
    {d₀ d₁ : ℂ} (hder₀ : HasDerivAt φ d₀ 0) (hder₁ : HasDerivAt φ d₁ (-1))
    (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) :
    ∃ (e : lambdaPunctured ⁻¹' {cutCompetitor φ hd hm (basepoint ht)})
      (M : SL(2, ℤ)) (hM : M ∈ CongruenceSubgroup.Gamma 2),
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((gammaZero ht ht').map (cutCompetitor φ hd hm).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ zeroDeckLabel e ∧
      lambdaPunctured_isCoveringMap.monodromy
        (.mk ((gammaPlus ht ht').map (cutCompetitor φ hd hm).continuous)) e =
        lambdaPunctured_quotientCovering.toPermFiber _ (conjugateOneDeckLabel M hM) e ∧
      (M 1 1)^2 = 1 ∧ ∃ k : ℤ,
        translate k * zeroGenerator * (translate k)⁻¹ = zeroGenerator ∧
        translate k * (M*oneGenerator*M⁻¹) * (translate k)⁻¹ = oneGenerator := by
  let F := cutCompetitor φ hd hm
  obtain ⟨Y, hY⟩ := tailed_positiveCircles_peripheralLabels
  let τ : UpperHalfPlane := ⟨⟨0, max Y 1⟩, zero_lt_one.trans_le (le_max_right Y 1)⟩
  have hτ : Y ≤ τ.im := le_max_left Y 1
  obtain ⟨h₀, h₁, hzero, hone⟩ := hY τ hτ
  have hF (z : cutDomain t) : (F z : ℂ) = φ z := rfl
  let α := (gammaZero ht ht').map F.continuous
  let β := (gammaPlus ht ht').map F.continuous
  obtain ⟨q₀, hq₀⟩ := markedImage_to_model ht ht' (Or.inl rfl) hε₀ hcont₀ hder₀ hd₀
    (b := 1) (c := lambdaRatio τ) (by rw [hφ₀]) F hF (lambdaRatio_ne_zero τ)
    (by simpa [hφ₀] using h₀) (positiveZeroCircle (lambdaPunctured τ) h₀)
    (by intro u; change lambdaRatio τ * positiveTurn u = _; rw [hφ₀, zero_add])
  obtain ⟨q₁, hq₁⟩ := markedImage_to_model ht ht' (Or.inr rfl) hε₁ hcont₁ hder₁ hd₁
    (b := 0) (c := lambdaRatio (ModularGroup.S • τ) - 1)
    (by ext z; simp [hφ₁, or_comm]) F hF (sub_ne_zero.mpr (lambdaRatio_ne_one _))
    (by rw [hφ₁, norm_sub_rev]; simpa using h₁)
    (positiveOneCircle (lambdaPunctured (ModularGroup.S • τ)) h₁)
    (by
      intro u
      have h' : ‖1 - (lambdaPunctured (ModularGroup.S • τ) : ℂ)‖ < 1 := h₁
      exact (positiveOneCircle_coe (lambdaPunctured (ModularGroup.S • τ)) h' u).trans (by
        change 1 + (lambdaRatio (ModularGroup.S • τ) - 1) * positiveTurn u = _
        rw [hφ₁]))
  have hz : HasPeripheralLabel α zeroCuspDeck := hzero q₀ α hq₀
  have ho : HasPeripheralLabel β oneCuspDeck := hone q₁ β hq₁
  obtain ⟨e, k, he₀, he₁, _⟩ := peripheral_pair_at_common_lift α β hz ho
  obtain ⟨M, hM, hproj⟩ := k.property
  have heq₀ : zeroCuspDeck = zeroDeckLabel := rfl
  have heq₁ : k * oneCuspDeck * k⁻¹ = conjugateOneDeckLabel M hM := by
    apply Subtype.ext
    change (k : PSL(2, ℝ)) * sl2zToPSL2R oneGenerator * (k : PSL(2, ℝ))⁻¹ =
      sl2zToPSL2R (M * oneGenerator * M⁻¹)
    rw [← hproj]
    simp only [map_mul, map_inv]
  rw [heq₀] at he₀
  rw [heq₁] at he₁
  exact ⟨e, M, hM, he₀, he₁,
    r17_lambda_normalization_of_peripheral_labels ht ht' hd hm e M hM he₀ he₁⟩

end BelgianChocolate.FirstAnnulus

