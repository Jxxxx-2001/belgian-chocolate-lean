import FirstAnnulusCoreWord
import FirstAnnulusMonodromyLength
import FirstAnnulusMatrix
import ModularLambdaCovering

/-! Transport from the radius-two marked core to the exponential of the
center line of the logarithmic strip of width `log 17`. -/

namespace BelgianChocolate.FirstAnnulus

open Complex Set unitInterval
open BelgianChocolate.FirstAnnulusPaths

private noncomputable def centerRadiusAt (a : unitInterval) : ℝ :=
  (1-(a:ℝ))*2+(a:ℝ)*Real.sqrt 17

private theorem centerRadius_mem (a : unitInterval) : centerRadiusAt a ∈ Ioo (1:ℝ) 17 := by
  have hs : Real.sqrt 17 ∈ Ioo (1:ℝ) 17 :=
    ⟨Real.lt_sqrt_of_sq_lt (by norm_num), (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)⟩
  exact convex_Ioo (1:ℝ) 17 (show (2:ℝ) ∈ Ioo 1 17 by constructor <;> norm_num)
    hs (sub_nonneg.mpr a.2.2) a.2.1 (by ring)

private theorem centerRadius_circle_mem (a : unitInterval) (ζ : Circle) :
    ((centerRadiusAt a:ℝ):ℂ)*(ζ:ℂ) ∈ annulus17 := by
  have h := centerRadius_mem a
  change ‖_‖ ∈ Ioo (1:ℝ) 17
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one,
    abs_of_pos (zero_lt_one.trans h.1)] using h

private noncomputable def radiusImage {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    C(unitInterval × Circle, cutDomain t) where
  toFun q := ⟨slitDiskInverse (joukowski kappa ((centerRadiusAt q.1 : ℂ)*(q.2 : ℂ))),
    normalized_embedding_mapsTo_cut ht ht' (centerRadius_circle_mem q.1 q.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun q : unitInterval × Circle ↦ (centerRadiusAt q.1 : ℂ)*(q.2 : ℂ)) := by
      unfold centerRadiusAt
      fun_prop
    exact normalized_embedding.1.continuousOn.comp_continuous hc
      (fun q ↦ centerRadius_circle_mem q.1 q.2)

/-- The radius-`√17` circle viewed in the punctured source. -/
noncomputable def stripCenterCircle {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    C(Circle, cutDomain t) where
  toFun ζ := radiusImage ht ht' (1,ζ)
  continuous_toFun := (radiusImage ht ht').continuous.comp (continuous_const.prodMk continuous_id)

/-- Linear interpolation of the radius gives a free homotopy in the full cut domain. -/
noncomputable def coreToStripCenter {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    (coreCircle t ht ht').Homotopy (stripCenterCircle ht ht') where
  toFun := radiusImage ht ht'
  continuous_toFun := (radiusImage ht ht').continuous
  map_zero_left ζ := by
    apply Subtype.ext
    change slitDiskInverse (joukowski kappa ((centerRadiusAt 0 : ℂ)*(ζ:ℂ))) = coreValue ζ
    simp [centerRadiusAt, coreValue]
  map_one_left _ := rfl

/-- Exponentiating the upward center segment gives one positive turn of radius `√17`. -/
theorem exp_logCenterSegment_zero (u : unitInterval) :
    Complex.exp (logCenterSegment (Real.log 17) 0 u) =
      (Real.sqrt 17 : ℂ) * (positiveCircleLoop u : ℂ) := by
  change Complex.exp ⟨Real.log 17/2,0+2*Real.pi*(u:ℝ)⟩ =
    (Real.sqrt 17 : ℂ) * Complex.exp (((2*Real.pi*(u:ℝ):ℝ):ℂ)*Complex.I)
  rw [zero_add, Complex.mk_eq_add_mul_I, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_half,
    Real.exp_log (by norm_num : (0:ℝ)<17)]

/-- This pointwise formula connects the loop used by covering transport to the
actual projected exponential strip segment used by the length estimate. -/
theorem stripCenterCircle_positiveLoop {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (u : unitInterval) :
    ((positiveCircleLoop.map (stripCenterCircle ht ht').continuous u : cutDomain t):ℂ) =
      slitDiskInverse (joukowski kappa (Complex.exp (logCenterSegment (Real.log 17) 0 u))) := by
  rw [exp_logCenterSegment_zero]
  change slitDiskInverse (joukowski kappa ((centerRadiusAt 1 : ℂ)*(positiveCircleLoop u:ℂ))) = _
  simp [centerRadiusAt]

private theorem rebase_tailed_loop {X : Type*} [TopologicalSpace X] {b c d : X}
    (q : Path b d) (loop : Path c c) (e : d = c) :
    let q' := q.cast rfl e.symm
    ((q'.trans loop).trans q'.symm) = ((q.trans (loop.cast e e)).trans q.symm) := by
  subst d
  rfl

open Path.Homotopic.Quotient in
/-- The strip center loop carries the marked product in its prescribed positive order. -/
theorem stripCenter_pairWord {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    let γ := positiveCircleLoop.map (stripCenterCircle ht ht').continuous
    ∃ q : Path (basepoint ht) (stripCenterCircle ht ht' 1),
      ((q.trans γ).trans q.symm).Homotopic (pairWord ht ht') := by
  let core := positiveCircleLoop.map (coreCircle t ht ht').continuous
  let γ := positiveCircleLoop.map (stripCenterCircle ht ht').continuous
  let H := coreToStripCenter ht ht'
  let r := H.evalAt 1
  obtain ⟨p,hp⟩ := firstAnnulus_core_pairWord ht ht'
  let p' := p.cast rfl core.source.symm
  have hp' : ((p'.trans core).trans p'.symm).Homotopic (pairWord ht ht') := by
    rw [rebase_tailed_loop p core core.source]
    exact hp
  have hr : ((r.trans γ).trans r.symm).Homotopic core :=
    FirstAnnulusTransport.free_homotopy_tailed_homotopy H positiveCircleLoop
  refine ⟨p'.trans r, ?_⟩
  apply Path.Homotopic.Quotient.eq.mp
  rw [← Path.Homotopic.Quotient.eq.mpr hp']
  have he := Path.Homotopic.Quotient.eq.mpr hr
  simp only [Path.trans_symm, mk_trans, mk_symm, trans_assoc] at he ⊢
  rw [← he]
  simp only [trans_assoc]
  rfl

/-- Covering transport along the projected center segment equals transport
along the two positive marked loops after transport along the source tail. -/
theorem stripCenter_monodromy_pairWord {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {p : E → X} (hp : IsCoveringMap p) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    (f : C(cutDomain t,X)) (e : p ⁻¹' {f (basepoint ht)}) :
    let γ := positiveCircleLoop.map (stripCenterCircle ht ht').continuous
    ∃ q : Path (basepoint ht) (stripCenterCircle ht ht' 1),
      hp.monodromy (.mk (γ.map f.continuous)) (hp.monodromy (.mk (q.map f.continuous)) e) =
        hp.monodromy (.mk (q.map f.continuous))
          (hp.monodromy (.mk ((gammaPlus ht ht').map f.continuous))
            (hp.monodromy (.mk ((gammaZero ht ht').map f.continuous)) e)) := by
  obtain ⟨q,hq⟩ := stripCenter_pairWord ht ht'
  exact ⟨q, FirstAnnulusTransport.monodromy_mapped_core_of_tailed_homotopy
    hp f q _ (gammaZero ht ht') (gammaPlus ht ht') hq e⟩



open Complex Set unitInterval
open scoped MatrixGroups
open BelgianChocolate.FirstAnnulusPaths

/-- A competitor in the normalized, slit source coordinates, regarded as a
continuous map into the chosen range of the covering. -/
noncomputable def cutCompetitor {t : ℝ} {X : Set ℂ} (φ : ℂ → ℂ)
    (hd : DifferentiableOn ℂ φ (cutDomain t)) (hm : MapsTo φ (cutDomain t) X) :
    C(cutDomain t, X) where
  toFun z := ⟨φ z,hm z.property⟩
  continuous_toFun := hd.continuousOn.domRestrict.subtype_mk _

/-- The two marked labels are based at the same lift. Their ordered product
acts on the lift reached by following the tail to the true strip center. -/
theorem stripCenter_deck_product {X E G : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [Group G] [MulAction G E] {P : E → X} (hp : IsQuotientCoveringMap P G)
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (f : C(cutDomain t, X))
    (e : P ⁻¹' {f (basepoint ht)}) (g₀ gPlus : G)
    (h₀ : hp.isCoveringMap.monodromy (.mk ((gammaZero ht ht').map f.continuous)) e =
      hp.toPermFiber _ g₀ e)
    (hPlus : hp.isCoveringMap.monodromy (.mk ((gammaPlus ht ht').map f.continuous)) e =
      hp.toPermFiber _ gPlus e) :
    let γ := positiveCircleLoop.map (stripCenterCircle ht ht').continuous
    ∃ q : Path (basepoint ht) (stripCenterCircle ht ht' 1),
      let e' := hp.isCoveringMap.monodromy (.mk (q.map f.continuous)) e
      hp.isCoveringMap.monodromy (.mk (γ.map f.continuous)) e' =
        hp.toPermFiber _ (g₀*gPlus) e' := by
  obtain ⟨q,hq⟩ := stripCenter_monodromy_pairWord hp.isCoveringMap ht ht' f e
  refine ⟨q, ?_⟩
  dsimp only
  rw [hq, ← FirstAnnulusTransport.transport_trans hp.isCoveringMap
    ((gammaZero ht ht').map f.continuous) ((gammaPlus ht ht').map f.continuous) e,
    FirstAnnulusTransport.deck_labels_trans hp _ _ e g₀ gPlus h₀ hPlus, hp.monodromy_toPermFiber]

private theorem cast_monodromy_coe {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {P : E → X} (hp : IsCoveringMap P) {p : E} {a : X} (e : P p = a) (γ : Path a a) :
    (hp.monodromy (.mk (γ.cast e e)) ⟨p,rfl⟩ : E) = (hp.monodromy (.mk γ) ⟨p,e⟩ : E) := by
  subst a
  rfl

/-- The radius-17 trace bound for the product of the two marked source labels.
The strip lift, its positive center loop and its endpoint are constructed from
the competitor and the covering. -/
theorem r17_trace_le_of_marked_labels {X : Set ℂ} (hX : IsOpen X)
    {G : Type*} [Group G] [MulAction G UpperHalfPlane]
    {P : UpperHalfPlane → X} (hp : IsQuotientCoveringMap P G)
    {Q : ℂ → ℂ} (hQ : ∀ z : UpperHalfPlane, Q z = (P z : ℂ))
    (hder : ∀ z : UpperHalfPlane, DifferentiableAt ℂ Q z ∧ deriv Q z ≠ 0)
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (cutDomain t)) (hm : MapsTo φ (cutDomain t) X)
    (e : P ⁻¹' {cutCompetitor φ hd hm (basepoint ht)}) (g₀ gPlus : G)
    (h₀ : hp.isCoveringMap.monodromy (.mk ((gammaZero ht ht').map (cutCompetitor φ hd hm).continuous)) e =
      hp.toPermFiber _ g₀ e)
    (hPlus : hp.isCoveringMap.monodromy (.mk ((gammaPlus ht ht').map (cutCompetitor φ hd hm).continuous)) e =
      hp.toPermFiber _ gPlus e)
    (g : SL(2,ℝ)) (hg : ∀ p : UpperHalfPlane, g • p = (g₀*gPlus) • p) :
    2*Real.arcosh (|(g : Matrix (Fin 2) (Fin 2) ℝ).trace|/2) ≤ 2*Real.pi^2/Real.log 17 := by
  let f := cutCompetitor φ hd hm
  let γ := positiveCircleLoop.map (stripCenterCircle ht ht').continuous
  let δ := γ.map f.continuous
  obtain ⟨q,hq⟩ := stripCenter_deck_product hp ht ht' f e g₀ gPlus h₀ hPlus
  let e' := hp.isCoveringMap.monodromy (.mk (q.map f.continuous)) e
  let p : UpperHalfPlane := e'.1
  have he : P p = f (stripCenterCircle ht ht' 1) := e'.2
  have hprod : hp.isCoveringMap.monodromy (.mk δ) e' = hp.toPermFiber _ (g₀*gPlus) e' := hq
  let b := φ ∘ (slitDiskInverse ∘ joukowski kappa)
  have hb : DifferentiableOn ℂ b (radialAnnulus 17) := hd.comp normalized_embedding.1
    (normalized_embedding_mapsTo_cut ht ht')
  have hbX : MapsTo b (radialAnnulus 17) X := hm.comp (normalized_embedding_mapsTo_cut ht ht')
  have hPmem (z : UpperHalfPlane) : Q z ∈ X := hQ z ▸ (P z).2
  have hsub : (fun z : UpperHalfPlane ↦ (⟨Q z,hPmem z⟩ : X)) = P :=
    funext fun z ↦ Subtype.ext (hQ z)
  have hcov : IsCoveringMapOn (fun z : UpperHalfPlane ↦ Q z) X :=
    IsCoveringMapOn.of_isCoveringMap_subtype hX hPmem (hsub ▸ hp.isCoveringMap)
  have h17 : (1:ℝ) < 17 := by norm_num
  have hL := Real.log_pos h17
  let S := logStrip (Real.log 17)
  let z₀ : S := ⟨⟨Real.log 17/2,0⟩, by
    change 0 < Real.log 17/2 ∧ Real.log 17/2 < Real.log 17
    constructor <;> linarith⟩
  have hseg (u : unitInterval) : logCenterSegment (Real.log 17) 0 u ∈ S := by
    change 0 < Real.log 17/2 ∧ Real.log 17/2 < Real.log 17
    constructor <;> linarith
  have hat (u : unitInterval) : b (Complex.exp (logCenterSegment (Real.log 17) 0 u)) = (δ u : ℂ) := by
    change φ (slitDiskInverse (joukowski kappa _)) = φ ((γ u : cutDomain t):ℂ)
    rw [show (γ u : ℂ) = _ from stripCenterCircle_positiveLoop ht ht' u]
  have hb₀ : Q p = b (Complex.exp z₀) := by
    have hz : logCenterSegment (Real.log 17) 0 0 = (z₀ : ℂ) := by simp [z₀,logCenterSegment]
    rw [← hz, hat, δ.source, hQ, he]
  obtain ⟨F,hF,hFm,hF₀,hFQ⟩ := exists_strip_holomorphicLift h17 hcov hder hb hbX z₀ p hb₀
  let δ' := δ.cast he he
  apply logStrip_trace_length_le_of_monodromy h17 0 hF hFm hp.isCoveringMap p hF₀.symm δ' _ g
  · calc
      g • p = (g₀*gPlus) • p := hg p
      _ = (hp.isCoveringMap.monodromy (.mk δ) e' : UpperHalfPlane) := by
        rw [hprod]; rfl
      _ = (hp.isCoveringMap.monodromy (.mk δ') ⟨p,rfl⟩ : UpperHalfPlane) :=
        (cast_monodromy_coe hp.isCoveringMap he δ).symm
  · intro u
    apply Subtype.ext
    change (P (liftCenterSegment hL 0 hF.continuousOn hFm u) : ℂ) = (δ u : ℂ)
    rw [← hQ]
    exact (hFQ _ (hseg u)).trans (hat u)



open Set UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups Manifold
open BelgianChocolate.FirstAnnulusPaths BelgianChocolate.ModularLambdaRatio

/-- For the actual modular lambda covering, verify the two marked labels at a
single starting lift. Any integral representative of their product then obeys
the sharp strip-center trace bound. -/
theorem r17_lambda_trace_le_of_marked_labels
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (cutDomain t))
    (hm : MapsTo φ (cutDomain t) ({0,1}ᶜ : Set ℂ))
    (e : lambdaPunctured ⁻¹' {cutCompetitor φ hd hm (basepoint ht)})
    (g₀ gPlus : gammaTwoProjective)
    (h₀ : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((gammaZero ht ht').map (cutCompetitor φ hd hm).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ g₀ e)
    (hPlus : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((gammaPlus ht ht').map (cutCompetitor φ hd hm).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ gPlus e)
    (g : SL(2,ℤ)) (hg : sl2zToPSL2R g = ((g₀*gPlus : gammaTwoProjective) : PSL(2,ℝ))) :
    2*Real.arcosh (|(((g : Matrix (Fin 2) (Fin 2) ℤ).trace : ℤ):ℝ)|/2) ≤
      2*Real.pi^2/Real.log 17 := by
  let A := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g
  have ha (p : UpperHalfPlane) : A • p = (g₀*gPlus) • p := by
    change A • p = (((g₀*gPlus : gammaTwoProjective):PSL(2,ℝ))) • p
    rw [← hg, sl2zToPSL2R_apply, UpperHalfPlane.pslMk_smul]
  have hdiff : DifferentiableOn ℂ (lambdaRatio ∘ ofComplex) upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp lambdaRatio_mdifferentiable
  have hl := r17_trace_le_of_marked_labels (X := ({0,1}ᶜ : Set ℂ))
    (Q := lambdaRatio ∘ ofComplex) (isOpen_compl_iff.mpr ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed)
    lambdaPunctured_quotientCovering (fun z ↦ by simp [lambdaPunctured])
    (fun z ↦ ⟨hdiff.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos),
      lambdaRatio_deriv_ne_zero z⟩) ht ht' hd hm e g₀ gPlus h₀ hPlus A ha
  simpa [A, Matrix.trace_fin_two] using hl


open Set UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups Manifold
open BelgianChocolate.FirstAnnulusPaths BelgianChocolate.ModularLambdaRatio

/-- The actual level-two matrix, interpreted as a deck transformation of lambda. -/
def congruenceLabel (M : SL(2,ℤ)) (hM : M ∈ CongruenceSubgroup.Gamma 2) : gammaTwoProjective :=
  ⟨sl2zToPSL2R M,M,hM,rfl⟩

private theorem zeroGenerator_level_two : zeroGenerator ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [zeroGenerator, Matrix.cons_val_zero, Matrix.cons_val_one]
  decide

private theorem oneGenerator_level_two : oneGenerator ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [oneGenerator, Matrix.cons_val_zero, Matrix.cons_val_one]
  decide

private theorem conjugatedOne_level_two (M : SL(2,ℤ)) (hM : M ∈ CongruenceSubgroup.Gamma 2) :
    M * oneGenerator * M⁻¹ ∈ CongruenceSubgroup.Gamma 2 :=
  (CongruenceSubgroup.Gamma 2).mul_mem ((CongruenceSubgroup.Gamma 2).mul_mem hM oneGenerator_level_two)
    ((CongruenceSubgroup.Gamma 2).inv_mem hM)

/-- The projective label represented by the specified positive zero generator. -/
def zeroDeckLabel : gammaTwoProjective := congruenceLabel zeroGenerator zeroGenerator_level_two

/-- The projective label represented by a level-two conjugate of the positive one generator. -/
def conjugateOneDeckLabel (M : SL(2,ℤ)) (hM : M ∈ CongruenceSubgroup.Gamma 2) :
    gammaTwoProjective := congruenceLabel (M*oneGenerator*M⁻¹) (conjugatedOne_level_two M hM)

/-- The two source peripheral labels are the remaining geometric hypotheses
for this first-annulus normalization. In particular, the trace bound is derived. -/
theorem r17_lambda_normalization_of_peripheral_labels
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (cutDomain t))
    (hm : MapsTo φ (cutDomain t) ({0,1}ᶜ : Set ℂ))
    (e : lambdaPunctured ⁻¹' {cutCompetitor φ hd hm (basepoint ht)})
    (M : SL(2,ℤ)) (hM : M ∈ CongruenceSubgroup.Gamma 2)
    (h₀ : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((gammaZero ht ht').map (cutCompetitor φ hd hm).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ zeroDeckLabel e)
    (hPlus : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((gammaPlus ht ht').map (cutCompetitor φ hd hm).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _
        (conjugateOneDeckLabel M hM) e) :
    (M 1 1)^2 = 1 ∧ ∃ k : ℤ,
      translate k * zeroGenerator * (translate k)⁻¹ = zeroGenerator ∧
      translate k * (M*oneGenerator*M⁻¹) * (translate k)⁻¹ = oneGenerator := by
  have hrep : sl2zToPSL2R (zeroGenerator*M*oneGenerator*M⁻¹) =
      ((zeroDeckLabel *
        conjugateOneDeckLabel M hM : gammaTwoProjective) : PSL(2,ℝ)) := by
    change _ = sl2zToPSL2R zeroGenerator * sl2zToPSL2R (M*oneGenerator*M⁻¹)
    simp only [map_mul, mul_assoc]
  have hb := r17_lambda_trace_le_of_marked_labels ht ht' hd hm e _ _ h₀ hPlus _ hrep
  obtain ⟨_,h01,_,h11⟩ := CongruenceSubgroup.Gamma_mem.mp hM
  have ho : 2 ∣ M 1 1 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by push_cast; rw [h11,sub_self])
  have he : 2 ∣ M 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h01
  have hodd : Odd (M 1 1) := by obtain ⟨k,hk⟩ := ho; exact ⟨k,by omega⟩
  have heven : Even (M 0 1) := by obtain ⟨k,hk⟩ := he; exact ⟨k,by omega⟩
  refine ⟨bottomRight_sq_eq_one_of_trace_bound M hodd ?_,
    exists_normalization_of_length_bound M hodd heven hb⟩
  exact_mod_cast BelgianChocolate.AnnulusLengthArithmetic.abs_trace_lt_thirty_four hb

end BelgianChocolate.FirstAnnulus
