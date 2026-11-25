import SourceDiskCompetitor

/-! Real reflection on the full source disk reverses the actual positive loops. -/

namespace BelgianChocolate.SourceDiskPaths

open Complex Metric Set unitInterval
open scoped ComplexConjugate

private theorem conj_neg_half : conj (-1 / 2 : ℂ) = -1 / 2 := by
  have h : conj (2 : ℂ) = 2 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, map_add, map_one]
  rw [map_div₀, map_neg, map_one, h]

private theorem conj_upper (t : ℝ) :
    conj ((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I := by
  simp [mul_neg, neg_mul]

private theorem conj_lower (t : ℝ) :
    conj (-(t : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
  simp [mul_neg, neg_mul]

theorem conj_mapsTo_sourceDisk (t : ℝ) : MapsTo (conj : ℂ → ℂ) (sourceDisk t) (sourceDisk t) := by
  rintro z ⟨hn, h₀, h₁, h₂⟩
  refine ⟨by simpa only [norm_conj] using hn, ?_, ?_, ?_⟩
  · intro h
    have hh := congrArg conj h
    rw [conj_conj, map_zero] at hh
    exact h₀ hh
  · intro h
    have hh := congrArg conj h
    rw [conj_conj, conj_upper] at hh
    exact h₂ hh
  · intro h
    have hh := congrArg conj h
    rw [conj_conj, conj_lower] at hh
    exact h₁ hh

noncomputable def sourceReflection (t : ℝ) : sourceDisk t ≃ₜ sourceDisk t where
  toFun z := ⟨conj z, conj_mapsTo_sourceDisk t z.property⟩
  invFun z := ⟨conj z, conj_mapsTo_sourceDisk t z.property⟩
  left_inv z := Subtype.ext (conj_conj (z : ℂ))
  right_inv z := Subtype.ext (conj_conj (z : ℂ))
  continuous_toFun := Continuous.subtype_mk (continuous_conj.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (continuous_conj.comp continuous_subtype_val) _

theorem sourceReflection_apply {t : ℝ} (z : sourceDisk t) :
    (sourceReflection t z : ℂ) = conj (z : ℂ) := rfl

theorem sourceReflection_base {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    sourceBasepoint ht ht' = sourceReflection t (sourceBasepoint ht ht') := by
  apply Subtype.ext
  rw [sourceReflection_apply, sourceBasepoint_coe]
  rw [conj_neg_half]

/-- Reflect a source loop without changing its declared basepoint. -/
noncomputable def reflectSourceLoop {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    (γ : Path (sourceBasepoint ht ht') (sourceBasepoint ht ht')) :
    Path (sourceBasepoint ht ht') (sourceBasepoint ht ht') :=
  (γ.map (sourceReflection t).continuous).cast
    (sourceReflection_base ht ht') (sourceReflection_base ht ht')

theorem reflectSourceLoop_apply {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    (γ : Path (sourceBasepoint ht ht') (sourceBasepoint ht ht')) (u : I) :
    (reflectSourceLoop ht ht' γ u : ℂ) = conj (γ u : ℂ) := rfl

private theorem conj_lineMap (a b : ℂ) (u : ℝ) :
    conj (AffineMap.lineMap a b u) = AffineMap.lineMap (conj a) (conj b) u := by
  simp [AffineMap.lineMap_apply_module, Complex.real_smul]

private theorem conj_circleMap_positive (p : ℂ) (r u : ℝ) :
    conj (circleMap p r (Real.pi + 2 * Real.pi * u)) =
      circleMap (conj p) r (Real.pi + 2 * Real.pi * (1 - u)) := by
  rw [conj_circleMap]
  rw [show Real.pi + 2 * Real.pi * (1 - u) =
    -(Real.pi + 2 * Real.pi * u) + 2 * Real.pi + 2 * Real.pi by ring,
    periodic_circleMap, periodic_circleMap]

theorem reflect_directedSourceLoop {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p : ℂ} {γ δ : Path (sourceBasepoint ht ht') (sourceBasepoint ht ht')}
    (hγ : IsDirectedSourceLoop p γ) (hδ : IsDirectedSourceLoop (conj p) δ) :
    (reflectSourceLoop ht ht' γ).Homotopic δ.symm := by
  obtain ⟨a, T, R, hT, hR, rfl⟩ := hγ
  obtain ⟨b, T', R', hT', hR', rfl⟩ := hδ
  let H := sourceReflection t
  have hab : b = H a := by
    apply Subtype.ext
    change (b : ℂ) = conj (a : ℂ)
    have ha : (a : ℂ) = p - ((t / 5 : ℝ) : ℂ) := by simpa using hT 1
    have hb : (b : ℂ) = conj p - ((t / 5 : ℝ) : ℂ) := by simpa using hT' 1
    rw [ha, hb, map_sub, Complex.conj_ofReal]
  let U := (T.map H.continuous).cast (sourceReflection_base ht ht') hab
  let V := (R.map H.continuous).cast hab hab
  have hU : U = T' := by
    apply Path.ext
    funext u
    apply Subtype.ext
    change conj (T u : ℂ) = (T' u : ℂ)
    rw [hT, hT', conj_lineMap, map_sub, Complex.conj_ofReal]
    rw [conj_neg_half]
  have hV : V = R'.symm := by
    apply Path.ext
    funext u
    apply Subtype.ext
    change conj (R u : ℂ) = (R' (unitInterval.symm u) : ℂ)
    rw [hR, hR', unitInterval.coe_symm_eq, conj_circleMap_positive]
  have hcon :
      reflectSourceLoop ht ht' ((T.trans R).trans T.symm) = (U.trans V).trans U.symm := by
    unfold reflectSourceLoop
    rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
    rfl
  rw [hcon, hU, hV, Path.trans_symm, Path.trans_symm, Path.symm_symm]
  apply Path.Homotopic.Quotient.eq.mp
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

theorem sourceReflection_gammaZero {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (reflectSourceLoop ht ht' (sourceGammaZero ht ht')).Homotopic (sourceGammaZero ht ht').symm :=
  reflect_directedSourceLoop ht ht' (sourceGammaZero_directed ht ht')
    (by simpa using sourceGammaZero_directed ht ht')

theorem sourceReflection_gammaPlus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (reflectSourceLoop ht ht' (sourceGammaPlus ht ht')).Homotopic (sourceGammaMinus ht ht').symm :=
  reflect_directedSourceLoop ht ht' (sourceGammaPlus_directed ht ht')
    (by rw [conj_upper]; exact sourceGammaMinus_directed ht ht')

theorem sourceReflection_gammaMinus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (reflectSourceLoop ht ht' (sourceGammaMinus ht ht')).Homotopic (sourceGammaPlus ht ht').symm :=
  reflect_directedSourceLoop ht ht' (sourceGammaMinus_directed ht ht')
    (by rw [conj_lower]; exact sourceGammaPlus_directed ht ht')

theorem unscale_neg_conj (t : ℝ) (s : ℂ) :
    unscale t (-conj s) = conj (unscale t s) := by
  simp [unscale, mul_neg, neg_mul]

theorem normalized_reflection {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hreal : ∀ z ∈ ball (0 : ℂ) 1, f (conj z) = conj (f z)) (s : scaledDisk t) :
    normalized t f (-conj (s : ℂ)) = conj (normalized t f s) := by
  change f (unscale t (-conj (s : ℂ))) = conj (f (unscale t s))
  rw [unscale_neg_conj]
  exact hreal _ (mem_ball_zero_iff.mpr ((unscale_mapsTo ht s.property).1))

theorem reflected_source_image_apply {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hreal : ∀ z ∈ ball (0 : ℂ) 1, f (conj z) = conj (f z))
    (γ : Path (sourceBasepoint ht ht') (sourceBasepoint ht ht')) (u : I) :
    (((reflectSourceLoop ht ht' γ).map (sourceMap hf).continuous) u : ℂ) =
      conj (((γ.map (sourceMap hf).continuous) u : ℂ)) := by
  change f (conj (γ u : ℂ)) = conj (f (γ u : ℂ))
  exact hreal _ (mem_ball_zero_iff.mpr (γ u).property.1)

/-- Transport real source reflection to the scaled coordinate. -/
noncomputable def scaledReflection {t : ℝ} (ht : 0 < t) : scaledDisk t ≃ₜ scaledDisk t :=
  ((scaleHomeomorph ht).symm.trans (sourceReflection t)).trans (scaleHomeomorph ht)

theorem scaledReflection_apply {t : ℝ} (ht : 0 < t) (s : scaledDisk t) :
    (scaledReflection ht s : ℂ) = -conj (s : ℂ) := by
  change FirstAnnulusPaths.scale t (conj (unscale t s)) = -conj (s : ℂ)
  rw [← unscale_neg_conj, scale_unscale ht]

theorem scaledReflection_base {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    scaledBasepoint ht ht' = scaledReflection ht (scaledBasepoint ht ht') := by
  let H := scaleHomeomorph ht
  apply H.symm.injective
  have h := sourceReflection_base ht ht'
  change H.symm (scaledBasepoint ht ht') = H.symm (H (sourceReflection t
    (H.symm (scaledBasepoint ht ht'))))
  rw [H.symm_apply_apply]
  exact h

noncomputable def reflectScaledLoop {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    (γ : Path (scaledBasepoint ht ht') (scaledBasepoint ht ht')) :
    Path (scaledBasepoint ht ht') (scaledBasepoint ht ht') :=
  (γ.map (scaledReflection ht).continuous).cast
    (scaledReflection_base ht ht') (scaledReflection_base ht ht')

theorem reflectScaledLoop_apply {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    (γ : Path (scaledBasepoint ht ht') (scaledBasepoint ht ht')) (u : I) :
    (reflectScaledLoop ht ht' γ u : ℂ) = -conj (γ u : ℂ) :=
  scaledReflection_apply ht (γ u)

theorem reflectScaledLoop_to_source {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    (γ : Path (scaledBasepoint ht ht') (scaledBasepoint ht ht')) :
    (reflectScaledLoop ht ht' γ).map (scaleHomeomorph ht).symm.continuous =
      reflectSourceLoop ht ht' (γ.map (scaleHomeomorph ht).symm.continuous) := by
  apply Path.ext
  funext u
  apply Subtype.ext
  change unscale t (reflectScaledLoop ht ht' γ u : ℂ) = conj (unscale t (γ u : ℂ))
  rw [reflectScaledLoop_apply, unscale_neg_conj]

private theorem homotopic_of_unscaleMap {t : ℝ} (ht : 0 < t) {a b : scaledDisk t}
    {γ δ : Path a b}
    (h : (γ.map (scaleHomeomorph ht).symm.continuous).Homotopic
      (δ.map (scaleHomeomorph ht).symm.continuous)) : γ.Homotopic δ := by
  let H := scaleHomeomorph ht
  let F : C(sourceDisk t, scaledDisk t) := ⟨H, H.continuous⟩
  have hcast := (h.map F).pathCast (H.apply_symm_apply a).symm
    (H.apply_symm_apply b).symm
  have hmap (p : Path a b) :
      ((p.map H.symm.continuous).map F.continuous).cast
        (H.apply_symm_apply a).symm (H.apply_symm_apply b).symm = p := by
    apply Path.ext
    funext u
    exact H.apply_symm_apply (p u)
  rw [hmap γ, hmap δ] at hcast
  exact hcast

theorem scaledReflection_gammaZero {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (reflectScaledLoop ht ht' (scaledGammaZero ht ht')).Homotopic (scaledGammaZero ht ht').symm := by
  apply homotopic_of_unscaleMap ht
  rw [reflectScaledLoop_to_source, ← Path.map_symm]
  exact sourceReflection_gammaZero ht ht'

theorem scaledReflection_gammaPlus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (reflectScaledLoop ht ht' (scaledGammaPlus ht ht')).Homotopic (scaledGammaMinus ht ht').symm := by
  apply homotopic_of_unscaleMap ht
  rw [reflectScaledLoop_to_source, ← Path.map_symm]
  exact sourceReflection_gammaPlus ht ht'

theorem scaledReflection_gammaMinus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (reflectScaledLoop ht ht' (scaledGammaMinus ht ht')).Homotopic (scaledGammaPlus ht ht').symm := by
  apply homotopic_of_unscaleMap ht
  rw [reflectScaledLoop_to_source, ← Path.map_symm]
  exact sourceReflection_gammaMinus ht ht'

theorem reflected_scaled_image_apply {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hreal : ∀ z ∈ ball (0 : ℂ) 1, f (conj z) = conj (f z))
    (γ : Path (scaledBasepoint ht ht') (scaledBasepoint ht ht')) (u : I) :
    (((reflectScaledLoop ht ht' γ).map (normalizedMap ht hf).continuous) u : ℂ) =
      conj (((γ.map (normalizedMap ht hf).continuous) u : ℂ)) := by
  change normalized t f (reflectScaledLoop ht ht' γ u : ℂ) = conj (normalized t f (γ u : ℂ))
  rw [reflectScaledLoop_apply]
  exact normalized_reflection ht hreal (γ u)

theorem reflected_scaled_image_gammaZero {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    ((reflectScaledLoop ht ht' (scaledGammaZero ht ht')).map (normalizedMap ht hf).continuous).Homotopic
      ((scaledGammaZero ht ht').map (normalizedMap ht hf).continuous).symm := by
  rw [Path.map_symm]
  exact (scaledReflection_gammaZero ht ht').map (normalizedMap ht hf)

theorem reflected_scaled_image_gammaPlus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) :
    ((reflectScaledLoop ht ht' (scaledGammaPlus ht ht')).map (normalizedMap ht hf).continuous).Homotopic
      ((scaledGammaMinus ht ht').map (normalizedMap ht hf).continuous).symm := by
  rw [Path.map_symm]
  exact (scaledReflection_gammaPlus ht ht').map (normalizedMap ht hf)

end BelgianChocolate.SourceDiskPaths

