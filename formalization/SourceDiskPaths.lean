import FirstAnnulusPaths

namespace BelgianChocolate.SourceDiskPaths

open Complex Metric Set unitInterval
open BelgianChocolate.FirstAnnulusPaths (cutDomain base foot scale)

/-- The full scaled disk retains all three punctures. -/
def scaledDisk (t : ℝ) : Set ℂ :=
  {s | ‖s‖ < 1 / t ∧ s ≠ 0 ∧ s ≠ -1 ∧ s ≠ 1}

/-- The physical source disk, with the three prescribed preimages removed. -/
def sourceDisk (t : ℝ) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ z ≠ 0 ∧ z ≠ (t : ℂ) * Complex.I ∧ z ≠ -(t : ℂ) * Complex.I}

theorem cut_subset_scaledDisk (t : ℝ) : cutDomain t ⊆ scaledDisk t := by
  rintro s ⟨hn, hcut, hzero, hneg⟩
  refine ⟨hn, hzero, hneg, ?_⟩
  intro h
  subst s
  exact hcut ⟨by simp, by simp, by simpa using hn⟩

noncomputable def cutInclusion (t : ℝ) : C(cutDomain t, scaledDisk t) :=
  ⟨fun s => ⟨s, cut_subset_scaledDisk t s.property⟩,
    Continuous.subtype_mk continuous_subtype_val _⟩

noncomputable def scaledBasepoint {t : ℝ} (ht : 0 < t) (_ht' : t ≤ 1 / 10) :
    scaledDisk t :=
  cutInclusion t (FirstAnnulusPaths.basepoint ht)

noncomputable def scaledGammaZero {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (scaledBasepoint ht ht') (scaledBasepoint ht ht') :=
  (FirstAnnulusPaths.gammaZero ht ht').map (cutInclusion t).continuous

noncomputable def scaledGammaPlus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (scaledBasepoint ht ht') (scaledBasepoint ht ht') :=
  (FirstAnnulusPaths.gammaPlus ht ht').map (cutInclusion t).continuous

theorem scaled_pairWord {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (FirstAnnulusPaths.pairWord ht ht').map (cutInclusion t).continuous =
      (scaledGammaZero ht ht').trans (scaledGammaPlus ht ht') := by
  exact Path.map_trans _ _ _

theorem mem_scaledDisk_of_im_ne_zero {t : ℝ} {s : ℂ} (hn : ‖s‖ < 1 / t)
    (hi : s.im ≠ 0) : s ∈ scaledDisk t := by
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro h; exact hi (by rw [h, Complex.zero_im])
  · intro h; exact hi (by rw [h, Complex.neg_im, Complex.one_im, neg_zero])
  · intro h; exact hi (by rw [h, Complex.one_im])

private theorem radius_ge_ten {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    10 ≤ 1 / t := (le_div_iff₀ ht).2 (by linarith)

private theorem base_im {t : ℝ} (ht : 0 < t) : (base t).im < 0 := by
  have hp : 0 < 1 / (2 * t) := one_div_pos.mpr (by positivity)
  simpa [base, Complex.mul_im] using (neg_lt_zero.mpr hp)

private theorem foot_one_im : (foot 1).im < 0 := by
  norm_num [foot, Complex.mul_im]

private theorem foot_one_norm : ‖foot 1‖ ≤ 6 / 5 := by
  have h := norm_sub_le (1 : ℂ) (((1 / 5 : ℝ) : ℂ) * Complex.I)
  norm_num [foot, norm_mul, norm_div] at h ⊢
  exact h

theorem foot_one_mem {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    foot 1 ∈ scaledDisk t :=
  mem_scaledDisk_of_im_ne_zero (by linarith [foot_one_norm, radius_ge_ten ht ht']) foot_one_im.ne

theorem minus_tail_mem {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) (u : I) :
    AffineMap.lineMap (base t) (foot 1) (u : ℝ) ∈ scaledDisk t ∧
      (AffineMap.lineMap (base t) (foot 1) (u : ℝ)).im < 0 := by
  have hn : AffineMap.lineMap (base t) (foot 1) (u : ℝ) ∈ ball (0 : ℂ) (1 / t) :=
    (convex_ball _ _).lineMap_mem (mem_ball_zero_iff.mpr (FirstAnnulusPaths.base_mem ht).1)
      (mem_ball_zero_iff.mpr (foot_one_mem ht ht').1) u.property
  have hi : (AffineMap.lineMap (base t) (foot 1) (u : ℝ)).im < 0 := by
    rw [AffineMap.lineMap_apply_module]
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    have h₀ := mul_nonpos_of_nonneg_of_nonpos u.property.1 foot_one_im.le
    rcases eq_or_lt_of_le u.property.2 with he | he
    · rw [he]
      simpa using foot_one_im
    · have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr he) (base_im ht)
      linarith
  exact ⟨mem_scaledDisk_of_im_ne_zero (mem_ball_zero_iff.mp hn) hi.ne, hi⟩

/-- All three marked circles, including their smaller concentric circles,
stay in the full punctured disk. -/
theorem scaled_circle_mem {t r : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p s : ℂ} (hp : p = 0 ∨ p = -1 ∨ p = 1) (hr : 0 < r) (hr' : r ≤ 1 / 5)
    (hs : s ∈ sphere p r) : s ∈ scaledDisk t := by
  have hd : ‖s - p‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hs
  have hnp : ‖p‖ ≤ 1 := by rcases hp with rfl | rfl | rfl <;> norm_num
  have hnorm : ‖s‖ ≤ 6 / 5 := by
    have hb := norm_add_le (s - p) p
    rw [sub_add_cancel, hd] at hb
    linarith
  refine ⟨by linarith [radius_ge_ten ht ht'], ?_, ?_, ?_⟩
  · intro h
    rw [h] at hd
    rcases hp with rfl | rfl | rfl <;> norm_num at hd <;> linarith
  · intro h
    rw [h] at hd
    rcases hp with rfl | rfl | rfl <;> norm_num at hd <;> linarith
  · intro h
    rw [h] at hd
    rcases hp with rfl | rfl | rfl <;> norm_num at hd <;> linarith

noncomputable def minusFootpoint {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) : scaledDisk t :=
  ⟨foot 1, foot_one_mem ht ht'⟩

noncomputable def minusTail {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (scaledBasepoint ht ht') (minusFootpoint ht ht') where
  toFun u := ⟨AffineMap.lineMap (base t) (foot 1) (u : ℝ), (minus_tail_mem ht ht' u).1⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  source' := by apply Subtype.ext; simp [scaledBasepoint, cutInclusion, FirstAnnulusPaths.basepoint]
  target' := by apply Subtype.ext; simp [minusFootpoint]

noncomputable def minusRound {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (minusFootpoint ht ht') (minusFootpoint ht ht') where
  toFun u := ⟨circleMap 1 (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * (u : ℝ)),
    scaled_circle_mem ht ht' (Or.inr (Or.inr rfl)) (by norm_num) le_rfl
      (circleMap_mem_sphere 1 (by norm_num) _)⟩
  continuous_toFun := Continuous.subtype_mk (by unfold circleMap; fun_prop) _
  source' := by
    apply Subtype.ext
    change circleMap 1 (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * 0) = foot 1
    rw [mul_zero, add_zero, ← neg_div, circleMap_neg_pi_div_two]
    rfl
  target' := by
    apply Subtype.ext
    change circleMap 1 (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * 1) = foot 1
    rw [mul_one, periodic_circleMap, ← neg_div, circleMap_neg_pi_div_two]
    rfl

noncomputable def scaledGammaMinus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (scaledBasepoint ht ht') (scaledBasepoint ht ht') :=
  ((minusTail ht ht').trans (minusRound ht ht')).trans (minusTail ht ht').symm

/-- The three positively oriented marked loops in manuscript execution order. -/
noncomputable def scaledTripleWord {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (scaledBasepoint ht ht') (scaledBasepoint ht ht') :=
  ((scaledGammaMinus ht ht').trans (scaledGammaZero ht ht')).trans (scaledGammaPlus ht ht')

/-- Inverse to the scaled coordinate (s=iz/t). -/
noncomputable def unscale (t : ℝ) (s : ℂ) : ℂ := -(t : ℂ) * Complex.I * s

theorem scale_eq_mul (t : ℝ) (z : ℂ) :
    scale t z = (Complex.I / (t : ℂ)) * z := by
  unfold scale
  ring

theorem unscale_eq_mul (t : ℝ) (s : ℂ) :
    unscale t s = (-(t : ℂ) * Complex.I) * s := rfl

theorem scale_unscale {t : ℝ} (ht : 0 < t) (s : ℂ) : scale t (unscale t s) = s := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold scale unscale
  rw [show Complex.I * (-(t : ℂ) * Complex.I * s) =
    -((t : ℂ) * s) * (Complex.I * Complex.I) by ring, Complex.I_mul_I]
  field_simp

theorem unscale_scale {t : ℝ} (ht : 0 < t) (z : ℂ) : unscale t (scale t z) = z := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [scale_eq_mul, unscale_eq_mul]
  calc
    _ = -((t : ℂ) * z) * (Complex.I * Complex.I) / (t : ℂ) := by ring
    _ = z := by rw [Complex.I_mul_I]; field_simp

@[simp] theorem scale_zero (t : ℝ) : scale t 0 = 0 := by simp [scale]

theorem scale_lower {t : ℝ} (ht : 0 < t) : scale t (-(t : ℂ) * Complex.I) = 1 := by
  rw [neg_mul, scale_eq_mul, mul_neg, ← scale_eq_mul, FirstAnnulusPaths.scale_upper ht, neg_neg]

theorem norm_scale {t : ℝ} (ht : 0 < t) (z : ℂ) : ‖scale t z‖ = ‖z‖ / t := by
  simp [scale, abs_of_pos ht]

theorem norm_unscale {t : ℝ} (ht : 0 < t) (s : ℂ) : ‖unscale t s‖ = t * ‖s‖ := by
  simp [unscale, abs_of_pos ht]

theorem scale_mapsTo {t : ℝ} (ht : 0 < t) : MapsTo (scale t) (sourceDisk t) (scaledDisk t) := by
  rintro z ⟨hn, h0, hU, hL⟩
  have hi : Function.Injective (scale t) :=
    Function.LeftInverse.injective (unscale_scale ht)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_scale ht]
    exact div_lt_div_of_pos_right hn ht
  · rw [← scale_zero t]; exact fun h => h0 (hi h)
  · rw [← FirstAnnulusPaths.scale_upper ht]; exact fun h => hU (hi h)
  · rw [← scale_lower ht]; exact fun h => hL (hi h)

theorem unscale_mapsTo {t : ℝ} (ht : 0 < t) : MapsTo (unscale t) (scaledDisk t) (sourceDisk t) := by
  rintro s ⟨hn, h0, hU, hL⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_unscale ht, mul_comm]
    exact (lt_div_iff₀ ht).mp hn
  · intro h
    have hs := congrArg (scale t) h
    rw [scale_unscale ht, scale_zero] at hs
    exact h0 hs
  · intro h
    have hs := congrArg (scale t) h
    rw [scale_unscale ht, FirstAnnulusPaths.scale_upper ht] at hs
    exact hU hs
  · intro h
    have hs := congrArg (scale t) h
    rw [scale_unscale ht, scale_lower ht] at hs
    exact hL hs

noncomputable def scaleHomeomorph {t : ℝ} (ht : 0 < t) : sourceDisk t ≃ₜ scaledDisk t where
  toFun z := ⟨scale t z, scale_mapsTo ht z.property⟩
  invFun s := ⟨unscale t s, unscale_mapsTo ht s.property⟩
  left_inv z := Subtype.ext (unscale_scale ht z)
  right_inv s := Subtype.ext (scale_unscale ht s)
  continuous_toFun := Continuous.subtype_mk (by unfold scale; fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by unfold unscale; fun_prop) _

theorem scaleHomeomorph_apply {t : ℝ} (ht : 0 < t) (z : sourceDisk t) :
    (scaleHomeomorph ht z : ℂ) = scale t z := rfl

theorem scaleHomeomorph_symm_apply {t : ℝ} (ht : 0 < t) (s : scaledDisk t) :
    ((scaleHomeomorph ht).symm s : ℂ) = unscale t s := rfl

noncomputable def sourceBasepoint {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) : sourceDisk t :=
  (scaleHomeomorph ht).symm (scaledBasepoint ht ht')

theorem sourceBasepoint_coe {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (sourceBasepoint ht ht' : ℂ) = -1 / 2 := by
  change unscale t (base t) = -1 / 2
  rw [← FirstAnnulusPaths.scale_base t, unscale_scale ht]

noncomputable def sourceGammaZero {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (sourceBasepoint ht ht') (sourceBasepoint ht ht') :=
  (scaledGammaZero ht ht').map (scaleHomeomorph ht).symm.continuous

noncomputable def sourceGammaPlus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (sourceBasepoint ht ht') (sourceBasepoint ht ht') :=
  (scaledGammaPlus ht ht').map (scaleHomeomorph ht).symm.continuous

noncomputable def sourceGammaMinus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (sourceBasepoint ht ht') (sourceBasepoint ht ht') :=
  (scaledGammaMinus ht ht').map (scaleHomeomorph ht).symm.continuous

noncomputable def sourceTripleWord {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (sourceBasepoint ht ht') (sourceBasepoint ht ht') :=
  ((sourceGammaMinus ht ht').trans (sourceGammaZero ht ht')).trans (sourceGammaPlus ht ht')

theorem source_tripleWord {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (scaledTripleWord ht ht').map (scaleHomeomorph ht).symm.continuous = sourceTripleWord ht ht' := by
  simp only [scaledTripleWord, sourceTripleWord, sourceGammaMinus, sourceGammaZero,
    sourceGammaPlus, Path.map_trans]
  rfl

theorem unscale_lineMap {t : ℝ} (ht : 0 < t) (a b : ℂ) (u : ℝ) :
    unscale t (AffineMap.lineMap a b u) =
      AffineMap.lineMap (unscale t a) (unscale t b) u := by
  apply Function.LeftInverse.injective (unscale_scale ht)
  rw [scale_unscale ht, FirstAnnulusPaths.scale_lineMap, scale_unscale ht, scale_unscale ht]

theorem unscale_foot {t : ℝ} (ht : 0 < t) (p : ℂ) :
    unscale t (foot p) = unscale t p - ((t / 5 : ℝ) : ℂ) := by
  apply Function.LeftInverse.injective (unscale_scale ht)
  rw [scale_unscale ht, FirstAnnulusPaths.scale_foot ht, scale_unscale ht]

theorem unscale_circleMap {t : ℝ} (ht : 0 < t) (p : ℂ) (θ : ℝ) :
    unscale t (circleMap p (1 / 5) (-(Real.pi / 2) + θ)) =
      circleMap (unscale t p) (t / 5) (Real.pi + θ) := by
  apply Function.LeftInverse.injective (unscale_scale ht)
  rw [scale_unscale ht, FirstAnnulusPaths.scale_circleMap ht, scale_unscale ht]

@[simp] theorem unscale_zero (t : ℝ) : unscale t 0 = 0 := by simp [unscale]

theorem unscale_neg_one {t : ℝ} (ht : 0 < t) : unscale t (-1) = (t : ℂ) * Complex.I := by
  rw [← FirstAnnulusPaths.scale_upper ht, unscale_scale ht]

theorem unscale_one {t : ℝ} (ht : 0 < t) : unscale t 1 = -(t : ℂ) * Complex.I := by
  rw [← scale_lower ht, unscale_scale ht]

/-- A source loop is made of the prescribed straight tail, a full positive turn,
and the reversed tail. The formula is given in the original (z)-coordinate. -/
def IsDirectedSourceLoop {t : ℝ} {b : sourceDisk t}
    (p : ℂ) (γ : Path b b) : Prop :=
  ∃ (c : sourceDisk t) (tail : Path b c) (round : Path c c),
    (∀ u : I, (tail u : ℂ) = AffineMap.lineMap (-1 / 2 : ℂ) (p - ((t / 5 : ℝ) : ℂ)) (u : ℝ)) ∧
    (∀ u : I, (round u : ℂ) = circleMap p (t / 5) (Real.pi + 2 * Real.pi * (u : ℝ))) ∧
    γ = (tail.trans round).trans tail.symm

private theorem directedSourceLoop_of_scaled {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p : ℂ} {c : scaledDisk t} (tail : Path (scaledBasepoint ht ht') c) (round : Path c c)
    (htail : ∀ u : I, (tail u : ℂ) = AffineMap.lineMap (base t) (foot p) (u : ℝ))
    (hround : ∀ u : I, (round u : ℂ) = circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * (u : ℝ))) :
    IsDirectedSourceLoop (unscale t p)
      (((tail.trans round).trans tail.symm).map (scaleHomeomorph ht).symm.continuous) := by
  let H := (scaleHomeomorph ht).symm
  refine ⟨H c, tail.map H.continuous, round.map H.continuous, ?_, ?_, ?_⟩
  · intro u
    change unscale t (tail u : ℂ) = _
    rw [htail, unscale_lineMap ht, unscale_foot ht, ← FirstAnnulusPaths.scale_base t, unscale_scale ht]
  · intro u
    change unscale t (round u : ℂ) = _
    rw [hround, unscale_circleMap ht]
  · rw [Path.map_trans, Path.map_trans, Path.map_symm]

private theorem directedSourceLoop_of_cut {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p : ℂ} (hp : p = 0 ∨ p = -1) :
    IsDirectedSourceLoop (unscale t p)
      (((FirstAnnulusPaths.tailedCircle ht ht' hp).map (cutInclusion t).continuous).map
        (scaleHomeomorph ht).symm.continuous) := by
  let T := (FirstAnnulusPaths.tail ht ht' hp).map (cutInclusion t).continuous
  let R := (FirstAnnulusPaths.round ht ht' hp).map (cutInclusion t).continuous
  have hmap : (FirstAnnulusPaths.tailedCircle ht ht' hp).map (cutInclusion t).continuous =
      (T.trans R).trans T.symm := by
    simp only [FirstAnnulusPaths.tailedCircle, Path.map_trans, ← Path.map_symm, T, R]
  rw [hmap]
  exact directedSourceLoop_of_scaled ht ht' (p := p) T R (fun _ => rfl) (fun _ => rfl)

theorem sourceGammaZero_directed {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    IsDirectedSourceLoop 0 (sourceGammaZero ht ht') := by
  have h := directedSourceLoop_of_cut ht ht' (p := 0) (Or.inl rfl)
  rw [unscale_zero] at h
  exact h

theorem sourceGammaPlus_directed {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    IsDirectedSourceLoop ((t : ℂ) * Complex.I) (sourceGammaPlus ht ht') := by
  have h := directedSourceLoop_of_cut ht ht' (p := -1) (Or.inr rfl)
  rw [unscale_neg_one ht] at h
  exact h

theorem sourceGammaMinus_directed {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    IsDirectedSourceLoop (-(t : ℂ) * Complex.I) (sourceGammaMinus ht ht') := by
  have h := directedSourceLoop_of_scaled ht ht' (p := 1) (minusTail ht ht') (minusRound ht ht')
    (fun _ => rfl) (fun _ => rfl)
  rw [unscale_one ht] at h
  exact h

end BelgianChocolate.SourceDiskPaths

