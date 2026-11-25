import ModularLambdaCovering
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic

/-! Positively oriented cusp paths for the modular lambda covering. -/

namespace BelgianChocolate.ModularLambdaRatio

open Complex Set UpperHalfPlane
open scoped MatrixGroups Topology

/-- Horizontal continuation through one positive period of the level-two coordinate. -/
noncomputable def cuspTranslation (τ : UpperHalfPlane) : C(unitInterval, UpperHalfPlane) :=
  ⟨fun u => (2 * (u : ℝ)) +ᵥ τ, by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    simp only [Function.comp_def, UpperHalfPlane.coe_vadd]
    fun_prop⟩

@[simp] theorem cuspTranslation_zero (τ : UpperHalfPlane) : cuspTranslation τ 0 = τ := by
  simp [cuspTranslation]

@[simp] theorem cuspTranslation_one (τ : UpperHalfPlane) :
    cuspTranslation τ 1 = ModularGroup.T ^ (2 : ℕ) • τ := by
  have h := UpperHalfPlane.modular_T_zpow_smul τ (2:ℤ)
  simpa [cuspTranslation] using h.symm

/-- The level-two nome winds through increasing angle `2πu` along the horizontal path. -/
theorem cuspTranslation_q (τ : UpperHalfPlane) (u : unitInterval) :
    Complex.exp (Real.pi * Complex.I * (cuspTranslation τ u : ℂ)) =
      Complex.exp (Real.pi * Complex.I * (τ : ℂ)) *
      Complex.exp (((2 : ℂ) * Real.pi * (u : ℝ)) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  change (Real.pi : ℂ) * Complex.I * (↑((2 * (u : ℝ)) +ᵥ τ : UpperHalfPlane) : ℂ) = _
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem cuspTranslation_lambda (τ : UpperHalfPlane) (u : unitInterval) :
    lambdaRatio (cuspTranslation τ u) =
      UpperHalfPlane.cuspFunction 2 lambdaRatio
        (Complex.exp (Real.pi * Complex.I * (τ : ℂ)) *
          Complex.exp (((2 : ℂ) * Real.pi * (u : ℝ)) * Complex.I)) := by
  rw [← cuspTranslation_q, lambdaCusp_eq_on_q]

private theorem ratio_end (τ : UpperHalfPlane) :
    lambdaRatio (cuspTranslation τ 1) = lambdaRatio τ := by
  rw [cuspTranslation_lambda]
  change UpperHalfPlane.cuspFunction 2 lambdaRatio
    (Complex.exp _ * Complex.exp ((2 * (Real.pi : ℂ) * ((1 : ℝ) : ℂ)) * Complex.I)) = _
  simp [lambdaCusp_eq_on_q]

private theorem continuous_lambdaPunctured : Continuous lambdaPunctured :=
  lambdaRatio_mdifferentiable.continuous.subtype_mk _

/-- The projected positive cusp loop at `0`, as a path in the twice-punctured plane. -/
noncomputable def zeroCuspLoop (τ : UpperHalfPlane) : Path (lambdaPunctured τ) (lambdaPunctured τ) :=
  ⟨(⟨lambdaPunctured, continuous_lambdaPunctured⟩ : C(UpperHalfPlane, _)).comp (cuspTranslation τ),
    by simp, by apply Subtype.ext; exact ratio_end τ⟩

@[simp] theorem zeroCuspLoop_coe (τ : UpperHalfPlane) (u : unitInterval) :
    (zeroCuspLoop τ u : ℂ) = lambdaRatio (cuspTranslation τ u) := rfl

/-- A positive cusp loop around `1` is obtained by `S`-transport of the horizontal lift. -/
noncomputable def cuspOneLift (τ : UpperHalfPlane) : C(unitInterval, UpperHalfPlane) :=
  ⟨fun u => ModularGroup.S • cuspTranslation τ u, by
    exact (continuous_const_smul ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S).toGL)).comp (cuspTranslation τ).continuous⟩

@[simp] theorem cuspOneLift_zero (τ : UpperHalfPlane) :
    cuspOneLift τ 0 = ModularGroup.S • τ := by simp [cuspOneLift]

@[simp] theorem cuspOneLift_one (τ : UpperHalfPlane) :
    cuspOneLift τ 1 = (ModularGroup.S * ModularGroup.T ^ (2:ℕ) * ModularGroup.S⁻¹) •
      (ModularGroup.S • τ) := by
  change ModularGroup.S • (cuspTranslation τ 1) = _
  rw [cuspTranslation_one, mul_smul, inv_smul_smul, mul_smul]

theorem cuspOneLift_lambda (τ : UpperHalfPlane) (u : unitInterval) :
    lambdaRatio (cuspOneLift τ u) = 1 - lambdaRatio (cuspTranslation τ u) :=
  lambdaRatio_S _

noncomputable def oneCuspLoop (τ : UpperHalfPlane) :
    Path (lambdaPunctured (ModularGroup.S • τ)) (lambdaPunctured (ModularGroup.S • τ)) :=
  ⟨(⟨lambdaPunctured, continuous_lambdaPunctured⟩ : C(UpperHalfPlane, _)).comp (cuspOneLift τ),
    by simp, by apply Subtype.ext; change lambdaRatio (cuspOneLift τ 1) = lambdaRatio (ModularGroup.S • τ)
                rw [cuspOneLift_lambda, ratio_end, lambdaRatio_S]⟩

@[simp] theorem oneCuspLoop_coe (τ : UpperHalfPlane) (u : unitInterval) :
    (oneCuspLoop τ u : ℂ) = 1 - lambdaRatio (cuspTranslation τ u) := cuspOneLift_lambda τ u

/-- The path lift of the positive loop at zero ends at the translate by `T²`. -/
theorem zeroCuspLoop_monodromy_of_covering (hcov : IsCoveringMap lambdaPunctured) (τ : UpperHalfPlane) :
    (hcov.monodromy (.mk (zeroCuspLoop τ)) ⟨τ, rfl⟩ : UpperHalfPlane) =
      ModularGroup.T ^ (2:ℕ) • τ := by
  exact (hcov.monodromy_eq_apply_one (Γ := cuspTranslation τ) (γ := zeroCuspLoop τ)
    (e := ⟨τ, rfl⟩) rfl (cuspTranslation_zero τ)).trans (cuspTranslation_one τ)

/-- The positively oriented cusp at one has the conjugate deck element `ST²S⁻¹`. -/
theorem oneCuspLoop_monodromy_of_covering (hcov : IsCoveringMap lambdaPunctured) (τ : UpperHalfPlane) :
    (hcov.monodromy (.mk (oneCuspLoop τ)) ⟨ModularGroup.S • τ, rfl⟩ : UpperHalfPlane) =
      (ModularGroup.S * ModularGroup.T ^ (2:ℕ) * ModularGroup.S⁻¹) •
        (ModularGroup.S • τ) := by
  exact (hcov.monodromy_eq_apply_one (Γ := cuspOneLift τ) (γ := oneCuspLoop τ)
    (e := ⟨ModularGroup.S • τ, rfl⟩) rfl (cuspOneLift_zero τ)).trans (cuspOneLift_one τ)

/-- Monodromy of the actual modular lambda covering on the positive zero cusp loop. -/
theorem zeroCuspLoop_monodromy (τ : UpperHalfPlane) :
    (lambdaPunctured_isCoveringMap.monodromy (.mk (zeroCuspLoop τ)) ⟨τ,rfl⟩ : UpperHalfPlane) =
      ModularGroup.T ^ (2:ℕ) • τ :=
  zeroCuspLoop_monodromy_of_covering lambdaPunctured_isCoveringMap τ

/-- Monodromy of the actual modular lambda covering on the positive one cusp loop. -/
theorem oneCuspLoop_monodromy (τ : UpperHalfPlane) :
    (lambdaPunctured_isCoveringMap.monodromy (.mk (oneCuspLoop τ))
      ⟨ModularGroup.S • τ,rfl⟩ : UpperHalfPlane) =
      (ModularGroup.S * ModularGroup.T ^ (2:ℕ) * ModularGroup.S⁻¹) • (ModularGroup.S • τ) :=
  oneCuspLoop_monodromy_of_covering lambdaPunctured_isCoveringMap τ



open Filter

/-- Level-two cusp coordinate. -/
noncomputable def cuspNome (τ : UpperHalfPlane) : ℂ := Complex.exp (Real.pi * Complex.I * (τ : ℂ))

private theorem continuous_cuspNome : Continuous cuspNome := by
  unfold cuspNome
  fun_prop

private theorem cuspNome_ne_zero (τ : UpperHalfPlane) : cuspNome τ ≠ 0 := Complex.exp_ne_zero _

private theorem nome_tendsto_zero : Tendsto cuspNome atImInfty (𝓝 0) := by
  have h := UpperHalfPlane.qParam_tendsto_atImInfty (h := 2) (by norm_num)
  refine h.congr fun τ => ?_
  unfold Function.Periodic.qParam cuspNome
  congr 1
  push_cast
  ring

private theorem exists_cusp_height :
    ∃ Y : ℝ, ∀ τ : UpperHalfPlane, Y ≤ τ.im →
      ‖lambdaRatio τ / cuspNome τ - 16‖ < 1 ∧ ‖cuspNome τ‖ < 1/20 := by
  have hratio := lambdaRatio_div_q_tendsto.eventually (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ)<1))
  have hq := nome_tendsto_zero.eventually (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ)<1/20))
  have hb : ∀ᶠ τ in atImInfty,
      ‖lambdaRatio τ / cuspNome τ - 16‖ < 1 ∧ ‖cuspNome τ‖ < 1/20 := by
    filter_upwards [hratio,hq] with τ hr hq
    change dist (lambdaRatio τ / cuspNome τ) (16:ℂ) < 1 at hr
    rw [Complex.dist_eq] at hr
    exact ⟨hr, mem_ball_zero_iff.mp hq⟩
  rw [atImInfty, eventually_comap, eventually_atTop] at hb
  obtain ⟨Y,hY⟩ := hb
  exact ⟨Y,fun τ hτ => hY _ hτ τ rfl⟩

/-- Continuous unit complex number rotating once counterclockwise as `u` runs from 0 to 1. -/
noncomputable def positiveTurn (u : unitInterval) : ℂ :=
  Complex.exp (((2 : ℂ) * Real.pi * (u : ℝ)) * Complex.I)

private theorem continuous_positiveTurn : Continuous positiveTurn := by
  unfold positiveTurn
  fun_prop

@[simp] theorem norm_positiveTurn (u : unitInterval) : ‖positiveTurn u‖ = 1 := by
  simp [positiveTurn, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

@[simp] theorem positiveTurn_zero : positiveTurn 0 = 1 := by simp [positiveTurn]
@[simp] theorem positiveTurn_one : positiveTurn 1 = 1 := by simp [positiveTurn]

/-- The positive circle about the puncture `0`, based at `a` and avoiding the puncture `1`. -/
noncomputable def positiveZeroCircle (a : ({0,1}ᶜ : Set ℂ)) (ha : ‖(a:ℂ)‖ < 1) : Path a a where
  toFun u := ⟨(a:ℂ) * positiveTurn u, by
    have h₀ : (a:ℂ) ≠ 0 := fun h => a.property (by rw [h]; simp)
    have hu : positiveTurn u ≠ 0 := Complex.exp_ne_zero _
    have h₁ : (a:ℂ) * positiveTurn u ≠ 1 := by
      intro h
      have := congrArg norm h
      exact ha.ne (by simpa [norm_mul] using this)
    simp [h₀, hu, h₁]⟩
  continuous_toFun := (continuous_const.mul continuous_positiveTurn).subtype_mk _
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

private theorem nome_end (τ : UpperHalfPlane) :
    cuspNome (cuspTranslation τ 1) = cuspNome τ := by
  change Complex.exp _ = _
  rw [cuspTranslation_q]
  exact (show cuspNome τ * positiveTurn 1 = cuspNome τ by rw [positiveTurn_one, mul_one])

private noncomputable def normalizedRatio (τ : UpperHalfPlane) : ℂ := lambdaRatio τ / cuspNome τ

private theorem normalizedRatio_mul_nome (τ : UpperHalfPlane) :
    normalizedRatio τ * cuspNome τ = lambdaRatio τ :=
  div_mul_cancel₀ _ (cuspNome_ne_zero _)

private theorem norm_ratio_lt {r : ℂ} (hr : ‖r - 16‖ < 1) : ‖r‖ < 17 := by
  have ht := norm_add_le (r-16) (16:ℂ)
  rw [sub_add_cancel] at ht
  norm_num at ht
  linarith

private theorem interpolation_mem {r q : ℂ} (h : r ∈ Metric.ball (16:ℂ) 1)
    (hq : ‖q‖ < 1/20) (hq₀ : q ≠ 0) : q*r ∈ ({0,1}ᶜ : Set ℂ) := by
  change dist r 16 < 1 at h
  rw [Complex.dist_eq] at h
  have hr : r ≠ 0 := by rintro rfl; norm_num at h
  have hbound := norm_ratio_lt h
  have hh : ‖q*r‖ < 1 := by
    rw [norm_mul]
    nlinarith [mul_lt_mul_of_pos_left hbound (norm_pos_iff.mpr hq₀)]
  have hn : q*r ≠ 1 := by intro he; simp [he] at hh
  simpa using And.intro (mul_ne_zero hq₀ hr) hn

/-- Sufficiently high lambda cusp loops represent the based class of the actual positively oriented
small circle, with the basepoint fixed throughout the deformation. -/
theorem zeroCuspLoop_homotopic_to_positiveCircle :
    ∃ Y : ℝ, ∀ τ : UpperHalfPlane, Y ≤ τ.im →
      ∃ ha : ‖lambdaRatio τ‖ < 1,
        (positiveZeroCircle (lambdaPunctured τ) ha).Homotopic (zeroCuspLoop τ) := by
  obtain ⟨Y,hY⟩ := exists_cusp_height
  refine ⟨Y, fun τ hτ => ?_⟩
  have hb (u : unitInterval) := hY (cuspTranslation τ u) (by simpa [cuspTranslation] using hτ)
  have hb₀ := hY τ hτ
  have ha : ‖lambdaRatio τ‖ < 1 := by
    rw [← normalizedRatio_mul_nome, norm_mul]
    have hbound : ‖normalizedRatio τ‖ < 17 := norm_ratio_lt hb₀.1
    nlinarith [mul_lt_mul_of_pos_right hbound (norm_pos_iff.mpr (cuspNome_ne_zero τ)),
      hb₀.2]
  refine ⟨ha, ?_⟩
  let q (u : unitInterval) := cuspNome (cuspTranslation τ u)
  let r (u : unitInterval) := normalizedRatio (cuspTranslation τ u)
  let rc := normalizedRatio τ
  let factor (s u : unitInterval) : ℂ := (1-(s:ℝ)) • rc + (s:ℝ) • r u
  have hf (s u : unitInterval) : factor s u ∈ Metric.ball (16:ℂ) 1 := by
    apply convex_ball (16:ℂ) 1 _ _ (sub_nonneg.mpr s.property.2) s.property.1 (by ring)
    · exact Metric.mem_ball.mpr (by rw [Complex.dist_eq]; exact hb₀.1)
    · exact Metric.mem_ball.mpr (by rw [Complex.dist_eq]; exact (hb u).1)
  let H (v : unitInterval × unitInterval) : ℂ := q v.2 * factor v.1 v.2
  have hc : Continuous (fun v : unitInterval × unitInterval => cuspTranslation τ v.2) :=
    (cuspTranslation τ).continuous.comp continuous_snd
  have hq := continuous_cuspNome.comp hc
  have hr := (lambdaRatio_mdifferentiable.continuous.comp hc).div hq (fun _ => cuspNome_ne_zero _)
  have hH : Continuous H := by
    have hs : Continuous (fun v : unitInterval × unitInterval => (v.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hs' : Continuous (fun v : unitInterval × unitInterval => 1-(v.1 : ℝ)) :=
      continuous_const.sub hs
    have hl : Continuous (fun v : unitInterval × unitInterval => (1-(v.1:ℝ)) • rc) :=
      hs'.smul continuous_const
    have hh : Continuous (fun v : unitInterval × unitInterval => (v.1:ℝ) • r v.2) := hs.smul hr
    exact hq.mul (hl.add hh)
  let hom : C(unitInterval × unitInterval, ({0,1}ᶜ : Set ℂ)) :=
    ⟨fun v => ⟨H v, interpolation_mem (hf v.1 v.2) (hb v.2).2 (cuspNome_ne_zero _)⟩,
      hH.subtype_mk _⟩
  have hnome (u : unitInterval) : q u = cuspNome τ * positiveTurn u := cuspTranslation_q τ u
  have hR : r 1 = rc := by
    have hl : lambdaRatio (cuspTranslation τ 1) = lambdaRatio τ := congrArg Subtype.val (zeroCuspLoop τ).target
    change lambdaRatio _ / cuspNome _ = _
    rw [hl, nome_end]
    rfl
  have heq (s : unitInterval) : factor s 0 = rc ∧ factor s 1 = rc := by
    have h₀ : r 0 = rc := by simp only [r,rc,cuspTranslation_zero]
    simp only [factor,h₀,hR,← add_smul,sub_add_cancel,one_smul,and_self]
  refine ⟨{ toContinuousMap := hom, map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
  · intro u
    apply Subtype.ext
    change q u * factor 0 u = lambdaRatio τ * positiveTurn u
    rw [hnome, ← normalizedRatio_mul_nome τ]
    simp [factor,rc]
    ring
  · intro u
    apply Subtype.ext
    change q u * factor 1 u = lambdaRatio (cuspTranslation τ u)
    simpa [factor,q,r,mul_comm] using normalizedRatio_mul_nome (cuspTranslation τ u)
  · intro s u hu
    rcases hu with h | h
    · subst u
      apply Subtype.ext
      change q 0 * factor s 0 = lambdaRatio τ * positiveTurn 0
      rw [(heq s).1, hnome, positiveTurn_zero, mul_one, mul_one, mul_comm]
      exact normalizedRatio_mul_nome τ
    · change u = 1 at h
      subst u
      apply Subtype.ext
      change q 1 * factor s 1 = lambdaRatio τ * positiveTurn 1
      rw [(heq s).2, hnome, positiveTurn_one, mul_one, mul_one, mul_comm]
      exact normalizedRatio_mul_nome τ

private theorem swapLambdaPunctures_mem (a : ({0,1}ᶜ : Set ℂ)) :
    1 - (a:ℂ) ∈ ({0,1}ᶜ : Set ℂ) := by
  have h₀ : (a:ℂ) ≠ 0 := fun h => a.property (by rw [h]; simp)
  have h₁ : (a:ℂ) ≠ 1 := fun h => a.property (by rw [h]; simp)
  simp [sub_eq_zero, Ne.symm h₁, h₀]

/-- Interchange the punctures by the holomorphic involution `z ↦ 1-z`. -/
noncomputable def swapLambdaPunctures : C(({0,1}ᶜ : Set ℂ), ({0,1}ᶜ : Set ℂ)) where
  toFun a := ⟨1 - (a:ℂ), swapLambdaPunctures_mem a⟩
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk swapLambdaPunctures_mem

@[simp] theorem swapLambdaPunctures_twice (a : ({0,1}ᶜ : Set ℂ)) :
    swapLambdaPunctures (swapLambdaPunctures a) = a :=
  Subtype.ext (by change 1-(1-(a:ℂ)) = a; ring)

private theorem lambdaPunctured_S (τ : UpperHalfPlane) :
    lambdaPunctured (ModularGroup.S • τ) = swapLambdaPunctures (lambdaPunctured τ) :=
  Subtype.ext (lambdaRatio_S _)

/-- The positive circle based at `a` about the puncture `1`, avoiding zero. -/
noncomputable def positiveOneCircle (a : ({0,1}ᶜ : Set ℂ)) (ha : ‖1-(a:ℂ)‖ < 1) : Path a a :=
  ((positiveZeroCircle (swapLambdaPunctures a) ha).map swapLambdaPunctures.continuous).cast
    (swapLambdaPunctures_twice a).symm (swapLambdaPunctures_twice a).symm

theorem positiveOneCircle_coe (a : ({0,1}ᶜ : Set ℂ)) (ha : ‖1-(a:ℂ)‖ < 1) (u : unitInterval) :
    (positiveOneCircle a ha u : ℂ) = 1 + ((a:ℂ)-1) * positiveTurn u := by
  change 1 - (1-(a:ℂ)) * positiveTurn u = _
  ring

/-- The same height threshold gives a positive small circle based at `λ(Sτ)` and centered at one. -/
theorem oneCuspLoop_homotopic_to_positiveCircle :
    ∃ Y : ℝ, ∀ τ : UpperHalfPlane, Y ≤ τ.im →
      ∃ ha : ‖1 - lambdaRatio (ModularGroup.S • τ)‖ < 1,
        (positiveOneCircle (lambdaPunctured (ModularGroup.S • τ)) ha).Homotopic (oneCuspLoop τ) := by
  obtain ⟨Y,hY⟩ := zeroCuspLoop_homotopic_to_positiveCircle
  refine ⟨Y,fun τ hτ => ?_⟩
  obtain ⟨ha, h⟩ := hY τ hτ
  have hb : ‖1 - lambdaRatio (ModularGroup.S • τ)‖ < 1 := by rw [lambdaRatio_S, sub_sub_cancel]; exact ha
  refine ⟨hb, ?_⟩
  have hbase := lambdaPunctured_S τ
  have h' :
      (((positiveZeroCircle (lambdaPunctured τ) ha).map swapLambdaPunctures.continuous).cast
        hbase hbase).Homotopic
      (((zeroCuspLoop τ).map swapLambdaPunctures.continuous).cast hbase hbase) :=
    h.map swapLambdaPunctures
  have hfirst :
      (((positiveZeroCircle (lambdaPunctured τ) ha).map swapLambdaPunctures.continuous).cast
        hbase hbase) = positiveOneCircle (lambdaPunctured (ModularGroup.S • τ)) hb := by
    apply Path.ext
    funext u
    apply Subtype.ext
    change 1 - lambdaRatio τ * positiveTurn u = 1-(1-lambdaRatio (ModularGroup.S • τ))*positiveTurn u
    rw [lambdaRatio_S]; ring
  have hlast : (((zeroCuspLoop τ).map swapLambdaPunctures.continuous).cast hbase hbase) =
      oneCuspLoop τ := by
    apply Path.ext
    funext u
    exact Subtype.ext (oneCuspLoop_coe τ u).symm
  rwa [hfirst,hlast] at h'

/-- Monodromy of honest positive circles around both punctures in the high cusp regime. -/
theorem positiveCircles_monodromy :
    ∃ Y : ℝ, ∀ τ : UpperHalfPlane, Y ≤ τ.im →
      ∃ (h₀ : ‖lambdaRatio τ‖ < 1) (h₁ : ‖1-lambdaRatio (ModularGroup.S • τ)‖ < 1),
        (lambdaPunctured_isCoveringMap.monodromy (.mk (positiveZeroCircle (lambdaPunctured τ) h₀))
          ⟨τ,rfl⟩ : UpperHalfPlane) = ModularGroup.T ^ (2:ℕ) • τ ∧
        (lambdaPunctured_isCoveringMap.monodromy
          (.mk (positiveOneCircle (lambdaPunctured (ModularGroup.S • τ)) h₁))
          ⟨ModularGroup.S • τ,rfl⟩ : UpperHalfPlane) =
          (ModularGroup.S * ModularGroup.T ^ (2:ℕ) * ModularGroup.S⁻¹) • (ModularGroup.S • τ) := by
  obtain ⟨Y₀,hY₀⟩ := zeroCuspLoop_homotopic_to_positiveCircle
  obtain ⟨Y₁,hY₁⟩ := oneCuspLoop_homotopic_to_positiveCircle
  refine ⟨max Y₀ Y₁, fun τ hτ => ?_⟩
  obtain ⟨h₀, h₀'⟩ := hY₀ τ ((le_max_left ..).trans hτ)
  obtain ⟨h₁, h₁'⟩ := hY₁ τ ((le_max_right ..).trans hτ)
  refine ⟨h₀,h₁,?_,?_⟩
  · rw [show Path.Homotopic.Quotient.mk _ = .mk (zeroCuspLoop τ) from Quotient.sound h₀']
    exact zeroCuspLoop_monodromy _
  · rw [show Path.Homotopic.Quotient.mk _ = .mk (oneCuspLoop τ) from Quotient.sound h₁']
    exact oneCuspLoop_monodromy _

end BelgianChocolate.ModularLambdaRatio

