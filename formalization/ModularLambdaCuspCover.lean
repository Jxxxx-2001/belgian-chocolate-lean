module

public import ModularLambdaCovering
import all ModularLambdaCovering
public import TauCeti.Topology.Covering.Quotient
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup
import Mathlib.Tactic.Ring

/-! The period-two quotient of modular lambda and its filling at the cusp. -/

public section

open Set Topology UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups

namespace BelgianChocolate.ModularLambdaRatio

/-- The open unit disc with its center removed. -/
abbrev PuncturedUnitDisc := {q : ℂ // ‖q‖ < 1 ∧ q ≠ 0}

/-- The level-two nome, valued in the punctured unit disc. -/
noncomputable def cuspNomeDisc (τ : ℍ) : PuncturedUnitDisc :=
  ⟨Function.Periodic.qParam 2 (τ : ℂ),
    Function.Periodic.norm_qParam_lt_one (by norm_num) τ.im_pos,
    Complex.exp_ne_zero _⟩

theorem cuspNomeDisc_coe (τ : ℍ) : (cuspNomeDisc τ : ℂ) = Complex.exp (Real.pi * Complex.I * (τ : ℂ)) := by
  change Function.Periodic.qParam 2 (τ : ℂ) = _
  unfold Function.Periodic.qParam
  congr 1
  push_cast
  ring

theorem cuspNomeDisc_surjective : Function.Surjective cuspNomeDisc := by
  intro q
  let τ : ℍ := ⟨Function.Periodic.invQParam 2 q, by
    rw [Function.Periodic.im_invQParam]
    exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by norm_num : (-2 : ℝ) < 0)
      (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))
      (Real.log_neg (norm_pos_iff.mpr q.property.2) q.property.1)⟩
  exact ⟨τ, Subtype.ext (Function.Periodic.qParam_right_inv (by norm_num) q.property.2)⟩

private theorem isOpen_puncturedUnitDisc : IsOpen {q : ℂ | ‖q‖ < 1 ∧ q ≠ 0} :=
  (isOpen_lt continuous_norm continuous_const).inter isOpen_compl_singleton

theorem cuspNomeDisc_isQuotientMap : IsQuotientMap cuspNomeDisc := by
  have hexp : IsOpenMap Complex.exp :=
    (isOpen_compl_singleton (x := (0 : ℂ))).isOpenEmbedding_subtypeVal.isOpenMap.comp
      Complex.isCoveringMap_exp.isOpenMap
  let c : ℂ := Real.pi * Complex.I
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have hopen : IsOpenMap (fun τ : ℍ => Complex.exp (c * (τ : ℂ))) :=
    hexp.comp ((Homeomorph.mulLeft₀ c hc).isOpenMap.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap)
  have hcont : Continuous (fun τ : ℍ => Complex.exp (c * (τ : ℂ))) := by fun_prop
  have h (τ : ℍ) : Complex.exp (c * (τ : ℂ)) = (cuspNomeDisc τ : ℂ) := (cuspNomeDisc_coe τ).symm
  simp_rw [h] at hopen hcont
  exact (isOpen_puncturedUnitDisc.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr hopen).isQuotientMap
    (isOpen_puncturedUnitDisc.isOpenEmbedding_subtypeVal.isEmbedding.continuous_iff.mpr hcont)
    cuspNomeDisc_surjective

theorem cuspNomeDisc_eq_iff (x y : ℍ) :
    cuspNomeDisc x = cuspNomeDisc y ↔ ∃ n : ℤ, x = (2 * n : ℝ) +ᵥ y := by
  rw [Subtype.ext_iff, cuspNomeDisc_coe, cuspNomeDisc_coe, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, UpperHalfPlane.ext ?_⟩
    rw [UpperHalfPlane.coe_vadd]
    have hp : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    apply mul_left_cancel₀ (mul_ne_zero hp Complex.I_ne_zero)
    push_cast
    linear_combination hn
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [UpperHalfPlane.coe_vadd]
    push_cast
    ring

/-- The holomorphic level-two cusp function on the open unit disc, including zero. -/
noncomputable def cuspLambda : ℂ → ℂ := UpperHalfPlane.cuspFunction 2 lambdaRatio

theorem cuspLambda_nome (τ : ℍ) : cuspLambda (cuspNomeDisc τ : ℂ) = lambdaRatio τ := by
  rw [cuspNomeDisc_coe]
  exact lambdaCusp_eq_on_q τ

theorem cuspLambda_zero : cuspLambda 0 = 0 := lambdaCusp_zero_and_deriv.1

theorem cuspLambda_hasDerivAt_zero : HasDerivAt cuspLambda (16 : ℂ) 0 :=
  lambdaCusp_zero_and_deriv.2

theorem cuspLambda_differentiableAt {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ cuspLambda q := lambdaCusp_differentiableAt hq

/-- The punctured cusp map descends from the modular lambda covering. -/
noncomputable def cuspLambdaPunctured (q : PuncturedUnitDisc) : ({0, 1}ᶜ : Set ℂ) :=
  ⟨cuspLambda q, by
    obtain ⟨τ, rfl⟩ := cuspNomeDisc_surjective q
    rw [cuspLambda_nome]
    simpa using ⟨lambdaRatio_ne_zero τ, lambdaRatio_ne_one τ⟩⟩

theorem cuspLambdaPunctured_comp_nome : cuspLambdaPunctured ∘ cuspNomeDisc = lambdaPunctured := by
  funext τ
  apply Subtype.ext
  change cuspLambda (cuspNomeDisc τ : ℂ) = lambdaRatio τ
  exact cuspLambda_nome τ

/-- The positive period-two translation in the effective modular group. -/
noncomputable def cuspPeriod : gammaTwoProjective :=
  ⟨sl2zToPSL2R (ModularGroup.T ^ (2 : ℤ)), Subgroup.mem_map_of_mem _
    (CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma 2 2 dvd_rfl)⟩

theorem cuspPeriod_zpow_smul (n : ℤ) (τ : ℍ) :
    cuspPeriod ^ n • τ = (2 * n : ℝ) +ᵥ τ := by
  change sl2zToPSL2R (ModularGroup.T ^ (2 : ℤ)) ^ n • τ = _
  rw [← map_zpow, UpperHalfPlane.sl2zToPSL2R_smul, ← zpow_mul,
    UpperHalfPlane.modular_T_zpow_smul]
  simp only [Int.cast_mul, Int.cast_ofNat]

theorem cuspNomeDisc_quotientCovering :
    IsQuotientCoveringMap cuspNomeDisc (Subgroup.zpowers cuspPeriod) := by
  apply cuspNomeDisc_isQuotientMap.isQuotientCoveringMap_of_properlyDiscontinuousSMul
  intro x y
  rw [cuspNomeDisc_eq_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨cuspPeriod ^ n, Subgroup.zpow_mem_zpowers cuspPeriod n⟩,
      (cuspPeriod_zpow_smul n y).trans hn.symm⟩
  · rintro ⟨⟨g, hg⟩, he⟩
    obtain ⟨n, rfl⟩ := hg
    exact ⟨n, he.symm.trans (cuspPeriod_zpow_smul n y)⟩

theorem cuspLambdaPunctured_isCoveringMap : IsCoveringMap cuspLambdaPunctured :=
  lambdaPunctured_quotientCovering.isCoveringMap_of_comp cuspNomeDisc_quotientCovering
    cuspLambdaPunctured_comp_nome

#print axioms cuspNomeDisc_surjective
#print axioms cuspNomeDisc_quotientCovering
#print axioms cuspLambdaPunctured_isCoveringMap

theorem cuspLambda_zero_iff {q : ℂ} (hq : ‖q‖ < 1) : cuspLambda q = 0 ↔ q = 0 := by
  constructor
  · intro h
    by_contra hn
    have hnonzero := (cuspLambdaPunctured ⟨q, hq, hn⟩).property
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hnonzero
    exact hnonzero.1 h
  · rintro rfl
    exact cuspLambda_zero

theorem cuspLambda_ne_one {q : ℂ} (hq : ‖q‖ < 1) : cuspLambda q ≠ 1 := by
  by_cases hq0 : q = 0
  · rw [hq0, cuspLambda_zero]
    norm_num
  · have h := (cuspLambdaPunctured ⟨q, hq, hq0⟩).property
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at h
    exact h.2

/-- The cusp map with the filled value equal to one and a positive derivative at zero. -/
noncomputable def cuspU (w : ℂ) : ℂ := 1 - cuspLambda (-w)

theorem cuspU_zero : cuspU 0 = 1 := by
  simp [cuspU, cuspLambda_zero]

theorem cuspU_eq_one_iff {w : ℂ} (hw : ‖w‖ < 1) : cuspU w = 1 ↔ w = 0 := by
  have hnorm : ‖-w‖ < 1 := by simpa only [norm_neg] using hw
  rw [cuspU, sub_eq_self, cuspLambda_zero_iff hnorm, neg_eq_zero]

theorem cuspU_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : cuspU w ≠ 0 := by
  have hnorm : ‖-w‖ < 1 := by simpa only [norm_neg] using hw
  exact sub_ne_zero.mpr (cuspLambda_ne_one hnorm).symm

theorem cuspU_hasDerivAt_zero : HasDerivAt cuspU (16 : ℂ) 0 := by
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) 0 := (hasDerivAt_id (0 : ℂ)).neg
  have hAt : HasDerivAt cuspLambda (16 : ℂ) ((fun w : ℂ => -w) 0) := by
    simpa only [neg_zero] using cuspLambda_hasDerivAt_zero
  have h := (hAt.comp 0 hneg).const_sub 1
  unfold cuspU
  simpa [Function.comp_def] using h

theorem cuspU_differentiableOn : DifferentiableOn ℂ cuspU {w : ℂ | ‖w‖ < 1} := by
  intro w hw
  change ‖w‖ < 1 at hw
  have hnorm : ‖-w‖ < 1 := by simpa only [norm_neg] using hw
  exact (((cuspLambda_differentiableAt hnorm).comp w differentiableAt_id.neg).const_sub 1).differentiableWithinAt

private theorem negDisc_mem (w : PuncturedUnitDisc) : ‖-(w : ℂ)‖ < 1 ∧ -(w : ℂ) ≠ 0 := by
  simpa only [norm_neg, neg_ne_zero] using w.property

private noncomputable def negDisc : PuncturedUnitDisc ≃ₜ PuncturedUnitDisc where
  toFun w := ⟨-w.1, negDisc_mem w⟩
  invFun w := ⟨-w.1, negDisc_mem w⟩
  left_inv _w := Subtype.ext (neg_neg _)
  right_inv _w := Subtype.ext (neg_neg _)
  continuous_toFun := continuous_subtype_val.neg.subtype_mk negDisc_mem
  continuous_invFun := continuous_subtype_val.neg.subtype_mk negDisc_mem

private theorem oneSub_mem {x : ℂ} (hx : x ∈ ({0,1}ᶜ : Set ℂ)) :
    1 - x ∈ ({0,1}ᶜ : Set ℂ) := by
  have hx' : x ≠ 0 ∧ x ≠ 1 := by simpa using hx
  have h0 : 1 - x ≠ 0 := sub_ne_zero.mpr hx'.2.symm
  have h1 : 1 - x ≠ 1 := fun h => hx'.1 (sub_eq_self.mp h)
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨h0, h1⟩

private noncomputable def oneSubPunctured : (({0,1}ᶜ : Set ℂ)) ≃ₜ (({0,1}ᶜ : Set ℂ)) where
  toFun x := ⟨1 - x.1, oneSub_mem x.property⟩
  invFun x := ⟨1 - x.1, oneSub_mem x.property⟩
  left_inv _x := Subtype.ext (sub_sub_cancel _ _)
  right_inv _x := Subtype.ext (sub_sub_cancel _ _)
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk (fun x => oneSub_mem x.property)
  continuous_invFun := (continuous_const.sub continuous_subtype_val).subtype_mk (fun x => oneSub_mem x.property)

/-- The restriction of the filled cusp map to the punctured unit disc. -/
noncomputable def cuspUPunctured : PuncturedUnitDisc → ({0,1}ᶜ : Set ℂ) :=
  oneSubPunctured ∘ cuspLambdaPunctured ∘ negDisc

theorem cuspUPunctured_coe (w : PuncturedUnitDisc) :
    (cuspUPunctured w : ℂ) = cuspU w := by
  simp [cuspUPunctured, oneSubPunctured, cuspLambdaPunctured, negDisc, cuspU, Function.comp_def]

theorem cuspUPunctured_isCoveringMap : IsCoveringMap cuspUPunctured :=
  (cuspLambdaPunctured_isCoveringMap.comp_homeomorph negDisc).homeomorph_comp oneSubPunctured

#print axioms cuspU_eq_one_iff
#print axioms cuspU_hasDerivAt_zero
#print axioms cuspUPunctured_isCoveringMap

end BelgianChocolate.ModularLambdaRatio

