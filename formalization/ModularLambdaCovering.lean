module

public import ModularLambdaJ
public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Basic
public import TauCeti.Analysis.Complex.Conformal.LocalDegree
public import Mathlib.Topology.Covering.Quotient
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-! The effective level-two action and the remaining geometric inputs to the
quotient-covering construction for the project's modular lambda function. -/

public section

open scoped MatrixGroups Manifold
open Filter Set Topology UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup

namespace BelgianChocolate.ModularLambdaRatio


/-- The integral trace of a level-two matrix cannot lie strictly between -2 and 2. -/
theorem gammaTwo_abs_trace_ge_two {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma 2) :
    (2 : ℤ) ≤ |(γ : Matrix (Fin 2) (Fin 2) ℤ).trace| := by
  rw [Matrix.trace_fin_two]
  by_contra! htrace
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  have even (x : ℤ) (hx : ((x : ℤ) : ZMod 2) = 0) : 2 ∣ x :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
  obtain ⟨a, ha⟩ := even (γ 0 0 - 1) (by push_cast; rw [h00, sub_self])
  obtain ⟨d, hd⟩ := even (γ 1 1 - 1) (by push_cast; rw [h11, sub_self])
  obtain ⟨b, hb⟩ := even (γ 0 1) h01
  obtain ⟨c, hc⟩ := even (γ 1 0) h10
  have hdiag₀ : γ 0 0 = 2 * a + 1 := by omega
  have hdiag₁ : γ 1 1 = -(2 * a + 1) := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp htrace
    omega
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hdiag₀, hdiag₁, hb, hc] at hdet
  have hincompatible : -1 - 4 * (a ^ 2 + a + b * c) = (1 : ℤ) := by
    linear_combination hdet
  omega


/-- Projectivizing removes the full point stabilizer of a level-two matrix. -/
theorem gammaTwo_psl_fix_eq_one {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma 2)
    {z : ℍ} (hz : sl2zToPSL2R γ • z = z) : sl2zToPSL2R γ = 1 := by
  let A := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ
  have hcast : sl2zToPSL2R γ = (A : PSL(2, ℝ)) := sl2zToPSL2R_apply γ
  rw [hcast] at hz ⊢
  by_contra hA
  rw [UpperHalfPlane.pslMk_smul] at hz
  have hell := Matrix.SpecialLinearGroup.isElliptic_of_smul_eq_self_of_ne_one hz hA
  have hlt := (Matrix.isElliptic_iff_abs_trace_lt_two A.det_coe).mp hell
  rw [Matrix.trace_fin_two] at hlt
  have hτ := gammaTwo_abs_trace_ge_two hγ
  rw [Matrix.trace_fin_two] at hτ
  have hge : (2 : ℝ) ≤ |(γ 0 0 : ℝ) + (γ 1 1 : ℝ)| := by exact_mod_cast hτ
  exact (not_lt_of_ge hge) hlt

theorem gammaTwo_action_free (g : ((CongruenceSubgroup.Gamma 2).map sl2zToPSL2R)) (z : ℍ)
    (h : g • z = z) : g = 1 := by
  obtain ⟨γ, hγ, hg⟩ := g.property
  have hz : sl2zToPSL2R γ • z = z := hg ▸ h
  exact Subtype.ext (hg.symm.trans (gammaTwo_psl_fix_eq_one hγ hz))





/-- The effective group corresponding to the level-two congruence subgroup. -/
abbrev gammaTwoProjective : Subgroup PSL(2, ℝ) :=
  (CongruenceSubgroup.Gamma 2).map sl2zToPSL2R

instance : DiscreteTopology gammaTwoProjective := by
  have h : IsDiscrete (psl2zToPSL2R.range : Set PSL(2, ℝ)) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  exact SetLike.isDiscrete_iff_discreteTopology.mp
    (h.mono (CongruenceSubgroup.Gamma 2).map_sl2zToPSL2R_le_range_psl2zToPSL2R)

instance : IsCancelSMul gammaTwoProjective ℍ :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr gammaTwo_action_free

/-- The invariant takes values in the twice-punctured complex plane. -/
noncomputable def lambdaPunctured (τ : ℍ) : ({0, 1}ᶜ : Set ℂ) :=
  ⟨lambdaRatio τ, by
    simpa using ⟨lambdaRatio_ne_zero τ, lambdaRatio_ne_one τ⟩⟩

theorem lambdaPunctured_isOpenMap : IsOpenMap lambdaPunctured := by
  intro U hU
  have h : lambdaPunctured '' U =
      Subtype.val ⁻¹' (lambdaRatio '' U) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
  rw [h]
  exact (lambdaRatio_isOpenMap U hU).preimage continuous_subtype_val

/-- The actual project lambda map is the quotient covering for the effective
level-two action. -/
theorem lambdaPunctured_quotientCovering :
    IsQuotientCoveringMap lambdaPunctured gammaTwoProjective := by
  have hsurj : Function.Surjective lambdaPunctured := by
    intro a
    have ha := a.property
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at ha
    obtain ⟨τ, hτ⟩ := lambdaRatio_surj ha.1 ha.2
    exact ⟨τ, Subtype.ext hτ⟩
  have hcont : Continuous lambdaPunctured :=
    lambdaRatio_mdifferentiable.continuous.subtype_mk _
  apply (lambdaPunctured_isOpenMap.isQuotientMap hcont hsurj)
    |>.isQuotientCoveringMap_of_properlyDiscontinuousSMul
  intro x y
  rw [MulAction.mem_orbit_iff]
  constructor
  · intro h
    have he : lambdaRatio y = lambdaRatio x := (congrArg Subtype.val h).symm
    obtain ⟨γ, hγ, hg⟩ := lambdaRatio_fiber.mp he
    exact ⟨⟨sl2zToPSL2R γ, γ, hγ, rfl⟩,
      by simpa only [Subgroup.smul_def, UpperHalfPlane.sl2zToPSL2R_smul] using hg⟩
  · rintro ⟨g, hg⟩
    obtain ⟨γ, hγ, hproj⟩ := g.property
    have he : γ • y = x := by
      simpa only [Subgroup.smul_def, ← hproj, UpperHalfPlane.sl2zToPSL2R_smul] using hg
    exact Subtype.ext (lambdaRatio_fiber.mpr ⟨γ, hγ, he⟩).symm

theorem lambdaPunctured_isCoveringMap : IsCoveringMap lambdaPunctured :=
  lambdaPunctured_quotientCovering.isCoveringMap

/-- In the ordinary complex coordinate on the upper half-plane, the quotient
covering has nonzero derivative at every point. -/
theorem lambdaRatio_deriv_ne_zero (τ : ℍ) :
    deriv (lambdaRatio ∘ ofComplex) (τ : ℂ) ≠ 0 := by
  let f : ℂ → ℂ := lambdaRatio ∘ ofComplex
  have hd : DifferentiableOn ℂ f upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp lambdaRatio_mdifferentiable
  have ha := hd.analyticOnNhd isOpen_upperHalfPlaneSet (τ : ℂ) τ.im_pos
  obtain ⟨U, hU, hsep⟩ := lambdaPunctured_quotientCovering.disjoint τ
  apply (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero ha).mp
  refine ⟨((↑) : ℍ → ℂ) '' U, isOpenEmbedding_coe.image_mem_nhds.mpr hU, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
  have hxy : lambdaPunctured x = lambdaPunctured y := by
    apply Subtype.ext
    change lambdaRatio x = lambdaRatio y
    simpa only [f, Function.comp_apply, ofComplex_apply] using he
  obtain ⟨g, hg⟩ := lambdaPunctured_quotientCovering.apply_eq_iff_mem_orbit.mp hxy
  have h1 : g = 1 := hsep g ⟨x, ⟨y, hy, hg⟩, hx⟩
  have hyx : y = x := by simpa [h1] using hg
  exact congrArg UpperHalfPlane.coe hyx.symm

end BelgianChocolate.ModularLambdaRatio

