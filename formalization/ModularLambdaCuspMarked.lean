import ModularLambdaCuspCover
import MarkedRealAxisSlice

/-! Compatibility of the analytic cusp filling with the marked coordinate. -/

open UpperHalfPlane
open scoped MatrixGroups

namespace BelgianChocolate.ModularLambdaRatio
/-- The marked cusp coordinate is the negative nome in the inverted chart. -/
theorem markedCusp_eq_neg_nome (τ : ℍ) :
    BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ) =
      -(cuspNomeDisc (ModularGroup.S • τ) : ℂ) := by
  rw [BelgianChocolate.MarkedRealAxis.cusp, cuspNomeDisc_coe, ModularGroup.coe_S_smul]
  congr 2
  simp only [div_eq_mul_inv]
  ring

theorem markedCusp_mem_puncturedUnitDisc (τ : ℍ) :
    ‖BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ)‖ < 1 ∧
      BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ) ≠ 0 := by
  rw [markedCusp_eq_neg_nome]
  have h := (cuspNomeDisc (ModularGroup.S • τ)).property
  simpa only [norm_neg, neg_ne_zero] using h

/-- The filled cusp map recovers lambda in the marked coordinate. -/
theorem cuspU_markedCusp (τ : ℍ) :
    cuspU (BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ)) = lambdaRatio τ := by
  rw [markedCusp_eq_neg_nome, cuspU, neg_neg, cuspLambda_nome, lambdaRatio_S, sub_sub_cancel]

#print axioms cuspU_markedCusp
/-- The marked cusp coordinate is invariant under every integral period in the inverted chart. -/
theorem markedCusp_conjPeriod (n : ℤ) (τ : ℍ) :
    BelgianChocolate.MarkedRealAxis.cusp
      ((ModularGroup.S⁻¹ • (ModularGroup.T ^ (2 * n) • (ModularGroup.S • τ))) : ℍ) =
    BelgianChocolate.MarkedRealAxis.cusp (τ : ℂ) := by
  rw [markedCusp_eq_neg_nome, markedCusp_eq_neg_nome, smul_inv_smul]
  have hNome :
      cuspNomeDisc (ModularGroup.T ^ (2 * n) • (ModularGroup.S • τ)) =
        cuspNomeDisc (ModularGroup.S • τ) :=
    (cuspNomeDisc_eq_iff _ _).mpr
      ⟨n, by simp only [UpperHalfPlane.modular_T_zpow_smul, Int.cast_mul, Int.cast_ofNat]⟩
  exact congrArg (fun q : PuncturedUnitDisc => -(q : ℂ)) hNome

#print axioms markedCusp_conjPeriod
end BelgianChocolate.ModularLambdaRatio
