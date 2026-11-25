import FirstAnnulusMatrix
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic

namespace BelgianChocolate.FirstAnnulus

open scoped MatrixGroups

/-- The zero-cusp matrix is the positive level-two translation. -/
theorem zeroGenerator_eq_T_sq : zeroGenerator = ModularGroup.T ^ (2 : ℕ) := by
  decide

/-- In the original upper-half-plane coordinate, the positive one-cusp
translation is conjugated by the matrix acting as negative inversion. -/
theorem oneGenerator_eq_S_T_sq_S_inv :
    oneGenerator = ModularGroup.S * ModularGroup.T ^ (2 : ℕ) * ModularGroup.S⁻¹ := by
  decide

theorem zeroGenerator_mem_gammaTwo : zeroGenerator ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  decide

theorem oneGenerator_mem_gammaTwo : oneGenerator ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  decide

end BelgianChocolate.FirstAnnulus
