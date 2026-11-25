import ControllerWitnessData

namespace BelgianChocolate.ControlWitness

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem z_exact_check :
    verifiedSchur (schurScales 30 (shiftedCayley zNums)) (shiftedCayley zNums) = true ∧
    evalRat zNums (((billion:ℚ)-1)/billion) ≠ 0 ∧
    zNums.length = 31 ∧ zNums.getLastD 0 ≠ 0 := by
  decide +kernel

end BelgianChocolate.ControlWitness

