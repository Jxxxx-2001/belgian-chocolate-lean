import ControllerWitnessData

namespace BelgianChocolate.ControlWitness

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem x_exact_check :
    verifiedSchur (schurScales 28 (shiftedCayley xNums)) (shiftedCayley xNums) = true ∧
    evalRat xNums (((billion:ℚ)-1)/billion) ≠ 0 ∧
    xNums.length = 29 ∧ xNums.getLastD 0 ≠ 0 := by
  decide +kernel

end BelgianChocolate.ControlWitness

