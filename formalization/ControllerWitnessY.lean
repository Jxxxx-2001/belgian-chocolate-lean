import ControllerWitnessData

namespace BelgianChocolate.ControlWitness

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem y_exact_check :
    verifiedSchur (schurScales 28 (shiftedCayley yNums)) (shiftedCayley yNums) = true ∧
    evalRat yNums (((billion:ℚ)-1)/billion) ≠ 0 ∧
    yNums.length = 29 ∧ yNums.getLastD 0 ≠ 0 := by
  decide +kernel

end BelgianChocolate.ControlWitness

