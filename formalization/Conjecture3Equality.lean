import HighDegreeGap
import LowDegreeSharpness

namespace BelgianChocolate.Conjectures

/-- The continued-fraction bound is the constant-numerator supremum exactly
for denominator degrees one, two, three and four. -/
theorem conjecture3_equality_iff {n : ℕ} (hn : 0 < n) :
    δₙ_star n = δₙ n ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
  constructor
  · intro he
    have hn4 : n ≤ 4 := by
      by_contra! hl
      exact (conjecture3_strict_of_five_le (show 5 ≤ n by omega)).ne he
    omega
  · intro h
    exact conjecture3_sharp_of_le_four hn (by omega)

#print axioms conjecture3_equality_iff
end BelgianChocolate.Conjectures

