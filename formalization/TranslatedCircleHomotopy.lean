import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic

namespace BelgianChocolate
open Set Metric Topology unitInterval

private theorem translatedCircle_mem {a b c : ℂ}
    (hc0 : c ≠ 0) (hcB : ‖c‖ < ‖b - a‖) (u : Circle) :
    a + c * (u : ℂ) ∈ ({a, b}ᶜ : Set ℂ) := by
  have hnorm : ‖a + c * (u : ℂ) - a‖ = ‖c‖ := by simp
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · intro he
    rw [he, sub_self, norm_zero] at hnorm
    exact hc0 (norm_eq_zero.mp hnorm.symm)
  · intro he
    rw [he] at hnorm
    exact (ne_of_lt hcB) hnorm.symm

/-- A positively oriented circle in the twice-punctured plane, encoded by its
nonzero complex radius and initial angle. -/
noncomputable def translatedCircle {a b c : ℂ}
    (hc0 : c ≠ 0) (hcB : ‖c‖ < ‖b - a‖) : C(Circle, ({a,b}ᶜ : Set ℂ)) :=
  ⟨fun u ↦ ⟨a + c * (u : ℂ), translatedCircle_mem hc0 hcB u⟩,
    Continuous.subtype_mk (by fun_prop) _⟩

/-- Two positive circles about the same puncture are freely homotopic if
their radii are smaller than the distance to the other puncture. -/
theorem translatedCircle_homotopy {a b c d : ℂ} (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hcB : ‖c‖ < ‖b - a‖) (hdB : ‖d‖ < ‖b - a‖) :
    Nonempty ((translatedCircle hc0 hcB).Homotopy (translatedCircle hd0 hdB)) := by
  let R (s : unitInterval) := (1 - (s : ℝ)) * ‖c‖ + (s : ℝ) * ‖d‖
  let A (s : unitInterval) :=
    (1 - (s : ℝ)) * Complex.arg c + (s : ℝ) * Complex.arg d
  let k (s : unitInterval) := (R s : ℂ) * Complex.exp ((A s : ℂ) * Complex.I)
  have hR (s : unitInterval) : 0 < R s ∧ R s < ‖b - a‖ := by
    have hc := norm_pos_iff.mpr hc0
    have hd := norm_pos_iff.mpr hd0
    have h0 : 0 ≤ (s : ℝ) := s.property.1
    have h1 : (s : ℝ) ≤ 1 := s.property.2
    constructor
    · change 0 < (1 - (s : ℝ)) * ‖c‖ + (s : ℝ) * ‖d‖
      rcases eq_or_lt_of_le h0 with he | hl
      · rw [he.symm, sub_zero, one_mul, zero_mul, add_zero]
        exact hc
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr h1) hc.le) (mul_pos hl hd)
    · change (1 - (s : ℝ)) * ‖c‖ + (s : ℝ) * ‖d‖ < ‖b - a‖
      have hM : max ‖c‖ ‖d‖ < ‖b - a‖ := max_lt hcB hdB
      calc
        _ ≤ (1 - (s : ℝ)) * max ‖c‖ ‖d‖ + (s : ℝ) * max ‖c‖ ‖d‖ :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr h1))
            (mul_le_mul_of_nonneg_left (le_max_right _ _) h0)
        _ = max ‖c‖ ‖d‖ := by ring
        _ < ‖b - a‖ := hM
  have hnorm (s : unitInterval) : ‖k s‖ = R s := by
    simp [k, Complex.norm_exp, Complex.mul_re, abs_of_pos (hR s).1]
  have hmem (s : unitInterval) (u : Circle) : a + k s * (u : ℂ) ∈ ({a,b}ᶜ : Set ℂ) :=
    translatedCircle_mem (norm_pos_iff.mp ((hnorm s).symm ▸ (hR s).1))
      ((hnorm s).symm ▸ (hR s).2) u
  have hK : Continuous k := by unfold k R A; fun_prop
  have hK0 : k 0 = c := by simp [k, R, A]
  have hK1 : k 1 = d := by simp [k, R, A]
  refine ⟨{
    toFun := fun su ↦ ⟨a + k su.1 * (su.2 : ℂ), hmem su.1 su.2⟩
    continuous_toFun := Continuous.subtype_mk (by fun_prop) _
    map_zero_left := fun u ↦ Subtype.ext (by change a + k 0 * _ = a + c * _; rw [hK0])
    map_one_left := fun u ↦ Subtype.ext (by change a + k 1 * _ = a + d * _; rw [hK1])
  }⟩

end BelgianChocolate
