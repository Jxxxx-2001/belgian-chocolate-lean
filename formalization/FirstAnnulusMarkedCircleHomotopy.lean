import FirstAnnulusEmbedding

namespace BelgianChocolate.FirstAnnulusPaths
open Complex Metric Set unitInterval
open BelgianChocolate.FirstAnnulus (positiveCircleLoop)

private noncomputable def markedCircleValue (p : ℂ) (r : ℝ) (u : Circle) : ℂ :=
  p + (r : ℂ) * (-Complex.I * (u : ℂ))

private theorem markedCircleValue_mem {t r : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p : ℂ} (hp : p = 0 ∨ p = -1) (hr : 0 < r) (hr' : r ≤ 1 / 5) (u : Circle) :
    markedCircleValue p r u ∈ cutDomain t := by
  let w := markedCircleValue p r u
  have hd : ‖w - p‖ = r := by
    simp [w, markedCircleValue, abs_of_pos hr]
  have hR : (10 : ℝ) ≤ 1 / t := (le_div_iff₀ ht).mpr (by linarith)
  have hnp : ‖p‖ ≤ 1 := by rcases hp with rfl | rfl <;> norm_num
  have hrp : p.re ≤ 0 := by rcases hp with rfl | rfl <;> norm_num
  have hnorm : ‖w‖ < 1 / t := by
    have h := norm_add_le (w - p) p
    rw [sub_add_cancel, hd] at h
    linarith
  have hre : w.re < 1 := by
    have h := Complex.re_le_norm (w - p)
    rw [Complex.sub_re, hd] at h
    linarith
  refine ⟨hnorm, fun h ↦ (not_le_of_gt hre) h.2.1, ?_, ?_⟩
  · intro he
    change w = _ at he
    rw [he] at hd
    rcases hp with rfl | rfl <;> norm_num at hd <;> linarith
  · intro he
    change w = _ at he
    rw [he] at hd
    rcases hp with rfl | rfl <;> norm_num at hd <;> linarith

/-- A positive marked circle of any smaller radius, starting below the
puncture just as the fixed loop in the source coordinates does. -/
noncomputable def smallMarkedCircle {t r : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p : ℂ} (hp : p = 0 ∨ p = -1) (hr : 0 < r) (hr' : r ≤ 1 / 5) :
    C(Circle, cutDomain t) :=
  ⟨fun u ↦ ⟨markedCircleValue p r u, markedCircleValue_mem ht ht' hp hr hr' u⟩,
    Continuous.subtype_mk (by unfold markedCircleValue; fun_prop) _⟩

theorem smallMarkedCircle_apply {t r : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p : ℂ} (hp : p = 0 ∨ p = -1) (hr : 0 < r) (hr' : r ≤ 1 / 5) (u : Circle) :
    ((smallMarkedCircle ht ht' hp hr hr' u : cutDomain t) : ℂ) =
      p + (r : ℂ) * (-Complex.I * (u : ℂ)) := rfl

/-- The whole radial deformation stays in the original cut-and-punctured
source domain, with its positive orientation unchanged. -/
noncomputable def shrinkMarkedCircle {t r : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p : ℂ} (hp : p = 0 ∨ p = -1) (hr : 0 < r) (hr' : r ≤ 1 / 5) :
    (smallMarkedCircle ht ht' hp (by norm_num : (0 : ℝ) < 1 / 5) le_rfl).Homotopy
      (smallMarkedCircle ht ht' hp hr hr') := by
  let R (s : unitInterval) := (1 - (s : ℝ)) * (1 / 5) + (s : ℝ) * r
  have hRpos (s : unitInterval) : 0 < R s := by
    change 0 < (1 - (s : ℝ)) * (1 / 5) + (s : ℝ) * r
    rcases eq_or_lt_of_le s.property.1 with h | h
    · simp [← h]
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr s.property.2) (by norm_num)) (mul_pos h hr)
  have hRle (s : unitInterval) : R s ≤ 1 / 5 := by
    calc
      R s ≤ (1 - (s : ℝ)) * (1 / 5) + (s : ℝ) * (1 / 5) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hr' s.property.1)
      _ = _ := by ring
  have hcont : Continuous R := by unfold R; fun_prop
  refine {
    toFun := fun su ↦ ⟨markedCircleValue p (R su.1) su.2,
      markedCircleValue_mem ht ht' hp (hRpos su.1) (hRle su.1) su.2⟩
    continuous_toFun := Continuous.subtype_mk (by unfold markedCircleValue; fun_prop) _
    map_zero_left := fun u ↦ Subtype.ext (by simp [smallMarkedCircle, R])
    map_one_left := fun u ↦ Subtype.ext (by simp [smallMarkedCircle, R])
  }

/-- At radius one fifth the positively parameterized circle agrees pointwise
with the actual round part of each marked path. -/
theorem round_eq_smallMarkedCircle_positiveLoop {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p : ℂ} (hp : p = 0 ∨ p = -1) (u : unitInterval) :
    round ht ht' hp u =
      smallMarkedCircle ht ht' hp (by norm_num : (0 : ℝ) < 1 / 5) le_rfl
        (positiveCircleLoop u) := by
  apply Subtype.ext
  change circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * (u : ℝ)) =
    markedCircleValue p (1 / 5) (positiveCircleLoop u)
  unfold circleMap markedCircleValue
  have he : (positiveCircleLoop u : ℂ) = Complex.exp (((2 * Real.pi * (u : ℝ) : ℝ) : ℂ) * Complex.I) := rfl
  rw [he]
  simp only [Complex.ofReal_add,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, add_mul, Complex.exp_add,
    ← neg_div, Complex.exp_neg_pi_div_two_mul_I]

end BelgianChocolate.FirstAnnulusPaths
