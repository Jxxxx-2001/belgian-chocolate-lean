import MarkedRealAxisSlice
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Topology.JordanCurve.Path
import Mathlib.Tactic

/-! Concrete outer Jordan boundary for the balanced-slit candidate.
This file does not construct the slit prime ends or harmonic measure. -/
namespace BelgianChocolate.SlitBoundaryGeometry

open Complex Metric Set unitInterval
open scoped Topology

noncomputable def upperPoint (θ : ℝ) : ℂ :=
  (Real.exp (-Real.sqrt (θ * (Real.pi - θ))) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

@[simp] theorem upperPoint_zero : upperPoint 0 = 1 := by simp [upperPoint]
@[simp] theorem upperPoint_pi : upperPoint Real.pi = -1 := by
  simp [upperPoint, Complex.exp_pi_mul_I]

theorem continuous_upperPoint : Continuous upperPoint := by unfold upperPoint; fun_prop

theorem norm_upperPoint (θ : ℝ) :
    ‖upperPoint θ‖ = Real.exp (-Real.sqrt (θ * (Real.pi - θ))) := by
  simp [upperPoint, Complex.norm_exp, Complex.mul_re]

/-- The curved boundary stays outside the circle of radius `exp(-π/2)`. -/
theorem norm_upperPoint_bounds {θ : ℝ} (hθ : θ ∈ Icc 0 Real.pi) :
    Real.exp (-(Real.pi / 2)) ≤ ‖upperPoint θ‖ ∧ ‖upperPoint θ‖ ≤ 1 := by
  have hp : 0 ≤ θ * (Real.pi - θ) := mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2)
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (θ * (Real.pi - θ))
  have hbound : Real.sqrt (θ * (Real.pi - θ)) ≤ Real.pi / 2 := by
    nlinarith [sq_nonneg (θ - Real.pi / 2), Real.pi_pos]
  rw [norm_upperPoint]
  constructor
  · exact Real.exp_le_exp.mpr (neg_le_neg hbound)
  · simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr hn)

/-- The closed curved arc from `1` to `-1`. -/
noncomputable def upperArc : Path (1 : ℂ) (-1) where
  toFun u := upperPoint (Real.pi * (u : ℝ))
  continuous_toFun := continuous_upperPoint.comp (by fun_prop)
  source' := by simp
  target' := by simp

/-- The closed lower unit semicircle with the same declared endpoints. -/
noncomputable def lowerArc : Path (1 : ℂ) (-1) where
  toFun u := Complex.exp (((-(Real.pi * (u : ℝ))) : ℂ) * Complex.I)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [Complex.exp_neg_pi_mul_I]

private theorem norm_polar (r θ : ℝ) (hr : 0 ≤ r) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  simp [Complex.norm_exp, Complex.mul_re, abs_of_nonneg hr]

private theorem polar_angle_unique {r s θ φ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hθ : θ ∈ Icc 0 Real.pi) (hφ : φ ∈ Icc 0 Real.pi)
    (h : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
      (s : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) : θ = φ := by
  have hrs : r = s := by
    have hn := congrArg norm h
    simpa only [norm_polar _ _ hr.le, norm_polar _ _ hs.le] using hn
  subst s
  have he := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') h
  apply eq_of_circleMap_eq (c := (0 : ℂ)) (R := 1) (by norm_num)
  · rw [abs_lt]
    constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2, Real.pi_pos]
  · simpa [circleMap] using he

theorem upperArc_injective : Function.Injective upperArc := by
  intro u v huv
  have hu : Real.pi * (u : ℝ) ∈ Icc 0 Real.pi :=
    ⟨mul_nonneg Real.pi_pos.le u.property.1, by nlinarith [v.property.2, u.property.2, Real.pi_pos]⟩
  have hv : Real.pi * (v : ℝ) ∈ Icc 0 Real.pi :=
    ⟨mul_nonneg Real.pi_pos.le v.property.1, by nlinarith [v.property.2, Real.pi_pos]⟩
  have hθ := polar_angle_unique (Real.exp_pos _) (Real.exp_pos _) hu hv huv
  apply Subtype.ext
  nlinarith [Real.pi_pos]

@[simp] theorem norm_lowerArc (u : I) : ‖lowerArc u‖ = 1 := by
  simp [lowerArc, Complex.norm_exp, Complex.mul_re]

theorem lowerArc_injective : Function.Injective lowerArc := by
  intro u v huv
  have he : circleMap (0 : ℂ) 1 (-(Real.pi * (u : ℝ))) =
      circleMap 0 1 (-(Real.pi * (v : ℝ))) := by simpa [circleMap, lowerArc] using huv
  have hangle := eq_of_circleMap_eq (by norm_num : (1 : ℝ) ≠ 0) (h := he) (by
    rw [abs_lt]
    constructor <;> nlinarith [u.property.1, u.property.2, v.property.1, v.property.2, Real.pi_pos])
  apply Subtype.ext
  nlinarith [Real.pi_pos]

private theorem upperArc_norm_one_endpoints {u : I} (hu : ‖upperArc u‖ = 1) : u = 0 ∨ u = 1 := by
  change ‖upperPoint (Real.pi * (u : ℝ))‖ = 1 at hu
  rw [norm_upperPoint, ← Real.exp_zero] at hu
  have hu := Real.exp_injective hu
  have hp : 0 ≤ (Real.pi * (u : ℝ)) * (Real.pi - Real.pi * (u : ℝ)) :=
    mul_nonneg (mul_nonneg Real.pi_pos.le u.property.1) (by nlinarith [u.property.2, Real.pi_pos])
  have hs := Real.sq_sqrt hp
  have hprod : (Real.pi * (u : ℝ)) * (Real.pi - Real.pi * (u : ℝ)) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h | h
  · left; apply Subtype.ext; change (u : ℝ) = 0; nlinarith [Real.pi_pos]
  · right; apply Subtype.ext; change (u : ℝ) = 1; nlinarith [Real.pi_pos]

/-- The curved arc and the lower circle meet only at their two endpoints. -/
theorem upper_lower_intersection : range upperArc ∩ range lowerArc = {(1 : ℂ), -1} := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    have hu : ‖upperArc u‖ = 1 := by rw [← hv, norm_lowerArc]
    rcases upperArc_norm_one_endpoints hu with rfl | rfl <;> simp
  · intro z hz
    rcases hz with rfl | rfl
    · exact ⟨⟨0, upperArc.source⟩, ⟨0, lowerArc.source⟩⟩
    · exact ⟨⟨1, upperArc.target⟩, ⟨1, lowerArc.target⟩⟩

/-- The explicit candidate outer boundary is a Jordan curve. -/
theorem candidate_boundary_isJordanCurve : TauCeti.IsJordanCurve (range upperArc ∪ range lowerArc) :=
  TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair
    upperArc_injective lowerArc_injective upper_lower_intersection

/-- The upper path closes exactly the curved edge used by the marking module. -/
theorem range_upperArc : range upperArc = {(1 : ℂ), -1} ∪ MarkedRealAxis.curvedEdge := by
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    by_cases hu₀ : u = 0
    · subst u; simp
    by_cases hu₁ : u = 1
    · subst u; simp
    have hu : (u : ℝ) ∈ Ioo 0 1 := by
      constructor
      · by_contra! h
        apply hu₀
        apply Subtype.ext
        change (u : ℝ) = 0
        linarith [u.property.1]
      · by_contra! h
        apply hu₁
        apply Subtype.ext
        change (u : ℝ) = 1
        linarith [u.property.2]
    right
    refine ⟨Real.pi * (u : ℝ), ⟨mul_pos Real.pi_pos hu.1, ?_⟩, rfl⟩
    simpa only [mul_one] using mul_lt_mul_of_pos_left hu.2 Real.pi_pos
  · intro z hz
    rcases hz with hz | ⟨θ, hθ, rfl⟩
    · rcases hz with rfl | rfl
      · exact ⟨0, upperArc.source⟩
      · exact ⟨1, upperArc.target⟩
    · refine ⟨⟨θ / Real.pi, ⟨(div_pos hθ.1 Real.pi_pos).le,
          (div_le_one Real.pi_pos).mpr hθ.2.le⟩⟩, ?_⟩
      change upperPoint (Real.pi * (θ / Real.pi)) = upperPoint θ
      congr 1
      field_simp

/-- A parameterized open lower unit semicircle, with angle between `-π` and `0`. -/
def lowerEdge : Set ℂ := {w | ∃ θ ∈ Ioo 0 Real.pi,
  w = Complex.exp ((-(θ : ℂ)) * Complex.I)}

theorem range_lowerArc : range lowerArc = {(1 : ℂ), -1} ∪ lowerEdge := by
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    by_cases hu₀ : u = 0
    · subst u; simp
    by_cases hu₁ : u = 1
    · subst u; simp
    have hu : (u : ℝ) ∈ Ioo 0 1 := by
      constructor
      · by_contra! h
        apply hu₀
        apply Subtype.ext
        change (u : ℝ) = 0
        linarith [u.property.1]
      · by_contra! h
        apply hu₁
        apply Subtype.ext
        change (u : ℝ) = 1
        linarith [u.property.2]
    right
    refine ⟨Real.pi * (u : ℝ), ⟨mul_pos Real.pi_pos hu.1, ?_⟩, ?_⟩
    · simpa only [mul_one] using mul_lt_mul_of_pos_left hu.2 Real.pi_pos
    · simp [lowerArc]
  · intro z hz
    rcases hz with hz | ⟨θ, hθ, rfl⟩
    · rcases hz with rfl | rfl
      · exact ⟨0, lowerArc.source⟩
      · exact ⟨1, lowerArc.target⟩
    · refine ⟨⟨θ / Real.pi, ⟨(div_pos hθ.1 Real.pi_pos).le,
          (div_le_one Real.pi_pos).mpr hθ.2.le⟩⟩, ?_⟩
      have hangle : (Real.pi : ℂ) * ((θ : ℂ) / (Real.pi : ℂ)) = (θ : ℂ) := by field_simp
      simp [lowerArc, hangle]

/-- The boundary from the manuscript: the closed curved edge and lower semicircle. -/
theorem manuscript_boundary_isJordanCurve :
    TauCeti.IsJordanCurve ({(1 : ℂ), -1} ∪ MarkedRealAxis.curvedEdge ∪ lowerEdge) := by
  convert candidate_boundary_isJordanCurve using 1
  rw [range_upperArc, range_lowerArc]
  ext z
  simp only [mem_union]
  tauto

#print axioms candidate_boundary_isJordanCurve
#print axioms norm_upperPoint_bounds
end BelgianChocolate.SlitBoundaryGeometry
