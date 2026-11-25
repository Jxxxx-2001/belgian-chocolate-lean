import SlitSquareRootBoundary
import SlitBoundaryGeometry

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Filter Topology
open scoped unitInterval
open BelgianChocolate.SlitSquareRoot

theorem upperArc_im_nonneg (u : I) : 0 ≤ (upperArc u).im := by
  have hs : 0 ≤ Real.sin (Real.pi * (u : ℝ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (mul_nonneg Real.pi_pos.le u.property.1) (by nlinarith [u.property.2, Real.pi_pos])
  change 0 ≤ (upperPoint (Real.pi * (u : ℝ))).im
  simpa [upperPoint, Complex.mul_im, Complex.exp_mul_I, ← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_sin] using
    mul_nonneg (Real.exp_pos (-Real.sqrt ((Real.pi * (u : ℝ)) *
      (Real.pi - Real.pi * (u : ℝ))))).le hs

theorem lowerArc_im_neg {u : I} (hu : u ∈ Ioo (0 : I) 1) : (lowerArc u).im < 0 := by
  have h0 : 0 < (u : ℝ) := hu.1
  have h1 : (u : ℝ) < 1 := hu.2
  have hs : 0 < Real.sin (Real.pi * (u : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (by nlinarith [Real.pi_pos])
  simpa [lowerArc, Complex.exp_mul_I, Real.sin_neg, ← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_sin] using neg_lt_zero.mpr hs

theorem upperArc_unfolding_target {α : ℝ} (hα : -1 ≤ α) :
    Tendsto (fun u : I => unfolding α (upperArc u)) (𝓝 1)
      (𝓝 ((Real.sqrt (1 + α) : ℂ) * Complex.I)) := by
  apply tendsto_unfolding_upper_at_neg_one hα
  · simpa only [upperArc.target] using upperArc.continuous.tendsto (1 : I)
  · exact Eventually.of_forall upperArc_im_nonneg

theorem lowerArc_unfolding_target {α : ℝ} (hα : -1 ≤ α) :
    Tendsto (fun u : I => unfolding α (lowerArc u)) (𝓝[Ioo (0 : I) 1] 1)
      (𝓝 (-(Real.sqrt (1 + α) : ℂ) * Complex.I)) := by
  apply tendsto_unfolding_lower_at_neg_one hα
  · have ht := lowerArc.continuous.tendsto (1 : I)
    rw [lowerArc.target] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact lowerArc_im_neg hu

#print axioms upperArc_unfolding_target
#print axioms lowerArc_unfolding_target
end BelgianChocolate.SlitBoundaryGeometry
