import SlitBalanceVariation

open Complex Metric Set Filter
open scoped Topology

namespace BelgianChocolate.SlitHarmonicMeasure

/-- The moving-tip estimate gives a two-sided modulus on the open parameter interval. -/
theorem continuousOn_of_slit_modulus {f : ℝ → ℝ}
    (h : ∀ x ∈ Ioo (-1 : ℝ) 0, ∀ y ∈ Ioo (-1 : ℝ) 0, x < y →
      0 ≤ f x - f y ∧ f x - f y ≤
        2*Real.sqrt (y-x)/(Real.sqrt (y-x)+Real.sqrt (-y))) :
    ContinuousOn f (Ioo (-1 : ℝ) 0) := by
  intro x hx
  let u := fun y : ℝ => Real.sqrt |y-x|
  let v := fun y : ℝ => Real.sqrt (-max x y)
  have hu : Continuous u := by dsimp [u]; fun_prop
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hd : u x + v x ≠ 0 := by
    simp [u,v,(Real.sqrt_pos.2 (neg_pos.2 hx.2)).ne']
  have hc := (((continuous_const (y := (2 : ℝ))).mul hu).continuousAt (x := x)).div
    ((hu.add hv).continuousAt) hd
  have hzero : Tendsto (fun y => 2*u y/(u y+v y)) (𝓝[Ioo (-1 : ℝ) 0] x) (𝓝 0) := by
    have hft : Tendsto (fun y => 2*u y/(u y+v y)) (𝓝[Ioo (-1 : ℝ) 0] x) (𝓝 (2*u x/(u x+v x))) := hc.continuousWithinAt.tendsto
    simpa only [show 2*u x/(u x+v x)=0 by simp [u]] using hft
  apply (tendsto_iff_dist_tendsto_zero).2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Eventually.of_forall fun _ => dist_nonneg)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rcases lt_trichotomy y x with hlt | rfl | hgt
  · obtain ⟨hn,hm⟩ := h y hy x hx hlt
    simpa [Real.dist_eq,abs_of_nonneg hn,u,v,abs_of_neg (sub_neg.2 hlt),
      max_eq_left hlt.le,neg_sub] using hm
  · simp [u]
  · obtain ⟨hn,hm⟩ := h x hx y hy hgt
    rw [dist_comm,Real.dist_eq,abs_of_nonneg hn]
    simpa [u,v,abs_of_pos (sub_pos.2 hgt),max_eq_right hgt.le] using hm

end BelgianChocolate.SlitHarmonicMeasure



