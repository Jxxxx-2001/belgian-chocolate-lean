import SlitOuterVariation
import SlitMassContinuity

namespace BelgianChocolate.SlitHarmonicMeasure
open Complex Set
open BelgianChocolate.SlitBoundaryGeometry

/-- Continuity and strict monotonicity hold for every choice of the centered
charts throughout the slit parameter interval. -/
theorem variation_of_centered_charts {F : ℝ → ℂ → ℂ}
    (hF : ∀ α ∈ Ioo (-1 : ℝ) 0, CenteredUnfoldedChart α (F α)) :
    ContinuousOn (fun α => a α (F α)) (Ioo (-1 : ℝ) 0) ∧
    ContinuousOn (fun α => b α (F α)) (Ioo (-1 : ℝ) 0) ∧
    ContinuousOn (fun α => d α (F α)) (Ioo (-1 : ℝ) 0) ∧
    StrictAntiOn (fun α => a α (F α)) (Ioo (-1 : ℝ) 0) ∧
    StrictMonoOn (fun α => b α (F α)) (Ioo (-1 : ℝ) 0) ∧
    StrictAntiOn (fun α => d α (F α)) (Ioo (-1 : ℝ) 0) := by
  let S := Ioo (-1 : ℝ) 0
  have hu {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hlt : x < y) :=
    upper_mass_variation hx.1 hlt hy.2 (hF _ hx) (hF _ hy)
  have hd {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hlt : x < y) :=
    lower_mass_variation hx.1 hlt hy.2 (hF _ hx) (hF _ hy)
  have ca : ContinuousOn (fun α => a α (F α)) S :=
    continuousOn_of_slit_modulus (fun _ hx _ hy hlt =>
      ⟨sub_nonneg.2 (hu hx hy hlt).1.le, (hu hx hy hlt).2⟩)
  have cd : ContinuousOn (fun α => d α (F α)) S :=
    continuousOn_of_slit_modulus (fun _ hx _ hy hlt =>
      ⟨sub_nonneg.2 (hd hx hy hlt).1.le, (hd hx hy hlt).2⟩)
  have total {x : ℝ} (hx : x ∈ S) := a_add_b_add_d (hF _ hx) hx.1 hx.2
  have cb : ContinuousOn (fun α => b α (F α)) S := by
    apply ((continuousOn_const (c := (1 : ℝ))).sub (ca.add cd)).congr
    intro x hx
    change b x (F x) = 1-(a x (F x)+d x (F x))
    linarith [total hx]
  refine ⟨ca,cb,cd,fun _ hx _ hy hlt => (hu hx hy hlt).1,?_,fun _ hx _ hy hlt => (hd hx hy hlt).1⟩
  intro x hx y hy hlt
  dsimp
  linarith [total hx,total hy,(hu hx hy hlt).1,(hd hx hy hlt).1]

end BelgianChocolate.SlitHarmonicMeasure
