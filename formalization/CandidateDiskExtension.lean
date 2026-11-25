import CandidateReflection
import CandidateSimpleZero

/-! One-sided analytic candidate data imply a real-symmetric marked disk
competitor. In particular neither a disk extension nor zero simplicity is
assumed: both are conclusions of reflection, removability and the cusp sign.
-/
namespace BelgianChocolate.CandidateReflection
open Complex Filter Metric Set Topology
open BelgianChocolate.SourceDiskPaths

theorem fillReflection_marked_of_upper_data {f : ℂ → ℂ} {t : ℝ} (ht : 0 < t)
    (hc : ContinuousOn f ((ball 0 1 \ {0}) ∩ {z : ℂ | 0 ≤ z.im}))
    (hd : DifferentiableOn ℂ f (ball 0 1 ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, z.im = 0 → (f z).im = 0)
    (havoid : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ z.im → z ≠ 0 →
      z ≠ (t : ℂ) * I → f z ∈ ({0,1}ᶜ : Set ℂ))
    (hplus : f ((t : ℂ) * I) = 1)
    (hplusSimple : ∃ d, HasDerivAt f d ((t : ℂ) * I) ∧ d ≠ 0)
    (hlim : Tendsto f (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝 0))
    (hsign : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] 0, 0 < (f z).im) :
    MarkedCompetitor t (fillReflection f) ∧ RealSymmetricOnDisk (fillReflection f) ∧
      (∃ d : ℝ, 0 < d ∧ HasDerivAt (fillReflection f) (d : ℂ) 0) ∧
      EqOn (fillReflection f) f (ball 0 1 ∩ {z : ℂ | 0 < z.im}) := by
  have hD := fillReflection_differentiableOn zero_lt_one hc hd hreal hlim
  have hR : RealSymmetricOnDisk (fillReflection f) := fun _ hz => fillReflection_conj hreal hz
  have hS : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < z.im → 0 < (fillReflection f z).im := by
    filter_upwards [eventually_nhdsWithin_iff.mp hsign] with z hz hi
    rw [fillReflection_upper hi]
    exact hz hi
  obtain ⟨d, hpos, hder⟩ := positive_derivative_of_upper_sign
    (hD.analyticAt (ball_mem_nhds 0 zero_lt_one)) (fillReflection_zero f) hR hS
  have hM := fillReflection_marked_of_simple_zero ht hD hreal havoid hplus hplusSimple
    ⟨(d : ℂ), hder, Complex.ofReal_ne_zero.mpr hpos.ne'⟩
  exact ⟨hM.1, hM.2, ⟨d, hpos, hder⟩, fun _ hz => fillReflection_upper hz.2⟩

end BelgianChocolate.CandidateReflection
