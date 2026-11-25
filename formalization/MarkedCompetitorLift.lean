import CuspLiftFilling
import MarkedAxisSlitLift
import MarkedAxisLift
import SecondAnnulusMarking

/-! The marked cusp lift of the original disk competitor on one slit domain. -/

namespace BelgianChocolate.SourceDiskPaths

open Complex Metric Set
open BelgianChocolate.ModularLambdaRatio BelgianChocolate.MarkedAxisSlit

/-- The half-disk lift is holomorphic across every ordinary point of both
real intervals. The zero over it is simple, and both boundary markings
belong to this very same lift. -/
theorem exists_marked_competitor_lift {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hreal : ∀ z ∈ ball (0 : ℂ) 1, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    {d : ℝ} (hder : HasDerivAt f (d : ℂ) 0) (hd : 0 < d) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ slit ∧
      (∀ z ∈ slit, ‖φ z‖ < 1) ∧ (∀ z ∈ slit, cuspU (φ z) = f z) ∧
      φ ((t : ℂ) * I) = 0 ∧ (∃ d', HasDerivAt φ d' ((t : ℂ) * I) ∧ d' ≠ 0) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 0, φ (x : ℂ) ∈ MarkedRealAxis.curvedEdge) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (-1 : ℝ) 0, φ (x : ℂ) = (y : ℂ)) := by
  obtain ⟨e, hre, hz, hp, _⟩ :=
    BelgianChocolate.SecondAnnulus.r19_source_common_lift ht ht' hf hreal hder hd
  obtain ⟨F, ⟨hbase, hF⟩, _⟩ := existsUnique_cuspULift_of_sourceGammaPlus ht ht' hf e hp
  have hF' (z : Domain t) : (cuspUPunctured (F z) : ℂ) = f z :=
    congrArg Subtype.val (congrFun hF z)
  have hlt : t < 1 := by linarith
  have hm := upper_subset_slit (UpperHalfDisk.puncture_mem ht hlt)
  obtain ⟨a, ha, hne⟩ := hf.plus_simple
  obtain ⟨φ, hφF, hdiff, hnorm, hU, hzero, hφder, hφne⟩ :=
    cuspLift_fill_continuous isOpen_slit ((slit_star ht hlt).isPathConnected hm).isConnected.isPreconnected hm
      (hf.holomorphic.mono fun _ hz ↦ mem_ball_zero_iff.mpr hz.1)
      F hF' hf.plus_value ha hne
  have hAxes := lift_marked_real_axes ht ht' hf hreal e hre hz F hbase hF
  have hr (x : ℝ) (hx : ‖(x : ℂ)‖ < 1) (hx₀ : x ≠ 0) :
      (x : ℂ) ∈ slit \ {UpperHalfDisk.puncture t} := by
    refine ⟨⟨hx, Or.inl (by simpa using hx₀)⟩, ?_⟩
    intro he
    have him := congrArg Complex.im he
    simp [UpperHalfDisk.puncture] at him
    linarith
  refine ⟨φ, hdiff, hnorm, hU, hzero, ⟨_, hφder, hφne⟩, ?_, ?_⟩
  · intro x hx
    have hn : ‖(x : ℂ)‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_neg hx.2] using neg_lt.mpr hx.1
    let v : Domain t := ⟨(x : ℂ), hr x hn hx.2.ne⟩
    rw [hφF v]
    exact (hAxes v (by simp [v])).1 (by simpa [v] using hx.2)
  · intro x hx
    have hn : ‖(x : ℂ)‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hx.1] using hx.2
    let v : Domain t := ⟨(x : ℂ), hr x hn hx.1.ne'⟩
    rw [hφF v]
    exact (hAxes v (by simp [v])).2 (by simpa [v] using hx.1)

end BelgianChocolate.SourceDiskPaths