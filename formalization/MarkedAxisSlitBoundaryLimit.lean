import CoveringBoundaryLimit
import MarkedAxisSlit
import ModularLambdaCuspCover

/-! A regular boundary value in the open upper semicircle forces the cusp lift
to approach an interior point of the punctured unit disc. -/

namespace BelgianChocolate.MarkedAxisSlit

open Complex Filter Metric Set Topology
open BelgianChocolate.ModularLambdaRatio
open scoped Topology

theorem cuspULift_tendsto_of_regular_boundary {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (F : C(Domain t, PuncturedUnitDisc))
    {a v : ℂ} (ha : ‖a‖ = 1) (haSlit : a.re ≠ 0 ∨ 0 < a.im) (hv : v ∈ ({0,1}ᶜ : Set ℂ))
    (hF : Tendsto (fun z => (cuspUPunctured (F z) : ℂ))
      (comap (Subtype.val : Domain t → ℂ) (𝓝 a)) (𝓝 v)) :
    ∃ e : PuncturedUnitDisc, cuspU e = v ∧
      Tendsto F (comap (Subtype.val : Domain t → ℂ) (𝓝 a)) (𝓝 e) := by
  let S := slit \ {UpperHalfDisk.puncture t}
  let W : Set ℂ := ({z : ℂ | z.re ≠ 0} ∪ {z : ℂ | 0 < z.im}) \ {UpperHalfDisk.puncture t}
  have hW : IsOpen W :=
    ((isOpen_ne_fun continuous_re continuous_const).union
      (isOpen_lt continuous_const continuous_im)).sdiff isClosed_singleton
  have hpNorm : ‖UpperHalfDisk.puncture t‖ = t := by simp [UpperHalfDisk.puncture, abs_of_pos ht]
  have haW : a ∈ W := by
    refine ⟨haSlit, ?_⟩
    intro he
    have h : a = UpperHalfDisk.puncture t := he
    rw [h, hpNorm] at ha
    exact ht1.ne ha
  have hsub : W ∩ ball (0 : ℂ) 1 ⊆ S := fun _ hz =>
    ⟨⟨mem_ball_zero_iff.mp hz.2, hz.1.1⟩, hz.1.2⟩
  have haBall : a ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball 0 one_ne_zero, mem_closedBall_zero_iff, ha]
  have haS : a ∈ closure S := closure_mono hsub (hW.inter_closure ⟨haW, haBall⟩)
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds haW)
  have hcap (R : ℝ) (hR : 0 < R) :
      ∃ r ∈ Ioo 0 R, IsPreconnected (S ∩ ball a r) := by
    let r := min (R / 2) δ
    have hr : 0 < r := lt_min (half_pos hR) hδ
    refine ⟨r, ⟨hr, (min_le_left ..).trans_lt (half_lt_self hR)⟩, ?_⟩
    have hW' : ball a r ⊆ W := (ball_subset_ball (min_le_right .. : r ≤ δ)).trans hδW
    have HS : S ∩ ball a r = ball (0 : ℂ) 1 ∩ ball a r := by
      apply Set.Subset.antisymm
      · rintro z ⟨hz, har⟩
        exact ⟨mem_ball_zero_iff.mpr hz.1.1, har⟩
      · rintro z ⟨hz, har⟩
        exact ⟨hsub ⟨hW' har, hz⟩, har⟩
    rw [HS]
    exact ((convex_ball (0 : ℂ) 1).inter (convex_ball a r)).isPreconnected
  let y : ({0,1}ᶜ : Set ℂ) := ⟨v, hv⟩
  have hproj : Tendsto (cuspUPunctured ∘ F) (comap (Subtype.val : S → ℂ) (𝓝 a)) (𝓝 y) :=
    IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr hF
  obtain ⟨e, he, hlim⟩ :=
    cuspUPunctured_isCoveringMap.exists_tendsto_at_boundary_of_preconnected_caps F haS hcap hproj
  exact ⟨e, (cuspUPunctured_coe e).symm.trans (congrArg Subtype.val he), hlim⟩

#print axioms cuspULift_tendsto_of_regular_boundary

end BelgianChocolate.MarkedAxisSlit

