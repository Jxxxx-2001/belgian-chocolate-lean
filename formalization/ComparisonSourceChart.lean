import ComparisonSourceBoundary
import TauCeti.Analysis.Complex.Conformal.Caratheodory
import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
import TauCeti.Analysis.Complex.Conformal.Jordan.Approach

/-! A centered Riemann chart for the physical source half-disc, including
the boundary extension and its injectivity. -/

namespace BelgianChocolate.HarmonicComparison

open Complex Filter Metric Set Topology
open scoped Topology

theorem comparisonHalfDisk_convex : Convex ℝ comparisonHalfDisk :=
  (convex_ball _ _).inter (convex_halfSpace_im_gt 0)

theorem comparisonHalfDisk_bounded : Bornology.IsBounded comparisonHalfDisk :=
  isBounded_ball.subset inter_subset_left

theorem central_point_mem_comparisonHalfDisk {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    (t : ℂ) * Complex.I ∈ comparisonHalfDisk := by
  rw [comparisonHalfDisk_eq_norm]
  exact ⟨by simpa [abs_of_pos ht] using ht', by simpa [Complex.mul_im] using ht⟩

theorem comparisonHalfDisk_jordan : TauCeti.IsJordanDomain comparisonHalfDisk := by
  have hn : comparisonHalfDisk.Nonempty :=
    ⟨_, central_point_mem_comparisonHalfDisk (t := 1 / 2) (by norm_num) (by norm_num)⟩
  refine ⟨isOpen_comparisonHalfDisk, ⟨hn, comparisonHalfDisk_convex.isPreconnected⟩,
    comparisonHalfDisk_bounded, ?_⟩
  apply TauCeti.isJordanCurve_frontier_of_convex comparisonHalfDisk_convex
  · simpa only [isOpen_comparisonHalfDisk.interior_eq] using hn
  · exact comparisonHalfDisk_bounded

/-- Data of a conformal chart used for the marked three-arc comparison. -/
structure CenteredComparisonChart (t : ℝ) (η : ℂ → ℂ) : Prop where
  zero : η 0 = (t : ℂ) * Complex.I
  holomorphic : DifferentiableOn ℂ η (ball 0 1)
  interior_bij : BijOn η (ball 0 1) comparisonHalfDisk
  closed_continuous : ContinuousOn η (closedBall 0 1)
  closed_bij : BijOn η (closedBall 0 1) (closure comparisonHalfDisk)
  frontier_bij : BijOn η (sphere 0 1) (frontier comparisonHalfDisk)

theorem exists_centered_comparisonChart {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    ∃ η : ℂ → ℂ, CenteredComparisonChart t η := by
  have hJ := comparisonHalfDisk_jordan
  let _ : LocallyConnectedSpace (frontier comparisonHalfDisk) :=
    hJ.isJordanCurve_frontier.locallyConnectedSpace
  obtain ⟨η, hc, hd, hbij, hz⟩ :=
    TauCeti.exists_continuousOn_closedBall_bijOn_ball_of_locallyConnectedSpace_frontier_of_mem
      hJ.isOpen hJ.isSimplyConnected hJ.isBounded (central_point_mem_comparisonHalfDisk ht ht')
  have hi : η '' ball 0 1 = comparisonHalfDisk := hbij.image_eq
  have hI : InjOn η (closedBall 0 1) :=
    TauCeti.injOn_closedBall_of_isJordanCurve_frontier (by norm_num) hd hbij.injOn
      (by rw [hi]; exact hJ.isBounded) (by rw [hi]; exact hJ.isJordanCurve_frontier) hc
      (fun _ _ => rfl)
  refine ⟨η, hz, hd, hbij, hc, ?_, ?_⟩
  · have h := TauCeti.bijOn_closure_closure_image (isBounded_ball (x := (0 : ℂ)) (r := 1))
      (by simpa only [closure_ball _ one_ne_zero] using hc) (fun _ _ => rfl)
      (by simpa only [closure_ball _ one_ne_zero] using hI)
    simpa only [closure_ball _ one_ne_zero, hi] using h
  · have hη := TauCeti.image_frontier_eq_frontier_image isOpen_ball
      (isBounded_ball (x := (0 : ℂ)) (r := 1)) hd hbij.injOn
      (by simpa only [closure_ball _ one_ne_zero] using hc) (fun _ _ => rfl)
    rw [frontier_ball _ one_ne_zero, hi] at hη
    rw [← hη]
    exact (hI.mono sphere_subset_closedBall).bijOn_image

/-- The chart sends a subset of the unit circle onto the actual open
semicircular boundary of the half-disc. -/
theorem CenteredComparisonChart.outer_surjOn {t : ℝ} {η : ℂ → ℂ}
    (hη : CenteredComparisonChart t η) :
    SurjOn η (sphere 0 1) comparisonOuterArc := by
  intro q hq
  apply hη.frontier_bij.surjOn
  rw [frontier_comparisonHalfDisk]
  exact Or.inl hq

/-- The seam preimages on the comparison circle form a finite set. -/
theorem CenteredComparisonChart.finite_seams {t : ℝ} {η : ℂ → ℂ}
    (hη : CenteredComparisonChart t η) :
    (sphere (0 : ℂ) 1 ∩ η ⁻¹' comparisonSeams).Finite := by
  apply Set.Finite.of_finite_image ?_ (hη.frontier_bij.injOn.mono inter_subset_left)
  apply comparisonSeams_finite.subset
  rintro _ ⟨z, hz, rfl⟩
  exact hz.2

/-- A point on the comparison circle away from the pulled-back seams belongs
to one of the three physical open boundary pieces, as classified by
the chart value. -/
theorem CenteredComparisonChart.marked_arc_cases {t : ℝ} {η : ℂ → ℂ}
    (hη : CenteredComparisonChart t η) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hs : ζ ∉ sphere (0 : ℂ) 1 ∩ η ⁻¹' comparisonSeams) :
    η ζ ∈ comparisonOuterArc ∨
      η ζ ∈ Complex.ofReal '' Ioo (-1 : ℝ) 0 ∨ η ζ ∈ Complex.ofReal '' Ioo (0 : ℝ) 1 :=
  frontier_comparisonHalfDisk_other (hη.frontier_bij.mapsTo hζ) (fun hh => hs ⟨hζ, hh⟩)

/-- The pulled-back negative real segment excludes the right physical seam
even in its closure. -/
theorem CenteredComparisonChart.negative_arc_no_limit_of_re_pos {t : ℝ} {η : ℂ → ℂ}
    (hη : CenteredComparisonChart t η) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hpos : 0 < (η ζ).re) :
    𝓝[sphere (0 : ℂ) 1 ∩ η ⁻¹' (Complex.ofReal '' Ioo (-1 : ℝ) 0)] ζ = ⊥ := by
  let G := sphere (0 : ℂ) 1 ∩ η ⁻¹' (Complex.ofReal '' Ioo (-1 : ℝ) 0)
  change 𝓝[G] ζ = ⊥
  have hsubset : G ⊆ closedBall (0 : ℂ) 1 := fun _ hz => sphere_subset_closedBall hz.1
  have hlim : Tendsto (fun w => (η w).re) (𝓝[G] ζ) (𝓝 ((η ζ).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      ((hη.closed_continuous ζ (sphere_subset_closedBall hζ)).mono hsubset)
  have hp : ∀ᶠ w in 𝓝[G] ζ, 0 < (η w).re := hlim.eventually (lt_mem_nhds hpos)
  have hn : ∀ᶠ w in 𝓝[G] ζ, (η w).re < 0 := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    obtain ⟨x, hx, he⟩ := hw.2
    rw [← he, Complex.ofReal_re]
    exact hx.2
  by_contra hne
  let _ : NeBot (𝓝[G] ζ) := ⟨hne⟩
  obtain ⟨w, hwp, hwn⟩ := (hp.and hn).exists
  exact (lt_asymm hwp) hwn

theorem CenteredComparisonChart.tendsto_negative_arc {t : ℝ} {η : ℂ → ℂ}
    (hη : CenteredComparisonChart t η) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    Tendsto η (𝓝[sphere (0 : ℂ) 1 ∩ η ⁻¹' (Complex.ofReal '' Ioo (-1 : ℝ) 0)] ζ)
      (𝓝[Complex.ofReal '' Ioo (-1 : ℝ) 0] (η ζ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(hη.closed_continuous ζ (sphere_subset_closedBall hζ)).mono ?_, ?_⟩
  · exact fun _ hw => sphere_subset_closedBall hw.1
  · filter_upwards [self_mem_nhdsWithin] with w hw using hw.2

end BelgianChocolate.HarmonicComparison

