import UnfoldedSlitPrimeEnds
import Mathlib.Analysis.Complex.Poisson

/-! Harmonic measure at the physical origin of the candidate slit domains. -/
namespace BelgianChocolate.SlitHarmonicMeasure
open Complex Metric Set MeasureTheory
open scoped ENNReal
open BelgianChocolate.SlitBoundaryGeometry BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex

/-- The centered boundary chart in physical coordinates. -/
noncomputable def physicalAngle (α : ℝ) (F : ℂ → ℂ) (θ : ℝ) : ℂ :=
  folding α (F (circleMap 0 1 θ))

/-- The set of angles in a single period whose physical boundary value lies in E. -/
noncomputable def angularSet (α : ℝ) (F : ℂ → ℂ) (E : Set ℂ) : Set ℝ :=
  Ioc 0 (2 * Real.pi) ∩ physicalAngle α F ⁻¹' E

/-- The harmonic measure represented by a Riemann map centered at the origin. -/
noncomputable def mass (α : ℝ) (F : ℂ → ℂ) (E : Set ℂ) : ℝ :=
  (volume (angularSet α F E)).toReal / (2 * Real.pi)

theorem continuous_physicalAngle {α : ℝ} {F : ℂ → ℂ} (h : CenteredUnfoldedChart α F) :
    Continuous (physicalAngle α F) := by
  unfold physicalAngle
  apply (differentiable_folding α).continuous.comp
  apply h.closed_continuous.comp_continuous
  · fun_prop [circleMap]
  · intro θ
    exact sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (zero_le_one' ℝ) θ)

theorem measurableSet_angularSet {α : ℝ} {F : ℂ → ℂ} {E : Set ℂ}
    (h : CenteredUnfoldedChart α F) (hE : MeasurableSet E) :
    MeasurableSet (angularSet α F E) :=
  measurableSet_Ioc.inter ((continuous_physicalAngle h).measurable hE)

private theorem volume_period_ne_top (α : ℝ) (F : ℂ → ℂ) (E : Set ℂ) :
    volume (angularSet α F E) ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (measure_mono inter_subset_left)
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

theorem mass_nonneg (α : ℝ) (F : ℂ → ℂ) (E : Set ℂ) : 0 ≤ mass α F E :=
  div_nonneg ENNReal.toReal_nonneg (by positivity)

theorem mass_univ (α : ℝ) (F : ℂ → ℂ) : mass α F univ = 1 := by
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [mass, angularSet, preimage_univ, inter_univ, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hπ.le, div_self hπ.ne']

theorem mass_mono {α : ℝ} {F : ℂ → ℂ} {E G : Set ℂ} (h : E ⊆ G) :
    mass α F E ≤ mass α F G := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact ENNReal.toReal_mono (volume_period_ne_top α F G)
    (measure_mono fun _ hx ↦ ⟨hx.1, h hx.2⟩)

theorem mass_union {α : ℝ} {F : ℂ → ℂ} {E G : Set ℂ}
    (h : CenteredUnfoldedChart α F) (hG : MeasurableSet G) (hd : Disjoint E G) :
    mass α F (E ∪ G) = mass α F E + mass α F G := by
  have h₁ : angularSet α F (E ∪ G) = angularSet α F E ∪ angularSet α F G := by
    simp [angularSet, inter_union_distrib_left]
  have h₂ : Disjoint (angularSet α F E) (angularSet α F G) := by
    refine Set.disjoint_left.mpr fun θ hθE hθG ↦ ?_
    exact Set.disjoint_left.mp hd hθE.2 hθG.2
  rw [mass, h₁, measure_union h₂ (measurableSet_angularSet h hG),
    ENNReal.toReal_add (volume_period_ne_top α F E) (volume_period_ne_top α F G), add_div]
  rfl

theorem circleIntegrable_physicalIndicator {α : ℝ} {F : ℂ → ℂ} {E : Set ℂ}
    (h : CenteredUnfoldedChart α F) (hE : MeasurableSet E) :
    CircleIntegrable (fun ζ ↦ E.indicator (fun _ ↦ (1 : ℝ)) (folding α (F ζ))) 0 1 := by
  rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  have hm : MeasurableSet (physicalAngle α F ⁻¹' E) := (continuous_physicalAngle h).measurable hE
  change IntegrableOn ((physicalAngle α F ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)))
    (Ioc 0 (2 * Real.pi))
  have : IsFiniteMeasure (volume.restrict (Ioc 0 (2 * Real.pi))) := by infer_instance
  exact (integrable_const _).indicator hm

theorem mass_eq_circleAverage {α : ℝ} {F : ℂ → ℂ} {E : Set ℂ}
    (h : CenteredUnfoldedChart α F) (hE : MeasurableSet E) :
    mass α F E =
      Real.circleAverage (fun ζ ↦ E.indicator (fun _ ↦ (1 : ℝ)) (folding α (F ζ))) 0 1 := by
  have hpre : MeasurableSet (physicalAngle α F ⁻¹' E) := (continuous_physicalAngle h).measurable hE
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity)]
  change _ = _ * ∫ θ in Ioc 0 (2 * Real.pi),
    (physicalAngle α F ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) θ
  rw [integral_indicator hpre, Measure.restrict_restrict hpre, integral_const]
  simp [mass, angularSet, inter_comm, div_eq_inv_mul, measureReal_def]

theorem mass_subadd {α : ℝ} {F : ℂ → ℂ} (E G : Set ℂ) :
    mass α F (E ∪ G) ≤ mass α F E + mass α F G := by
  have he : angularSet α F (E ∪ G) = angularSet α F E ∪ angularSet α F G := by
    simp [angularSet, inter_union_distrib_left]
  unfold mass
  rw [he, ← add_div, ← ENNReal.toReal_add (volume_period_ne_top α F E)
    (volume_period_ne_top α F G)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨volume_period_ne_top α F E, volume_period_ne_top α F G⟩) (measure_union_le _ _)

/-- A folded singleton has zero angular mass, including the two ends over `-1`. -/
theorem mass_singleton {α : ℝ} {F : ℂ → ℂ} (h : CenteredUnfoldedChart α F) (z : ℂ) :
    mass α F {z} = 0 := by
  have hn := (h.finite_folded_fiber z).countable.preimage_circleMap (0 : ℂ) one_ne_zero
  have hsub : angularSet α F {z} ⊆
      circleMap (0 : ℂ) 1 ⁻¹' (sphere (0 : ℂ) 1 ∩ (folding α ∘ F) ⁻¹' {z}) := by
    intro θ hθ
    exact ⟨circleMap_mem_sphere _ zero_le_one θ, hθ.2⟩
  rw [mass, (hn.mono hsub).measure_zero volume, ENNReal.toReal_zero, zero_div]

theorem mass_eq_one_of_boundary_subset {α : ℝ} {F : ℂ → ℂ} {E : Set ℂ}
    (hs : MapsTo (folding α ∘ F) (sphere (0 : ℂ) 1) E) : mass α F E = 1 := by
  have he : angularSet α F E = angularSet α F univ := by
    ext θ
    simp only [angularSet, mem_inter_iff, preimage_univ, mem_univ, and_true]
    exact ⟨And.left, fun hθ ↦ ⟨hθ, hs (circleMap_mem_sphere _ zero_le_one θ)⟩⟩
  rw [mass, he]
  exact mass_univ α F

theorem mass_pos_of_isOpen_hit {α : ℝ} {F : ℂ → ℂ} {E U : Set ℂ}
    (h : CenteredUnfoldedChart α F) (hU : IsOpen U)
    (hUE : ∀ ζ ∈ sphere (0 : ℂ) 1, folding α (F ζ) ∈ U → folding α (F ζ) ∈ E)
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) (hζU : folding α (F ζ) ∈ U) :
    0 < mass α F E := by
  have hmem : ζ ∈ circleMap (0 : ℂ) 1 '' Ioc 0 (2 * Real.pi) := by
    simpa only [image_circleMap_Ioc, abs_one] using hζ
  obtain ⟨θ,hθ,rfl⟩ := hmem
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp
    (hU.preimage (continuous_physicalAngle h)) θ hζU
  let l := max 0 (θ - ε)
  have hlt : l < θ := max_lt hθ.1 (sub_lt_self _ hε)
  have hsub : Ioo l θ ⊆ angularSet α F E := by
    intro t ht
    have ht₁ : t ∈ Ioc (0 : ℝ) (2 * Real.pi) :=
      ⟨(le_max_left ..).trans_lt ht.1, ht.2.le.trans hθ.2⟩
    have ht₂ : t ∈ ball θ ε := by
      rw [mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]
      have hb := (le_max_right 0 (θ - ε)).trans_lt ht.1
      linarith
    exact ⟨ht₁, hUE _ (circleMap_mem_sphere _ zero_le_one _) (hball ht₂)⟩
  have hm : 0 < volume (angularSet α F E) :=
    (isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hlt)).trans_le (measure_mono hsub)
  exact div_pos (ENNReal.toReal_pos hm.ne' (volume_period_ne_top α F E)) (by positivity)

private theorem upper_im_pos {w : ℂ} (hw : w ∈ MarkedRealAxis.curvedEdge) : 0 < w.im := by
  obtain ⟨θ,hθ,rfl⟩ := hw
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero,
    Complex.exp_im, Complex.mul_I_re, neg_zero, Real.exp_zero, Complex.I_im, mul_one, one_mul]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

private theorem lower_im_neg {w : ℂ} (hw : w ∈ lowerEdge) : w.im < 0 := by
  obtain ⟨θ,hθ,rfl⟩ := hw
  simpa [Complex.exp_mul_I, ← Complex.ofReal_neg, ← Complex.ofReal_sin, Real.sin_neg] using
    neg_lt_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

private theorem ends_im_zero {w : ℂ} (hw : w ∈ ({1,-1} : Set ℂ)) : w.im = 0 := by
  rcases hw with rfl | rfl <;> simp

private theorem curvedEdge_eq_frontier_inter :
    MarkedRealAxis.curvedEdge = frontier radialDomain ∩ {w | 0 < w.im} := by
  ext w
  rw [frontier_radialDomain]
  refine ⟨fun hw ↦ ⟨Or.inl (Or.inr hw), upper_im_pos hw⟩, ?_⟩
  rintro ⟨(hw | hw) | hw, hp⟩
  · exact False.elim (hp.ne' (ends_im_zero hw))
  · exact hw
  · exact False.elim ((lower_im_neg hw).not_gt hp)

private theorem lowerEdge_eq_frontier_inter :
    lowerEdge = frontier radialDomain ∩ {w | w.im < 0} := by
  ext w
  rw [frontier_radialDomain]
  refine ⟨fun hw ↦ ⟨Or.inr hw, lower_im_neg hw⟩, ?_⟩
  rintro ⟨(hw | hw) | hw, hp⟩
  · exact False.elim (hp.ne (ends_im_zero hw))
  · exact False.elim ((upper_im_pos hw).not_gt hp)
  · exact hw

private theorem measurableSet_lowerEdge : MeasurableSet lowerEdge := by
  rw [lowerEdge_eq_frontier_inter]
  exact isClosed_frontier.measurableSet.inter
    ((isOpen_lt Complex.continuous_im continuous_const).measurableSet)

private theorem measurableSet_negativeSlit (α : ℝ) : MeasurableSet (negativeSlit α) := by
  have hf : negativeSlit α =
      {w : ℂ | w.im = 0} ∩ ({w : ℂ | -1 ≤ w.re} ∩ {w : ℂ | w.re ≤ α}) := rfl
  rw [hf]
  exact (isClosed_eq Complex.continuous_im continuous_const).measurableSet.inter
    ((isClosed_le continuous_const Complex.continuous_re).measurableSet.inter
      (isClosed_le Complex.continuous_re continuous_const).measurableSet)

/-- Upper curved edge harmonic measure at zero. -/
noncomputable def a (α : ℝ) (F : ℂ → ℂ) : ℝ := mass α F MarkedRealAxis.curvedEdge
/-- Combined slit-bank harmonic measure at zero. -/
noncomputable def b (α : ℝ) (F : ℂ → ℂ) : ℝ := mass α F (negativeSlit α)
/-- Lower semicircle harmonic measure at zero. -/
noncomputable def d (α : ℝ) (F : ℂ → ℂ) : ℝ := mass α F lowerEdge

/-- The three boundary pieces partition harmonic measure. The remaining physical
endpoints have zero mass. -/
theorem a_add_b_add_d {α : ℝ} {F : ℂ → ℂ} (h : CenteredUnfoldedChart α F)
    (hl : -1 < α) (hr : α < 0) : a α F + b α F + d α F = 1 := by
  have hab : Disjoint MarkedRealAxis.curvedEdge (negativeSlit α) :=
    Set.disjoint_left.mpr fun _ hc hs ↦ (upper_im_pos hc).ne' hs.1
  have habd : Disjoint (MarkedRealAxis.curvedEdge ∪ negativeSlit α) lowerEdge := by
    refine Set.disjoint_left.mpr fun z hz hd ↦ ?_
    rcases hz with hc | hs
    · exact (lower_im_neg hd).not_gt (upper_im_pos hc)
    · exact (lower_im_neg hd).ne hs.1
  let E := MarkedRealAxis.curvedEdge ∪ negativeSlit α ∪ lowerEdge
  have he : mass α F E = a α F + b α F + d α F := by
    simp only [E, mass_union h measurableSet_lowerEdge habd,
      mass_union h (measurableSet_negativeSlit α) hab, a, b, d]
  have hcover : MapsTo (folding α ∘ F) (sphere (0 : ℂ) 1) (E ∪ {1,-1}) := by
    intro ζ hζ
    have hx : (folding α ∘ F) ζ ∈ frontier radialDomain ∪ negativeSlit α := by
      rw [← h.physical_boundary_image hl hr]
      exact mem_image_of_mem _ hζ
    rw [frontier_radialDomain] at hx
    rcases hx with ((he | ha) | hd) | hb
    · exact Or.inr he
    · exact Or.inl (Or.inl (Or.inl ha))
    · exact Or.inl (Or.inr hd)
    · exact Or.inl (Or.inl (Or.inr hb))
  have hz : mass α F ({1,-1} : Set ℂ) = 0 := by
    apply le_antisymm _ (mass_nonneg ..)
    rw [show ({1,-1} : Set ℂ) = {1} ∪ {-1} by ext; simp [or_comm]]
    simpa only [mass_singleton h, add_zero] using mass_subadd (α := α) (F := F) {1} {-1}
  apply le_antisymm
  · rw [← he, ← mass_univ α F]
    exact mass_mono (subset_univ E)
  · have hle := mass_subadd (α := α) (F := F) E {1,-1}
    rwa [mass_eq_one_of_boundary_subset hcover, hz, add_zero, he] at hle

theorem curvedEdge_subset_frontier : MarkedRealAxis.curvedEdge ⊆ frontier radialDomain := by
  rw [curvedEdge_eq_frontier_inter]
  exact inter_subset_left

theorem lowerEdge_subset_frontier : lowerEdge ⊆ frontier radialDomain := by
  rw [lowerEdge_eq_frontier_inter]
  exact inter_subset_left

theorem curvedEdge_measurableSet : MeasurableSet MarkedRealAxis.curvedEdge := by
  rw [curvedEdge_eq_frontier_inter]
  exact isClosed_frontier.measurableSet.inter
    ((isOpen_lt continuous_const Complex.continuous_im).measurableSet)

theorem lowerEdge_measurableSet : MeasurableSet lowerEdge :=
  measurableSet_lowerEdge

end BelgianChocolate.SlitHarmonicMeasure


