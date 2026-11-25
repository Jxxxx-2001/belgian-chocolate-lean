import SlitBalanceVariation
import SlitBoundaryMean

namespace BelgianChocolate.SlitHarmonicMeasure

open Complex Metric Set MeasureTheory Filter
open BelgianChocolate.SlitBoundaryGeometry BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A transfer of the disk harmonic extension to the enlarged slit. Its boundary
average splits into the new outer-side mass and a positive contribution on the added cut. -/
theorem mass_outer_transfer {α β : ℝ} {A B G H : ℂ → ℂ} {E : Set ℂ}
    (hl : -1 < α) (hab : α < β) (hr : β < 0)
    (ha : CenteredUnfoldedChart α A) (hb : CenteredUnfoldedChart β B)
    (hE : MeasurableSet E) (hout : E ⊆ frontier radialDomain)
    (hG : DifferentiableOn ℂ G (ball 0 1)) (hc : ContinuousOn G (closedBall 0 1))
    (hg : MapsTo G (ball 0 1) (ball 0 1))
    (hgc : MapsTo G (closedBall 0 1) (closedBall 0 1)) (hg0 : G 0 = 0)
    (hid : ∀ z ∈ closedBall (0 : ℂ) 1, folding α (A (G z)) = folding β (B z))
    (hH : DifferentiableOn ℂ H (ball 0 1))
    (hbnd : ∀ z ∈ ball (0 : ℂ) 1, (H z).re ∈ Ioo (0 : ℝ) 1)
    (hlim : ∀ z ∈ sphere (0 : ℂ) 1, folding α (A z) ∉ ({1,-1} : Set ℂ) →
      Tendsto (fun w => (H w).re) (𝓝[ball 0 1] z)
        (𝓝 (E.indicator (fun _ => (1 : ℝ)) (folding α (A z))))) :
    mass β B E < mass α A E ∧
    mass α A E - mass β B E ≤ 2*Real.sqrt (β-α)/(Real.sqrt (β-α)+Real.sqrt (-β)) := by
  classical
  let D := ball (0 : ℂ) 1
  let P := folding β ∘ B
  let I := fun z : ℂ => E.indicator (fun _ => (1 : ℝ)) (P z)
  let K := D.indicator (fun w : ℂ => (H w).re)
  let k := K ∘ G
  let J := {w : ℂ | w.im = 0 ∧ α ≤ w.re ∧ w.re ≤ β}
  let O := {w : ℂ | w.im = 0 ∧ α < w.re ∧ w.re < β}
  have kbd (w : ℂ) : K w ∈ Icc (0 : ℝ) 1 := by
    by_cases hw : w ∈ D
    · simpa [K, hw] using Set.Ioo_subset_Icc_self (hbnd w hw)
    · simp [K, hw]
  have gout {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) (hi : G z ∈ D) :
      P z ∈ candidateSlit α := by
    change folding β (B z) ∈ candidateSlit α
    rw [← hid z (sphere_subset_closedBall hz)]
    exact ha.folded_interior.2.2.mapsTo hi
  have hbdy {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
      P z ∈ frontier radialDomain ∪ negativeSlit β :=
    hb.physical_boundary_image (hl.trans hab) hr ▸ mem_image_of_mem _ hz
  have int_not_fr {w : ℂ} (hw : w ∈ radialDomain) : w ∉ frontier radialDomain :=
    fun hf => hf.2 (isOpen_radialDomain.interior_eq.symm ▸ hw)
  have gseg {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) (hi : G z ∈ D) : P z ∈ J := by
    have hw := gout hz hi
    have hs := (hbdy hz).resolve_left (int_not_fr hw.1)
    exact ⟨hs.1, le_of_not_ge (fun hh => hw.2 ⟨hs.1,hs.2.1,hh⟩), hs.2.2⟩
  have goint {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) (ho : P z ∈ O) : G z ∈ D := by
    by_contra hn
    have hsp : G z ∈ sphere (0 : ℂ) 1 := mem_sphere.mpr
      ((mem_closedBall.mp (hgc (sphere_subset_closedBall hz))).antisymm (not_lt.mp hn))
    have hbd : P z ∈ frontier radialDomain ∪ negativeSlit α := by
      rw [← ha.physical_boundary_image hl (hab.trans hr)]
      exact ⟨G z,hsp,hid z (sphere_subset_closedBall hz)⟩
    have hrd : P z ∈ radialDomain := by
      change ‖P z‖ < radialRadius (P z)
      have hre : (((P z).re : ℝ) : ℂ) = P z := Complex.ext (by simp) (by simpa using ho.1.symm)
      rw [← hre]
      simp [radialRadius, abs_of_neg (ho.2.2.trans hr)]
      linarith [ho.2.1]
    exact ho.2.1.not_ge ((hbd.resolve_left (int_not_fr hrd)).2.2)
  have exc {γ : ℝ} {F : ℂ → ℂ} (h : CenteredUnfoldedChart γ F) :
      (sphere (0 : ℂ) 1 ∩ (folding γ ∘ F) ⁻¹' ({1,-1} : Set ℂ)).Countable := by
    rw [show ({1,-1} : Set ℂ) = {1} ∪ {-1} by rfl, preimage_union, inter_union_distrib_left]
    exact
      ((h.finite_folded_fiber 1).union (h.finite_folded_fiber (-1))).countable
  have hnorm {z : ℂ} (hz : z ∈ D) : ‖(H z).re‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (hbnd _ hz).1]
    exact (hbnd _ hz).2.le
  have ma : mass α A E = (H 0).re := by
    rw [mass_eq_circleAverage ha hE]
    apply circleAverage_eq_re_of_boundary_limits (exc ha) hH (fun _ hz => hnorm hz)
    exact fun z hz he => hlim z hz (fun hh => he ⟨hz,hh⟩)
  have av : Real.circleAverage (I + k) 0 1 = (H 0).re := by
    conv_rhs => rw [← hg0]
    apply circleAverage_eq_re_of_boundary_limits (exc hb) (hH.comp hG hg)
      (fun _ hz => hnorm (hg hz))
    intro z hz he
    have hcz : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
    have htg : Tendsto G (𝓝[D] z) (𝓝[D] (G z)) :=
      ((hc z hcz).mono ball_subset_closedBall).tendsto_nhdsWithin hg
    by_cases gi : G z ∈ D
    · have hnot : P z ∉ E := fun hh => int_not_fr (gout hz gi).1 (hout hh)
      have ht := (continuous_re.continuousAt.tendsto.comp
        ((hH.continuousOn (G z) gi).tendsto.comp htg))
      simpa [I,k,K,gi,hnot,Function.comp_def] using ht
    · have gs : G z ∈ sphere (0 : ℂ) 1 := mem_sphere.mpr
        ((mem_closedBall.mp (hgc hcz)).antisymm (not_lt.mp gi))
      have ht := (hlim _ gs (fun hh => he ⟨hz,show folding β (B z) ∈ _ from (hid z hcz) ▸ hh⟩)).comp htg
      simpa [I,k,K,gi,Function.comp_def,hid z hcz,P] using ht
  have hK : Measurable K :=
    (continuous_re.comp_continuousOn hH.continuousOn).measurable_piecewise
      continuous_zero.continuousOn measurableSet_ball
  have hcg : Continuous (fun θ : ℝ => G (circleMap 0 1 θ)) :=
    hc.comp_continuous (by fun_prop [circleMap])
      (fun θ => sphere_subset_closedBall (circleMap_mem_sphere _ zero_le_one θ))
  let μ := volume.restrict (Ioc 0 (2*Real.pi))
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hkint : Integrable (fun θ => k (circleMap 0 1 θ)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (hK.comp hcg.measurable).aestronglyMeasurable
    exact ae_of_all _ fun θ => by
      change ‖K (G (circleMap 0 1 θ))‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (kbd _).1]
      exact (kbd _).2
  have hkc : CircleIntegrable k 0 1 := by
    rwa [CircleIntegrable,intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  have hsplit : mass α A E - mass β B E = Real.circleAverage k 0 1 := by
    have hi : CircleIntegrable I 0 1 := circleIntegrable_physicalIndicator hb hE
    have mb : mass β B E = Real.circleAverage I 0 1 := mass_eq_circleAverage hb hE
    rw [ma, ← av, Real.circleAverage_add hi hkc, mb]
    ring
  have kmass : 0 < Real.circleAverage k 0 1 := by
    rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity)]
    apply mul_pos (by positivity)
    apply (integral_pos_iff_support_of_nonneg (fun θ => (kbd _).1) hkint).2
    have hm := mass_added_segment_pos hl hab hr hb
    have hv : 0 < volume (angularSet β B O) := by
      by_contra! hv
      change 0 < (volume (angularSet β B O)).toReal / _ at hm
      simp [le_antisymm hv (bot_le)] at hm
    have hO : MeasurableSet O := (isClosed_eq continuous_im continuous_const).measurableSet.inter
      ((isOpen_lt continuous_const continuous_re).measurableSet.inter
      (isOpen_lt continuous_re continuous_const).measurableSet)
    apply lt_of_lt_of_le hv
    have hs : μ (physicalAngle β B ⁻¹' O) = volume (angularSet β B O) := by
      rw [Measure.restrict_apply ((continuous_physicalAngle hb).measurable hO)]
      simp [angularSet,inter_comm]
    rw [← hs]
    apply measure_mono
    intro θ hθ
    have gi := goint (circleMap_mem_sphere _ zero_le_one θ) hθ
    exact (by simpa [k,K,gi] using (hbnd _ gi).1.ne' : k (circleMap 0 1 θ) ≠ 0)
  refine ⟨by linarith, hsplit.le.trans ?_⟩
  apply le_trans _ (mass_added_segment_le hab hr hb)
  have hJ : MeasurableSet J := (isClosed_eq continuous_im continuous_const).measurableSet.inter
    ((isClosed_le continuous_const continuous_re).measurableSet.inter
      (isClosed_le continuous_re continuous_const).measurableSet)
  rw [mass_eq_circleAverage hb hJ]
  apply Real.circleAverage_mono hkc (circleIntegrable_physicalIndicator hb hJ)
  intro z hz
  have hzs : z ∈ sphere (0 : ℂ) 1 := by simpa using hz
  by_cases gi : G z ∈ D
  · change k z ≤ J.indicator (fun _ => (1 : ℝ)) (P z)
    rw [indicator_of_mem (gseg hzs gi)]
    exact (kbd _).2
  · change K (G z) ≤ J.indicator _ (P z)
    rw [show K (G z) = 0 from indicator_of_notMem gi _]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

end BelgianChocolate.SlitHarmonicMeasure


