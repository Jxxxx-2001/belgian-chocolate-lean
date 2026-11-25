import SlitCayleyAngles
import SlitHalfPlaneDiskChart
import SlitMassChartIndependence
import UnfoldedSlitPhysicalSides

namespace BelgianChocolate.SlitHarmonicMeasure
open Complex Set Metric MeasureTheory Filter
open BelgianChocolate.SlitBoundaryGeometry BelgianChocolate.SlitSquareRoot
open BelgianChocolate.SlitStarConvex BelgianChocolate.NormalizationCenter

private theorem circle_at_angle_ne_one (x : ℝ) : circleMap 0 1 (cayleyAngle x) ≠ 1 := by
  intro he
  have he0 : circleMap (0 : ℂ) 1 (cayleyAngle x) = circleMap 0 1 0 := by rw [he]; simp [circleMap]
  have hb := cayleyAngle_mem x
  have ht := eq_of_circleMap_eq (by norm_num : (1 : ℝ) ≠ 0)
    ((by rw [sub_zero,abs_of_pos hb.1]; exact hb.2 : |cayleyAngle x - 0| < 2*Real.pi)) he0
  exact hb.1.ne' ht

private theorem upper_pos {w : ℂ} (hw : w ∈ MarkedRealAxis.curvedEdge) : 0 < w.im := by
  obtain ⟨θ,hθ,rfl⟩ := hw
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero,
    Complex.exp_im, Complex.mul_I_re, neg_zero, Real.exp_zero, Complex.I_im, mul_one, one_mul]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

/-- With the source center at i, each ray on the marked real line has the
angular length given by the Cayley prevertex. -/
theorem centered_prevertex_masses {α q r : ℝ} {G : ℂ → ℂ}
    (hl : -1 < α) (hr : α < 0) (h : UnfoldedHalfPlaneChart α G)
    (hq : G (q : ℂ) = lowerBankEnd α) (hR : G (r : ℂ) = rightEnd α) :
    a α (halfPlaneDiskChart α G) = (2*Real.pi - cayleyAngle r)/(2*Real.pi) ∧
    b α (halfPlaneDiskChart α G) = cayleyAngle q/(2*Real.pi) := by
  let F := halfPlaneDiskChart α G
  have hqr := h.prevertex_order hl hr hq hR
  obtain ⟨hbank,-,-⟩ := h.trace_three_sides hl hr hq hR
  obtain ⟨-,hlower,hupper⟩ := h.folded_three_sides hl hr hq hR
  have bank {x : ℝ} (hx : x < q) : folding α (G (x : ℂ)) ∈ negativeSlit α := by
    rw [← folding_image_bankPath hl]
    exact ⟨_, hbank x hx,rfl⟩
  have he (x : ℝ) : physicalAngle α F (cayleyAngle x) = folding α (G (x : ℂ)) := by
    unfold physicalAngle F
    rw [halfPlaneDiskChart_regular (circle_at_angle_ne_one x),cayley_circle_at_angle]
  have hs (x : ℝ) (hxq : x ≠ q) (hxr : x ≠ r) :
      (physicalAngle α F (cayleyAngle x) ∈ MarkedRealAxis.curvedEdge ↔ r < x) ∧
      (physicalAngle α F (cayleyAngle x) ∈ negativeSlit α ↔ x < q) := by
    rw [he]
    by_cases hx : x < q
    · have hb := bank hx
      exact ⟨iff_of_false (fun hu => (upper_pos hu).ne' hb.1) (by linarith), iff_of_true hb hx⟩
    by_cases hy : r < x
    · have hu := hupper x hy
      exact ⟨iff_of_true hu hy,iff_of_false (fun hb => (upper_pos hu).ne' hb.1) hx⟩
    have hmid := (hlower x ⟨lt_of_le_of_ne (le_of_not_gt hx) hxq.symm,
      lt_of_le_of_ne (le_of_not_gt hy) hxr⟩).2
    exact ⟨iff_of_false (fun hu => hmid.not_gt (upper_pos hu)) hy,
      iff_of_false (fun hb => hmid.ne hb.1) hx⟩
  have hae : ∀ᵐ θ : ℝ, (θ ∈ angularSet α F MarkedRealAxis.curvedEdge ↔ θ ∈ Ioo (cayleyAngle r) (2*Real.pi)) ∧
      (θ ∈ angularSet α F (negativeSlit α) ↔ θ ∈ Ioo 0 (cayleyAngle q)) := by
    filter_upwards [Measure.ae_ne volume (2*Real.pi), Measure.ae_ne volume (cayleyAngle q),Measure.ae_ne volume (cayleyAngle r)] with θ ht hq' hr'
    by_cases hθ : θ ∈ Ioo 0 (2*Real.pi)
    · obtain ⟨x,_,rfl⟩ := cayleyAngle_surjOn hθ
      have hh := hs x (fun heq => hq' (heq ▸ rfl)) (fun heq => hr' (heq ▸ rfl))
      simp only [angularSet, mem_inter_iff, mem_Ioc, mem_preimage, mem_Ioo, hθ.1, hθ.2.le,hθ.2,
        and_self, true_and, and_true, hh.1,hh.2, cayleyAngle_strictMono.lt_iff_lt]
    · have h0 : θ ∉ Ioc 0 (2*Real.pi) := fun hh => hθ ⟨hh.1,lt_of_le_of_ne hh.2 ht⟩
      have h1 : θ ∉ Ioo (cayleyAngle r) (2*Real.pi) := fun hh => hθ ⟨(cayleyAngle_mem r).1.trans hh.1,hh.2⟩
      have h2 : θ ∉ Ioo 0 (cayleyAngle q) := fun hh => hθ ⟨hh.1,hh.2.trans (cayleyAngle_mem q).2⟩
      simp [angularSet,h0,h1,h2]
  have ma : volume (angularSet α F MarkedRealAxis.curvedEdge) = volume (Ioo (cayleyAngle r) (2*Real.pi)) :=
    measure_congr (hae.mono fun _ hh => propext hh.1)
  have mb : volume (angularSet α F (negativeSlit α)) = volume (Ioo 0 (cayleyAngle q)) :=
    measure_congr (hae.mono fun _ hh => propext hh.2)
  change (_ / _ = _ ∧ _ / _ = _)

  change (volume (angularSet α F _)).toReal / _ = _ ∧ (volume (angularSet α F _)).toReal / _ = _
  rw [ma,mb,Real.volume_Ioo,Real.volume_Ioo,ENNReal.toReal_ofReal (sub_nonneg.mpr (cayleyAngle_mem r).2.le),
    sub_zero,ENNReal.toReal_ofReal (cayleyAngle_mem q).1.le]
  exact ⟨rfl,rfl⟩

end BelgianChocolate.SlitHarmonicMeasure

