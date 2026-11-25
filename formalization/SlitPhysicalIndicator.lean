import SlitArcIndicator
import SlitHarmonicMeasure
import UnfoldedSlitPhysicalSides
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

/-! Holomorphic indicator traces for the actual upper and lower slit boundary. -/

namespace BelgianChocolate.SlitHarmonicMeasure

open Complex Set Metric Filter Bornology UpperHalfPlane
open BelgianChocolate.SlitArcIndicator BelgianChocolate.SlitBoundaryGeometry
open BelgianChocolate.SlitSquareRoot BelgianChocolate.SlitStarConvex
open scoped Topology

private theorem trace_inverse {ι : Type*} {l : Filter ι} {α : ℝ} {G : ℂ → ℂ}
    (hG : UnfoldedHalfPlaneChart α G) {g : ι → ℂ} {x : ℂ} (hx : 0 ≤ x.im)
    (hmem : ∀ᶠ z in l, 0 ≤ (g z).im) (ht : Tendsto (G ∘ g) l (𝓝 (G x))) :
    Tendsto g l (𝓝 x) := by
  have hp : G x ≠ upperBankEnd α := (hG.closed_bij.mapsTo hx).2
  have hdp : 0 < dist (G x) (upperBankEnd α) := dist_pos.mpr hp
  let εp := dist (G x) (upperBankEnd α) / 2
  have hεp : 0 < εp := half_pos hdp
  have hfar := eventually_inf_principal.mp (hG.at_infty (ball_mem_nhds _ hεp))
  obtain ⟨R, _, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).mem_iff.mp hfar
  have hbounded : ∀ᶠ z in l, g z ∈ closedBall (0 : ℂ) R := by
    filter_upwards [hmem, ht (ball_mem_nhds (G x) hεp)] with z hz hnear
    by_contra h
    have hzfar := hR h hz
    have htriangle := dist_triangle (G x) (G (g z)) (upperBankEnd α)
    change dist (G (g z)) (G x) < εp at hnear
    change dist (G (g z)) (upperBankEnd α) < εp at hzfar
    rw [dist_comm (G x) (G (g z))] at htriangle
    exact (not_lt_of_ge htriangle) (by dsimp [εp] at *; linarith)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K := (closedBall (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im}) ∩ (ball x ε)ᶜ
  have hK : IsCompact K := by
    rw [show K = closedBall (0 : ℂ) R ∩ ({z : ℂ | 0 ≤ z.im} ∩ (ball x ε)ᶜ) from
      inter_assoc ..]
    exact (isCompact_closedBall _ _).inter_right
      ((isClosed_le continuous_const Complex.continuous_im).inter isOpen_ball.isClosed_compl)
  have hs : K ⊆ {z : ℂ | 0 ≤ z.im} := fun _ hz => hz.1.2
  have himage := (hK.image_of_continuousOn (hG.cont.mono hs)).isClosed
  have hxout : G x ∉ G '' K := by
    rintro ⟨y, hy, he⟩
    have heq := hG.closed_bij.injOn (hs hy) hx he
    exact hy.2 (heq.symm ▸ mem_ball_self hε)
  filter_upwards [hmem, hbounded,
    ht (himage.isOpen_compl.mem_nhds hxout)] with z hz hzr himg
  by_contra hfar'
  exact himg ⟨g z, ⟨⟨hzr, hz⟩, hfar'⟩, rfl⟩

private theorem upper_im_of_curved {z : ℂ} (hz : z ∈ MarkedRealAxis.curvedEdge) : 0 < z.im := by
  obtain ⟨θ,hθ,rfl⟩ := hz
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero,
    Complex.exp_im, Complex.mul_I_re, neg_zero, Real.exp_zero, Complex.I_im, mul_one, one_mul]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

private theorem lower_im_of_lower {z : ℂ} (hz : z ∈ lowerEdge) : z.im < 0 := by
  obtain ⟨θ,hθ,rfl⟩ := hz
  simpa [Complex.exp_mul_I, ← Complex.ofReal_neg, ← Complex.ofReal_sin, Real.sin_neg] using
    neg_lt_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

private noncomputable def halfPlaneQuotient (lower : Bool) (z : ℂ) : ℂ :=
  if lower then (z - 2) / (z + 2) else -1 / (z - 2)

private theorem halfPlaneQuotient_im_pos (lower : Bool) {z : ℂ} (hz : 0 < z.im) :
    0 < (halfPlaneQuotient lower z).im := by
  have hp : z + 2 ≠ 0 := fun h => hz.ne' (by simpa using congrArg Complex.im h)
  have hm : z - 2 ≠ 0 := fun h => hz.ne' (by simpa using congrArg Complex.im h)
  cases lower
  · have he : (halfPlaneQuotient false z).im = z.im / normSq (z-2) := by
      change ((-1 : ℂ) / (z-2)).im = _
      rw [Complex.div_im]
      norm_num [Complex.sub_im, Complex.neg_im, Complex.neg_re, neg_div]
    rw [he]
    exact div_pos hz (normSq_pos.mpr hm)
  · have he : (halfPlaneQuotient true z).im = 4 * z.im / normSq (z+2) := by
      change ((z-2) / (z+2)).im = _
      rw [Complex.div_im]
      norm_num [Complex.sub_im, Complex.sub_re, Complex.add_im, Complex.add_re]
      ring
    rw [he]
    exact div_pos (by positivity) (normSq_pos.mpr hp)

private theorem halfPlaneQuotient_diff (lower : Bool) {z : ℂ}
    (hp : z+2 ≠ 0) (hm : z-2 ≠ 0) :
    DifferentiableAt ℂ (halfPlaneQuotient lower) z := by
  cases lower
  · change DifferentiableAt ℂ (fun w : ℂ => -1 / (w-2)) z
    have hd : DifferentiableAt ℂ (fun w : ℂ => w-2) z := by fun_prop
    exact (differentiableAt_const (-1 : ℂ)).div hd hm
  · change DifferentiableAt ℂ (fun w : ℂ => (w-2) / (w+2)) z
    have hn : DifferentiableAt ℂ (fun w : ℂ => w-2) z := by fun_prop
    have hd : DifferentiableAt ℂ (fun w : ℂ => w+2) z := by fun_prop
    exact hn.div hd hp

private noncomputable def realQuotient (lower : Bool) (x : ℝ) : ℝ :=
  if lower then (x - 2) / (x + 2) else -1 / (x - 2)

private theorem halfPlaneQuotient_ofReal (lower : Bool) (x : ℝ) :
    halfPlaneQuotient lower (x : ℂ) = (realQuotient lower x : ℂ) := by
  cases lower <;> simp [halfPlaneQuotient, realQuotient]

private theorem realQuotient_ne_zero (lower : Bool) {x : ℝ} (hx : x ≠ -2) (hx' : x ≠ 2) :
    realQuotient lower x ≠ 0 := by
  cases lower
  · simpa [realQuotient] using div_ne_zero (by norm_num : (-1:ℝ) ≠ 0) (sub_ne_zero.mpr hx')
  · simpa [realQuotient] using div_ne_zero (sub_ne_zero.mpr hx')
      (by intro h; apply hx; linarith : x+2 ≠ 0)

private def side (lower : Bool) : Set ℂ :=
  if lower then lowerEdge else MarkedRealAxis.curvedEdge

private theorem side_iff_quotient_neg (lower : Bool) {α : ℝ} {G : ℂ → ℂ}
    (hbank : ∀ x : ℝ, x < -2 → ∃ y ∈ Ioo (-1 : ℝ) 0, folding α (G (x : ℂ)) = (y : ℂ))
    (hlower : ∀ x ∈ Ioo (-2 : ℝ) 2,
      ‖folding α (G (x : ℂ))‖ = 1 ∧ (folding α (G (x : ℂ))).im < 0)
    (hupper : ∀ x : ℝ, 2 < x → folding α (G (x : ℂ)) ∈ MarkedRealAxis.curvedEdge)
    {x : ℝ} (hx : x ≠ -2) (hx' : x ≠ 2)
    (hboundary : folding α (G (x : ℂ)) ∈ frontier radialDomain ∪ negativeSlit α) :
    folding α (G (x : ℂ)) ∈ side lower ↔ realQuotient lower x < 0 := by
  rcases lt_or_gt_of_ne hx with hleft | hleft
  · obtain ⟨y, _, hy⟩ := hbank x hleft
    rw [hy]
    cases lower
    · exact iff_of_false (fun h => (upper_im_of_curved h).ne' (ofReal_im y)) (not_lt_of_ge
        (div_nonneg_of_nonpos (by norm_num) (by linarith) : 0 ≤ realQuotient false x))
    · exact iff_of_false (fun h => (lower_im_of_lower h).ne (ofReal_im y)) (not_lt_of_ge
        (div_nonneg_of_nonpos (by linarith) (by linarith) : 0 ≤ realQuotient true x))
  · rcases lt_or_gt_of_ne hx' with hright | hright
    · have him := (hlower x ⟨hleft, hright⟩).2
      have hml : folding α (G (x : ℂ)) ∈ lowerEdge := by
        rw [frontier_radialDomain] at hboundary
        rcases hboundary with ((he | hu) | hl) | hb
        · rcases he with he | he
          · simp [he] at him
          · have he' : folding α (G (x : ℂ)) = -1 := he
            simp [he'] at him
        · exact ((upper_im_of_curved hu).not_gt him).elim
        · exact hl
        · exact (him.ne hb.1).elim
      cases lower
      · exact iff_of_false (fun h => (upper_im_of_curved h).not_gt him) (not_lt_of_ge
          (div_nonneg_of_nonpos (by norm_num) (by linarith) : 0 ≤ realQuotient false x))
      · exact iff_of_true hml (div_neg_of_neg_of_pos (by linarith) (by linarith))
    · have hmu := hupper x hright
      cases lower
      · exact iff_of_true hmu (div_neg_of_neg_of_pos (by norm_num) (by linarith))
      · exact iff_of_false (fun h => (upper_im_of_curved hmu).not_gt (lower_im_of_lower h))
          (not_lt_of_ge (div_nonneg (by linarith) (by linarith) : 0 ≤ realQuotient true x))

private theorem exists_side_indicator (lower : Bool) {α : ℝ}
    (hl : -1 < α) (hr : α < 0) {F : ℂ → ℂ} (hF : CenteredUnfoldedChart α F) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, (H z).re ∈ Ioo 0 1) ∧
      ∀ z ∈ sphere (0 : ℂ) 1, folding α (F z) ∉ ({1,-1} : Set ℂ) →
        Tendsto (fun w => (H w).re) (𝓝[ball 0 1] z)
          (𝓝 ((side lower).indicator (fun _ => (1 : ℝ)) (folding α (F z)))) := by
  classical
  obtain ⟨G,hG,hQ,hR,hbank,hlower,hupper⟩ := exists_normalized_physical_chart hl hr
  let V := Function.invFunOn G upperHalfPlaneSet
  let T := V ∘ F
  have holoV : DifferentiableOn ℂ V (unfoldedDomain α) := by
    rw [← hG.interior_bij.image_eq]
    exact DifferentiableOn.invFunOn hG.holo (isOpen_lt continuous_const Complex.continuous_im)
      hG.interior_bij.injOn
  have holoT := holoV.comp hF.holomorphic hF.interior_bij.mapsTo
  have himT (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : 0 < (T z).im :=
    hG.interior_bij.surjOn.mapsTo_invFunOn (hF.interior_bij.mapsTo hz)
  let Q := halfPlaneQuotient lower
  have hp {z : ℂ} (hz : 0 < z.im) : z + 2 ≠ 0 := by
    intro he
    exact hz.ne' (by simpa using congrArg Complex.im he)
  have hm {z : ℂ} (hz : 0 < z.im) : z - 2 ≠ 0 := by
    intro he
    exact hz.ne' (by simpa using congrArg Complex.im he)
  let H := upperArgument ∘ Q ∘ T
  have holoH : DifferentiableOn ℂ H (ball 0 1) := by
    intro z hz
    have hdiff := halfPlaneQuotient_diff lower (hp (himT z hz)) (hm (himT z hz))
    apply DifferentiableAt.differentiableWithinAt
    exact ((differentiableAt_upperArgument (halfPlaneQuotient_im_pos lower (himT z hz))).comp
      (T z) hdiff).comp z (holoT.differentiableAt (isOpen_ball.mem_nhds hz))
  refine ⟨H, holoH, fun z hz => upperArgument_between (halfPlaneQuotient_im_pos lower (himT z hz)), ?_⟩
  intro z hz hends
  have hfront := hF.frontier_bij.mapsTo hz
  have hne : F z ≠ upperBankEnd α := by
    intro he
    apply hends
    rw [he, folding_upperBankEnd hl hr]
    simp
  obtain ⟨x, hx⟩ := hG.real_prevertex hfront hne
  have hx₀ : x ≠ -2 := by
    rintro rfl
    apply hends
    rw [← hx, show ((-2 : ℝ) : ℂ) = -2 by norm_num, hQ, folding_lowerBankEnd hl hr]
    simp
  have hx₁ : x ≠ 2 := by
    rintro rfl
    apply hends
    rw [← hx, show ((2 : ℝ) : ℂ) = 2 by norm_num, hR, folding_rightEnd hl hr]
    simp
  have hFtrace : Tendsto F (𝓝[ball 0 1] z) (𝓝 (F z)) :=
    (hF.closed_continuous z (sphere_subset_closedBall hz)).mono ball_subset_closedBall
  have hGT : Tendsto (G ∘ T) (𝓝[ball 0 1] z) (𝓝 (G (x : ℂ))) := by
    rw [hx]
    apply hFtrace.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hG.interior_bij.surjOn.rightInvOn_invFunOn (hF.interior_bij.mapsTo hw)).symm
  have hTtrace := trace_inverse hG (show 0 ≤ (x : ℂ).im by simp)
    (Filter.mem_of_superset self_mem_nhdsWithin fun w hw => (himT w hw).le) hGT
  have hqdiff := halfPlaneQuotient_diff lower
    (z := (x : ℂ)) (by exact_mod_cast (by intro h; apply hx₀; linarith : x+2 ≠ 0))
    (by exact_mod_cast sub_ne_zero.mpr hx₁)
  have hqtrace : Tendsto (Q ∘ T) (𝓝[ball 0 1] z) (𝓝 (Q (x : ℂ))) :=
    hqdiff.continuousAt.tendsto.comp hTtrace
  have hqreal : Q (x : ℂ) = (realQuotient lower x : ℂ) := halfPlaneQuotient_ofReal lower x
  have hn := realQuotient_ne_zero lower hx₀ hx₁
  have hArg := tendsto_upperArgument_re hqtrace
    (Filter.mem_of_superset self_mem_nhdsWithin fun w hw => halfPlaneQuotient_im_pos lower (himT w hw))
    (by rw [hqreal]; simp)
    (by rw [hqreal]; exact_mod_cast hn)
  have hboundary : folding α (G (x : ℂ)) ∈ frontier radialDomain ∪ negativeSlit α := by
    rw [hx, ← hF.physical_boundary_image hl hr]
    exact mem_image_of_mem (folding α ∘ F) hz
  have hiff := side_iff_quotient_neg lower hbank hlower hupper hx₀ hx₁ hboundary
  rw [hx] at hiff
  by_cases hs : folding α (F z) ∈ side lower
  · rw [Set.indicator_of_mem hs]
    rwa [hqreal, arg_ofReal_of_neg (hiff.mp hs), div_self Real.pi_ne_zero] at hArg
  · rw [Set.indicator_of_notMem hs]
    rwa [hqreal, arg_ofReal_of_nonneg (le_of_not_gt (fun h => hs (hiff.mpr h))), zero_div] at hArg

/-- The upper boundary mass of a folded slit chart is the real trace of a
holomorphic function with real part strictly between zero and one. -/
theorem exists_upper_indicator {α : ℝ} (hl : -1 < α) (hr : α < 0) {F : ℂ → ℂ}
    (hF : CenteredUnfoldedChart α F) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, (H z).re ∈ Ioo 0 1) ∧
      ∀ z ∈ sphere (0 : ℂ) 1, folding α (F z) ∉ ({1,-1} : Set ℂ) →
        Tendsto (fun w => (H w).re) (𝓝[ball 0 1] z)
          (𝓝 (MarkedRealAxis.curvedEdge.indicator (fun _ => (1 : ℝ)) (folding α (F z)))) :=
  exists_side_indicator false hl hr hF

/-- The lower boundary mass of a folded slit chart is the real trace of a
holomorphic function with real part strictly between zero and one. -/
theorem exists_lower_indicator {α : ℝ} (hl : -1 < α) (hr : α < 0) {F : ℂ → ℂ}
    (hF : CenteredUnfoldedChart α F) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, (H z).re ∈ Ioo 0 1) ∧
      ∀ z ∈ sphere (0 : ℂ) 1, folding α (F z) ∉ ({1,-1} : Set ℂ) →
        Tendsto (fun w => (H w).re) (𝓝[ball 0 1] z)
          (𝓝 (lowerEdge.indicator (fun _ => (1 : ℝ)) (folding α (F z)))) :=
  exists_side_indicator true hl hr hF

end BelgianChocolate.SlitHarmonicMeasure
