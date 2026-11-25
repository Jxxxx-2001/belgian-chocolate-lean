import SlitBarrierMean

namespace BelgianChocolate.SlitHarmonicMeasure

open Complex Metric Set MeasureTheory
open BelgianChocolate.SlitBoundaryGeometry BelgianChocolate.SlitSquareRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Harmonic measure of a closed neighborhood of the moving slit tip. -/
theorem mass_tip_ball_le {β ε : ℝ} {F : ℂ → ℂ} (he : 0 < ε)
    (h : CenteredUnfoldedChart β F) :
    mass β F (closedBall (β : ℂ) (ε^2)) ≤
      (((2 * ε : ℝ) : ℂ) / ((ε : ℂ) + unfolding β 0)).re := by
  let H := fun z : ℂ => ((2 * ε : ℝ) : ℂ) / ((ε : ℂ) + F z)
  have hr {z : ℂ} (hz : z ∈ closedBall 0 1) : 0 ≤ (F z).re := by
    exact (closure_minimal (t := {u : ℂ | 0 ≤ u.re})
      (fun (u : ℂ) (hu : u ∈ unfoldedDomain β) => hu.1.le)
      (isClosed_le continuous_const continuous_re)) (h.closed_bij.mapsTo hz)
  have hne {z : ℂ} (hz : z ∈ closedBall 0 1) : (ε : ℂ) + F z ≠ 0 := by
    intro eq
    have ht := congrArg Complex.re eq
    simp at ht
    linarith [hr hz]
  have hzero : (H 0).re = _ := congrArg (fun u : ℂ => (((2*ε : ℝ) : ℂ)/((ε : ℂ)+u)).re) h.zero
  rw [← hzero]
  apply mass_le_re_barrier (H := H) h measurableSet_closedBall
  · exact (differentiableOn_const (((2*ε : ℝ) : ℂ))).div ((differentiableOn_const (ε : ℂ)).add h.holomorphic)
      (fun _ hz => hne (ball_subset_closedBall hz))
  · exact continuousOn_const.div (continuousOn_const.add h.closed_continuous) (fun _ hz => hne hz)
  · intro z hz
    have hclosed := sphere_subset_closedBall hz
    have hpos := Complex.normSq_pos.mpr (hne hclosed)
    have hden : Complex.normSq ((ε : ℂ) + F z) =
        ε^2 + 2*ε*(F z).re + Complex.normSq (F z) := by
      simp [Complex.normSq_apply, sq]; ring
    have hform : (H z).re = 2*ε*(ε+(F z).re)/Complex.normSq ((ε : ℂ) + F z) := by
      simp [H, Complex.div_re]
    rw [hform]
    by_cases hin : folding β (F z) ∈ closedBall (β : ℂ) (ε^2)
    · rw [indicator_of_mem hin]
      have hb := mem_closedBall.mp hin
      rw [dist_eq_norm, folding, add_sub_cancel_right, norm_pow, Complex.sq_norm] at hb
      apply (le_div_iff₀ hpos).mpr
      rw [hden]
      linarith
    · rw [indicator_of_notMem hin]
      exact div_nonneg (mul_nonneg (by positivity) (add_nonneg he.le (hr hclosed))) hpos.le

/-- Explicit bound for the harmonic measure of the newly added slit segment. -/
theorem mass_added_segment_le {α β : ℝ} {F : ℂ → ℂ} (hab : α < β) (hr : β < 0)
    (h : CenteredUnfoldedChart β F) :
    mass β F {w : ℂ | w.im = 0 ∧ α ≤ w.re ∧ w.re ≤ β} ≤
      2 * Real.sqrt (β-α) / (Real.sqrt (β-α) + Real.sqrt (-β)) := by
  let ε := Real.sqrt (β-α)
  let t := Real.sqrt (-β)
  have he : 0 < ε := Real.sqrt_pos.2 (sub_pos.2 hab)
  have ht : 0 < t := Real.sqrt_pos.2 (neg_pos.2 hr)
  have hes : ε^2 = β-α := Real.sq_sqrt (sub_nonneg.2 hab.le)
  have hts : t^2 = -β := Real.sq_sqrt (neg_nonneg.2 hr.le)
  have hfold : folding β (t : ℂ) = 0 := by
    change (t : ℂ)^2 + (β : ℂ) = 0
    exact_mod_cast (show t^2+β=0 by linarith)
  have hun := unfolding_folding_of_re_pos (α := β) (u := (t : ℂ)) (by simpa using ht)
  rw [hfold] at hun
  apply le_trans (mass_mono (G := closedBall (β : ℂ) (ε^2)) ?_) ?_
  · intro w hw
    obtain ⟨him,hlo,hhi⟩ := hw
    have hwre : (w.re : ℂ) = w := Complex.ext (by simp) (by simpa using him.symm)
    rw [mem_closedBall, dist_eq_norm, ← hwre, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.2 hhi), hes]
    linarith
  · have hb := mass_tip_ball_le he h
    rw [hun, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re] at hb
    exact hb

/-- Both banks of every nontrivial added open segment have positive total mass. -/
theorem mass_added_segment_pos {α β : ℝ} {F : ℂ → ℂ} (hl : -1 < α) (hab : α < β)
    (hr : β < 0) (h : CenteredUnfoldedChart β F) :
    0 < mass β F {w : ℂ | w.im = 0 ∧ α < w.re ∧ w.re < β} := by
  let m : ℝ := (α+β)/2
  have hm : α < m ∧ m < β := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  let U := radialDomain ∩ Complex.re ⁻¹' Ioo α β
  have hU : IsOpen U := isOpen_radialDomain.inter (isOpen_Ioo.preimage continuous_re)
  have hmb : (m : ℂ) ∈ radialDomain := by
    change ‖(m : ℂ)‖ < radialRadius (m : ℂ)
    simp [radialRadius, abs_of_neg (hm.2.trans hr)]
    linarith [hm.1]
  have hms : (m : ℂ) ∈ BelgianChocolate.SlitStarConvex.negativeSlit β :=
    ⟨by simp, by simpa using (hl.trans hm.1).le, by simpa using hm.2.le⟩
  have him := h.physical_boundary_image (hl.trans hab) hr
  have hmem : (m : ℂ) ∈ (folding β ∘ F) '' sphere 0 1 := by rw [him]; exact Or.inr hms
  obtain ⟨ζ,hζ,hζm⟩ := hmem
  apply mass_pos_of_isOpen_hit h hU _ hζ
  · change (folding β ∘ F) ζ ∈ U
    rw [hζm]
    exact ⟨hmb, hm⟩
  · intro z hz hzu
    have hb : (folding β ∘ F) z ∈ frontier radialDomain ∪ _ := him ▸ mem_image_of_mem _ hz
    rcases hb with hf | hs
    · exact False.elim (hf.2 (isOpen_radialDomain.interior_eq.symm ▸ hzu.1))
    · exact ⟨hs.1, hzu.2⟩

end BelgianChocolate.SlitHarmonicMeasure




