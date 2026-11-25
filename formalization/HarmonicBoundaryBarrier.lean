import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Tactic.Linarith

/-! A boundary lower bound across an isolated exceptional point of a disc. -/

namespace BelgianChocolate.HarmonicComparison

open Complex Filter Metric Set Topology
open scoped ComplexConjugate

private theorem norm_le_one_of_locally_bounded_boundary {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball 0 1))
    (hboundary : ∀ ξ : ℂ, ‖ξ‖ = 1 →
      ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z ξ < d → ‖G z‖ ≤ 1) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖G z‖ ≤ 1 := by
  let S : Set ℂ := {z ∈ ball 0 1 | 1 < ‖G z‖}
  have hS : S ⊆ ball (0 : ℂ) 1 := fun _ hz ↦ hz.1
  have hcl : closure S ⊆ ball (0 : ℂ) 1 := by
    intro x hx
    have hxle : x ∈ closedBall (0 : ℂ) 1 :=
      closure_minimal (hS.trans ball_subset_closedBall) isClosed_closedBall hx
    by_contra h
    have hxξ : ‖x‖ = 1 :=
      le_antisymm (mem_closedBall_zero_iff.mp hxle) (not_lt.mp (fun h' ↦ h (mem_ball_zero_iff.mpr h')))
    obtain ⟨d, hd, hdG⟩ := hboundary x hxξ
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx d hd
    exact (not_lt.mpr (hdG y hy.1 (by rwa [dist_comm]))) hy.2
  have hfrontier : ∀ x ∈ frontier S, ‖G x‖ ≤ 1 := by
    intro x hx
    by_contra! h
    have hxb := hcl (frontier_subset_closure hx)
    have hxcont : ContinuousAt (fun z ↦ ‖G z‖) x :=
      (hG.continuousOn.continuousAt (isOpen_ball.mem_nhds hxb)).norm
    have hneigh : S ∈ 𝓝 x :=
      Filter.inter_mem (isOpen_ball.mem_nhds hxb) (hxcont (lt_mem_nhds h))
    exact hx.2 (mem_interior_iff_mem_nhds.mpr hneigh)
  intro z hz
  by_contra! h
  exact (not_lt.mpr
    (Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball.subset hS)
      ⟨hG.mono hS, hG.continuousOn.mono hcl⟩
      hfrontier (subset_closure (show z ∈ S from ⟨hz, h⟩)))) h

private theorem norm_le_one_of_one_boundary_exception {G : ℂ → ℂ} {M : ℝ} {ξ : ℂ}
    (hG : DifferentiableOn ℂ G (ball 0 1))
    (hM₀ : 0 ≤ M)
    (hM : ∀ z ∈ ball (0 : ℂ) 1, ‖G z‖ ≤ M)
    (hξ : ‖ξ‖ = 1)
    (hboundary : ∀ η : ℂ, ‖η‖ = 1 → η ≠ ξ →
      ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z η < d → ‖G z‖ ≤ 1) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖G z‖ ≤ 1 := by
  intro z hz
  by_contra! hn
  have hzne : z ≠ ξ := fun h ↦ by
    have := mem_ball_zero_iff.mp hz
    rw [h, hξ] at this
    exact (lt_irrefl 1) this
  have hfac : 0 < ‖(z - ξ) / 2‖ := norm_pos_iff.mpr (div_ne_zero (sub_ne_zero.mpr hzne) (by norm_num))
  obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt (1 / ‖(z - ξ) / 2‖) hn
  let H : ℂ → ℂ := fun w ↦ (w - ξ) / 2 * G w ^ n
  have hH : DifferentiableOn ℂ H (ball 0 1) :=
    ((differentiable_id.sub_const ξ).div_const (2 : ℂ)).differentiableOn.mul (hG.pow n)
  have hnorm (w : ℂ) : ‖H w‖ = (dist w ξ / 2) * ‖G w‖ ^ n := by
    simp [H, norm_pow, dist_eq_norm]
  have hunit := norm_le_one_of_locally_bounded_boundary hH (fun η hη ↦ by
    by_cases h : η = ξ
    · subst η
      refine ⟨2 / (1 + M ^ n), by positivity, ?_⟩
      intro w hw hd
      rw [hnorm]
      have hp : ‖G w‖ ^ n ≤ M ^ n := pow_le_pow_left₀ (norm_nonneg _) (hM w hw) _
      have hprod : dist w ξ / 2 * (1 + M ^ n) ≤ 1 := by
        have hpos : 0 < 1 + M ^ n := by positivity
        have h' := (lt_div_iff₀ hpos).mp hd
        linarith
      calc
        dist w ξ / 2 * ‖G w‖ ^ n ≤ dist w ξ / 2 * (1 + M ^ n) := by gcongr; linarith
        _ ≤ 1 := hprod
    · obtain ⟨d, hd, hdG⟩ := hboundary η hη h
      refine ⟨d, hd, ?_⟩
      intro w hw hdw
      have hdist : dist w ξ ≤ 2 := by
        rw [dist_eq_norm]
        have hb : ‖w‖ ≤ 1 := (mem_ball_zero_iff.mp hw).le
        linarith [norm_sub_le w ξ]
      rw [hnorm]
      calc
        dist w ξ / 2 * ‖G w‖ ^ n ≤ 1 * 1 := by
          gcongr
          · linarith
          · exact pow_le_one₀ (norm_nonneg _) (hdG w hw hdw)
        _ = 1 := one_mul 1) z hz
  have hp := (div_lt_iff₀ hfac).mp hn'
  exact (not_lt_of_ge (by simpa only [H, norm_mul, norm_pow, mul_comm] using hunit)) hp

private theorem one_sub_re_mul_conj_eq {ξ η : ℂ} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) :
    1 - (conj ξ * η).re = dist η ξ ^ 2 / 2 := by
  have hξsq := Complex.sq_norm ξ
  have hηsq := Complex.sq_norm η
  rw [hξ, one_pow, Complex.normSq_apply] at hξsq
  rw [hη, one_pow, Complex.normSq_apply] at hηsq
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
  simp only [mul_re, conj_re, conj_im, sub_re, sub_im]
  nlinarith

/-- Lower bounds from inside the disc at all nearby boundary points other than
the distinguished point imply an interior lower bound there too. The proof damps
the exponential of the holomorphic function away from the distinguished point.
An analytic factor removes that single exception in the maximum argument. -/
theorem im_lowerBound_near_boundary_of_puncturedArc {W : ℂ → ℂ} {M : ℝ} {ξ : ℂ}
    (hW : DifferentiableOn ℂ W (ball 0 1))
    (hM : ∀ z ∈ ball (0 : ℂ) 1, -M ≤ (W z).im)
    (hξ : ‖ξ‖ = 1)
    (hnear : ∀ ε > 0, ∃ ρ > 0, ∀ η : ℂ, ‖η‖ = 1 → η ≠ ξ → dist η ξ < ρ →
      ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z η < d → -ε ≤ (W z).im) :
    ∀ ε > 0, ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z ξ < d → -ε ≤ (W z).im := by
  intro ε hε
  let a : ℝ := ε / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨ρ, hρ, hnear'⟩ := hnear a ha
  let C : ℝ := (max M 0 + 1) / (ρ ^ 2 / 4)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC' : C * (ρ ^ 2 / 4) = max M 0 + 1 := by
    dsimp [C]
    field_simp
  let P : ℂ → ℂ := fun z ↦ 1 - conj ξ * z
  have hP : Differentiable ℂ P := (differentiable_const _).sub
    ((differentiable_const _).mul differentiable_id)
  have hPcont : Continuous (fun z ↦ (P z).re) := Complex.continuous_re.comp hP.continuous
  have hPξ : (P ξ).re = 0 := by
    simpa [P] using one_sub_re_mul_conj_eq hξ hξ
  have hPnonneg (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : 0 ≤ (P z).re := by
    simp only [P, sub_re, one_re, sub_nonneg]
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_conj, hξ, one_mul]
    exact (mem_ball_zero_iff.mp hz).le
  let G : ℂ → ℂ := fun z ↦ Complex.exp (I * W z - ((a : ℂ) + (C : ℂ) * P z))
  have hG : DifferentiableOn ℂ G (ball 0 1) := by
    exact ((hW.const_mul I).sub
      ((differentiableOn_const _).add (hP.differentiableOn.const_mul _))).cexp
  have hGnorm (z : ℂ) : ‖G z‖ = Real.exp (-(W z).im - (a + C * (P z).re)) := by
    simp [G, Complex.norm_exp, mul_re]
  have hGM (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : ‖G z‖ ≤ Real.exp M := by
    rw [hGnorm, Real.exp_le_exp]
    nlinarith [hM z hz, mul_nonneg hC.le (hPnonneg z hz)]
  have hnorm := norm_le_one_of_one_boundary_exception hG (Real.exp_nonneg M) hGM hξ
    (fun η hη hηξ ↦ by
      by_cases h : dist η ξ < ρ
      · obtain ⟨d, hd, hbound⟩ := hnear' η hη hηξ h
        refine ⟨d, hd, ?_⟩
        intro z hz hzd
        rw [hGnorm, ← Real.exp_zero, Real.exp_le_exp]
        nlinarith [hbound z hz hzd, mul_nonneg hC.le (hPnonneg z hz)]
      · have hPη : ρ ^ 2 / 4 < (P η).re := by
          have hdist := not_lt.mp h
          have hsq := pow_le_pow_left₀ hρ.le hdist 2
          have heq : (P η).re = dist η ξ ^ 2 / 2 := by
            simpa [P] using one_sub_re_mul_conj_eq hξ hη
          rw [heq]
          nlinarith [sq_pos_of_pos hρ]
        obtain ⟨d, hd, hdP⟩ := Metric.nhds_basis_ball.eventually_iff.mp
          ((hPcont.continuousAt : ContinuousAt (fun z ↦ (P z).re) η) (lt_mem_nhds hPη))
        refine ⟨d, hd, ?_⟩
        intro z hz hzd
        have hPz : ρ ^ 2 / 4 < (P z).re := hdP (mem_ball.mpr hzd)
        have hp : C * (ρ ^ 2 / 4) ≤ C * (P z).re := mul_le_mul_of_nonneg_left hPz.le hC.le
        rw [hC'] at hp
        rw [hGnorm, ← Real.exp_zero, Real.exp_le_exp]
        linarith [hM z hz, le_max_left M 0])
  have hCξ : C * (P ξ).re < a := by simpa [hPξ] using ha
  have hCPcont : ContinuousAt (fun z ↦ C * (P z).re) ξ :=
    (continuous_const.mul hPcont).continuousAt
  obtain ⟨d, hd, hdP⟩ := Metric.nhds_basis_ball.eventually_iff.mp
    (hCPcont (gt_mem_nhds hCξ))
  refine ⟨d, hd, ?_⟩
  intro z hz hzd
  have h := hnorm z hz
  rw [hGnorm, ← Real.exp_zero, Real.exp_le_exp] at h
  have hPz := hdP (mem_ball.mpr hzd)
  dsimp [a] at *
  linarith

/-- Convert a local lower bound at a unit boundary point to the radial form used
by the disc comparison theorem. -/
theorem radial_im_lowerBound_of_local {W : ℂ → ℂ} {ξ : ℂ} (hξ : ‖ξ‖ = 1)
    (hlower : ∀ ε > 0, ∃ d > 0, ∀ z ∈ ball (0 : ℂ) 1, dist z ξ < d → -ε ≤ (W z).im) :
    ∀ ε > 0, ∃ b ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo b 1, -ε ≤ (W (r • ξ)).im := by
  intro ε hε
  obtain ⟨d, hd, hnear⟩ := hlower ε hε
  let b : ℝ := max (1 - d) (1 / 2)
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _), ?_⟩
    exact max_lt (by linarith) (by norm_num)
  refine ⟨b, hb, ?_⟩
  intro r hr
  have hr₀ := hb.1.trans hr.1
  apply hnear (r • ξ)
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr₀, hξ, mul_one]
    exact hr.2
  · have hdist : dist (r • ξ) ξ = 1 - r := by
      calc
        dist (r • ξ) ξ = ‖(r - 1) • ξ‖ := by rw [dist_eq_norm, sub_smul, one_smul]
        _ = 1 - r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hr.2), hξ, mul_one, neg_sub]
    have hr₁ := (le_max_left (1 - d) (1 / 2)).trans_lt hr.1
    rw [hdist]
    linarith

end BelgianChocolate.HarmonicComparison
