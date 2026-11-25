import ControllerDiskRealization
import Mathlib.Analysis.Complex.CauchyIntegral

namespace BelgianChocolate.ControlWitness
open Complex Polynomial Finset Metric Set Filter
open scoped ComplexConjugate NNReal ENNReal Topology

private noncomputable def realTruncation (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range n, C (p.coeff k).re * X^k

private theorem realTruncation_eval (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (z : ℂ) :
    2*aeval z (realTruncation p n) = p.partialSum n z + conj (p.partialSum n (conj z)) := by
  simp only [realTruncation,map_sum,map_mul,map_pow,aeval_C,aeval_X,
    FormalMultilinearSeries.partialSum,FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    smul_eq_mul,map_pow,conj_conj]
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  have e : (p.coeff k : ℂ)+conj (p.coeff k) = 2*((p.coeff k).re:ℂ) := by
    apply Complex.ext <;> simp
    ring
  linear_combination -(z^k)*e

theorem exists_real_polynomial_approx {a : ℂ → ℂ} {R : ℝ≥0} (hR : 1 < R)
    (ha : DifferentiableOn ℂ a (closedBall 0 R))
    (hsym : ∀ z : ℂ, ‖z‖ ≤ 1 → a (conj z) = conj (a z))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ z : ℂ, ‖z‖ ≤ 1 → ‖aeval z p - a z‖ < ε := by
  obtain ⟨r,hr,hr'⟩ := exists_between hR
  let p := cauchyPowerSeries a 0 R
  have hpower := ha.hasFPowerSeriesOnBall (lt_trans zero_lt_one hR)
  have hh := hpower.tendstoUniformlyOn (r' := r) (by exact_mod_cast hr')
  have he := (Metric.tendstoUniformlyOn_iff.mp hh ε hε).exists
  obtain ⟨n,hn⟩ := he
  refine ⟨realTruncation p n,fun z hz => ?_⟩
  have hl : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖p.partialSum n w-a w‖ < ε := by
    intro w hw
    have hw' : w ∈ ball (0:ℂ) r := mem_ball_zero_iff.mpr (lt_of_le_of_lt hw (by exact_mod_cast hr))
    simpa [p,dist_eq_norm,norm_sub_rev] using hn w hw'
  have hc := hl (conj z) (by simpa using hz)
  have e : 2*(aeval z (realTruncation p n)-a z) =
      (p.partialSum n z-a z) + conj (p.partialSum n (conj z)-a (conj z)) := by
    rw [map_sub,hsym z hz,conj_conj,mul_sub,realTruncation_eval]
    ring
  have h := norm_add_le (p.partialSum n z-a z) (conj (p.partialSum n (conj z)-a (conj z)))
  rw [← e,norm_mul,Complex.norm_conj] at h
  norm_num at h
  linarith [hl z hz]

private theorem uniform_lower {f : ℂ → ℂ} (hf : ContinuousOn f (closedBall 0 1))
    (hn : ∀ z : ℂ, ‖z‖ ≤ 1 → f z ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → m ≤ ‖f z‖ := by
  obtain ⟨w,hw,hm⟩ := (isCompact_closedBall (0:ℂ) 1).exists_isMinOn
    ⟨0,by simp⟩ hf.norm
  exact ⟨_,norm_pos_iff.mpr (hn w (by simpa using hw)),fun z hz => hm (by simpa using hz)⟩

/-- Strict-side realization once the removable analytic unit on a larger disk is available. -/
theorem feasible_of_analytic_disk_unit {δ : ℝ} (hδ : δ < 1) {a : ℂ → ℂ} {R : ℝ≥0}
    (hR : 1 < R) (ha : DifferentiableOn ℂ a (closedBall 0 R))
    (hsym : ∀ z : ℂ, ‖z‖ ≤ 1 → a (conj z) = conj (a z))
    (hA : ∀ z : ℂ, ‖z‖ ≤ 1 → a z ≠ 0)
    (hD : ∀ z : ℂ, ‖z‖ ≤ 1 → 1+z^2*(1+(δ:ℂ))/(1-(δ:ℂ))+z*a z ≠ 0) :
    Feasible δ := by
  have hcont := ha.continuousOn.mono (closedBall_subset_closedBall (by exact_mod_cast hR.le))
  obtain ⟨m,hm,hm'⟩ := uniform_lower hcont hA
  let d := fun z : ℂ => 1+z^2*(1+(δ:ℂ))/(1-(δ:ℂ))+z*a z
  have hdcont : ContinuousOn d (closedBall 0 1) := by dsimp [d]; fun_prop
  obtain ⟨l,hl,hl'⟩ := uniform_lower hdcont hD
  obtain ⟨p,hp⟩ := exists_real_polynomial_approx hR ha hsym (lt_min hm hl)
  apply feasible_of_disk_polynomial hδ p
  · intro z hz he
    have h := hp z hz
    rw [he,zero_sub,norm_neg] at h
    exact (not_lt_of_ge (hm' z hz)) (h.trans_le (min_le_left _ _))
  · intro z hz he
    have e : d z = -(z*(aeval z p-a z)) := by dsimp [d]; linear_combination he
    have h := hl' z hz
    rw [e,norm_neg,norm_mul] at h
    have h' := mul_le_mul_of_nonneg_right hz (norm_nonneg (aeval z p-a z))
    linarith [(hp z hz).trans_le (min_le_right _ _)]

end BelgianChocolate.ControlWitness

