import ControllerFeasible
import ComparisonCayley
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace BelgianChocolate.ControlWitness

open Complex Metric Set Polynomial
open BelgianChocolate.HarmonicComparison

noncomputable def closedLoop (δ : ℝ) (x y : ℝ[X]) : ℝ[X] :=
  (X^2 - C (2*δ)*X + 1)*x + (X^2-1)*y

noncomputable def diskController (δ : ℝ) (x y : ℝ[X]) (z : ℂ) : ℂ :=
  let s := comparisonQuotient z
  (s^2-1)*aeval s y / aeval s (closedLoop δ x y)

/-- The two explicit holomorphic unit factors of the controller in disk coordinates. -/
noncomputable def diskUnit (c : ℂ) (p q : ℝ[X]) (z : ℂ) : ℂ :=
  c * aeval (comparisonQuotient z) p /
    ((1-z)^2 * aeval (comparisonQuotient z) q)

private theorem disk_den_ne_zero {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) : 1-z ≠ 0 := by
  intro e
  have h := mem_ball_zero_iff.mp hz
  rw [← sub_eq_zero.mp e] at h
  simp at h

private theorem stable_eval_cayley {p : ℝ[X]} (hp : StrictlyStable p) {z : ℂ}
    (hz : z ∈ ball (0:ℂ) 1) : aeval (comparisonQuotient z) p ≠ 0 := by
  intro e
  exact (hp.2 _ e).not_ge (comparisonQuotient_re_pos (mem_ball_zero_iff.mp hz)).le

theorem disk_unit_regular {c : ℂ} (hc : c ≠ 0) {p q : ℝ[X]}
    (hp : StrictlyStable p) (hq : StrictlyStable q) {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    DifferentiableAt ℂ (diskUnit c p q) z ∧ diskUnit c p q z ≠ 0 := by
  have hden := disk_den_ne_zero hz
  have h1 : DifferentiableAt ℂ (fun _ : ℂ => (1:ℂ)) z := differentiableAt_const _
  have h2 : DifferentiableAt ℂ (fun w : ℂ => 1-w) z := h1.sub differentiableAt_id
  have hs : DifferentiableAt ℂ comparisonQuotient z :=
    (h1.add differentiableAt_id).div h2 hden
  have hpn := stable_eval_cayley hp hz
  have hqn := stable_eval_cayley hq hz
  have hdn := mul_ne_zero (pow_ne_zero 2 hden) hqn
  refine ⟨?_,div_ne_zero (mul_ne_zero hc hpn) hdn⟩
  have hc' : DifferentiableAt ℂ (fun _ : ℂ => c) z := differentiableAt_const _
  have hp' : DifferentiableAt ℂ (fun w : ℂ => aeval (comparisonQuotient w) p) z :=
    DifferentiableAt.comp (f := comparisonQuotient) (g := fun s : ℂ => aeval s p) z
      p.differentiableAt_aeval hs
  have hq' : DifferentiableAt ℂ (fun w : ℂ => aeval (comparisonQuotient w) q) z :=
    DifferentiableAt.comp (f := comparisonQuotient) (g := fun s : ℂ => aeval s q) z
      q.differentiableAt_aeval hs
  exact (hc'.mul hp').div ((h2.pow 2).mul hq') hdn

theorem disk_zero_factor (δ : ℝ) (x y : ℝ[X])
    (hq : StrictlyStable (closedLoop δ x y)) {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    diskController δ x y z = z*diskUnit 4 y (closedLoop δ x y) z := by
  have hden := disk_den_ne_zero hz
  have hqn := stable_eval_cayley hq hz
  have e : (comparisonQuotient z)^2-1 = 4*z/(1-z)^2 := by
    unfold comparisonQuotient
    field_simp
    ring
  simp only [diskController,diskUnit,e]
  field_simp [hden,hqn]


theorem disk_one_factor {δ t : ℝ} (hrel : t^2*(1+δ) = 1-δ)
    (x y : ℝ[X]) (hq : StrictlyStable (closedLoop δ x y)) {z : ℂ}
    (hz : z ∈ ball (0:ℂ) 1) :
    diskController δ x y z = 1 + (z-(t:ℂ)*I)*(z+(t:ℂ)*I)*
      diskUnit (-2*(1+(δ:ℂ))) x (closedLoop δ x y) z := by
  let s := comparisonQuotient z
  let q := closedLoop δ x y
  have hden := disk_den_ne_zero hz
  have hqn : aeval s q ≠ 0 := stable_eval_cayley hq hz
  have hr : (t:ℂ)^2*(1+(δ:ℂ)) = 1-(δ:ℂ) := by exact_mod_cast hrel
  have e : (s^2-2*(δ:ℂ)*s+1)*(1-z)^2 =
      2*(1+(δ:ℂ))*(z-(t:ℂ)*I)*(z+(t:ℂ)*I) := by
    dsimp [s,comparisonQuotient]
    field_simp [hden]
    linear_combination -2*hr + 2*(1+(δ:ℂ))*(t:ℂ)^2*Complex.I_sq
  have eq : aeval s q =
      (s^2-2*(δ:ℂ)*s+1)*aeval s x + (s^2-1)*aeval s y := by
    simp [q,closedLoop]
  change (s^2-1)*aeval s y/aeval s q =
    1+(z-(t:ℂ)*I)*(z+(t:ℂ)*I)*((-2*(1+(δ:ℂ)))*aeval s x/((1-z)^2*aeval s q))
  field_simp [hden,hqn]
  linear_combination -(1-z)^2*eq - (aeval s x)*e

end BelgianChocolate.ControlWitness

