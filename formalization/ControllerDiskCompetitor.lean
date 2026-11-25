import ControllerDiskMap
import ControllerDiskFactors

namespace BelgianChocolate.ControlWitness

open Complex Metric Set Polynomial
open scoped ComplexConjugate
open BelgianChocolate.SourceDiskPaths
open BelgianChocolate.HarmonicComparison

private theorem real_poly_conj (p : ℝ[X]) (s : ℂ) :
    aeval (conj s) p = conj (aeval s p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n r => simp [Polynomial.aeval_monomial]

theorem diskController_conj (δ : ℝ) (x y : ℝ[X]) (z : ℂ) :
    diskController δ x y (conj z) = conj (diskController δ x y z) := by
  have e : comparisonQuotient (conj z) = conj (comparisonQuotient z) := by
    simp [comparisonQuotient]
  simp only [diskController,e,real_poly_conj,map_div₀,map_mul,map_sub,map_pow,map_one]

theorem controller_to_marked {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) (ht' : t < 1)
    (hrel : t^2*(1+δ)=1-δ) {x y : ℝ[X]} (hx : StrictlyStable x)
    (hy : StrictlyStable y) (hq : StrictlyStable (closedLoop δ x y)) :
    MarkedCompetitor t (diskController δ x y) := by
  apply marked_of_disk_factors ht ht' _ (diskUnit 4 y (closedLoop δ x y))
    (diskUnit (-2*(1+(δ:ℂ))) x (closedLoop δ x y))
  · exact fun _ hz => disk_unit_regular (by norm_num) hy hq hz
  · have hn : (1:ℂ)+(δ:ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1:ℝ)+δ ≠ 0)
    exact fun _ hz => disk_unit_regular (mul_ne_zero (by norm_num) hn) hx hq hz
  · exact fun _ hz => disk_zero_factor δ x y hq hz
  · exact fun _ hz => disk_one_factor hrel x y hq hz

/-- Forward Cayley implication for every finite real strictly stable controller. -/
theorem feasible_to_marked {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) (ht' : t < 1)
    (hrel : t^2*(1+δ)=1-δ) (hfeas : Feasible δ) :
    ∃ f : ℂ → ℂ, MarkedCompetitor t f ∧ ∀ z, f (conj z) = conj (f z) := by
  obtain ⟨x,y,hx,hy,_,hq⟩ := hfeas
  exact ⟨_,controller_to_marked hδ ht ht' hrel hx hy hq,diskController_conj δ x y⟩

/-- Natural disk parameter of every feasible control parameter in the open unit interval. -/
theorem feasible_to_disk {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) (hc : Feasible δ) :
    let t := Real.sqrt ((1-δ)/(1+δ))
    0 < t ∧ t < 1 ∧ ∃ f : ℂ → ℂ, MarkedCompetitor t f ∧ ∀ z, f (conj z) = conj (f z) := by
  let t := Real.sqrt ((1-δ)/(1+δ))
  have hd : 0 < 1+δ := by linarith
  have hr : 0 < (1-δ)/(1+δ) := div_pos (by linarith) hd
  have ht : 0 < t := Real.sqrt_pos.2 hr
  have hs : t^2 = (1-δ)/(1+δ) := Real.sq_sqrt hr.le
  have hsmall : (1-δ)/(1+δ) < 1 := (div_lt_one hd).2 (by linarith)
  have ht' : t < 1 := by nlinarith
  exact ⟨ht,ht',feasible_to_marked hδ ht ht' (by rw [hs]; field_simp) hc⟩

/-- The explicit degree-28 controller yields a real-symmetric marked disk competitor
at the exact parameter `witnessT`, strictly below one tenth. -/
theorem witness_marked : ∃ f : ℂ → ℂ,
    MarkedCompetitor witnessT f ∧ ∀ z, f (conj z) = conj (f z) := by
  apply feasible_to_marked (δ := (98236947/100000000:ℝ)) (by norm_num)
    witnessT_spec.2.1 (by linarith [witnessT_spec.2.2]) _ witness_feasible
  rw [witnessT_spec.1]
  norm_num

end BelgianChocolate.ControlWitness

