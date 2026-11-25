import ControllerWitness

namespace BelgianChocolate.ControlWitness

open Polynomial

/-- Strict Hurwitz stability for polynomials with real coefficients. -/
def StrictlyStable (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ ∀ s : ℂ, aeval s p = 0 → s.re < 0

def Feasible (δ : ℝ) : Prop :=
  ∃ x y : ℝ[X], StrictlyStable x ∧ StrictlyStable y ∧ y.natDegree ≤ x.natDegree ∧
    StrictlyStable ((X^2 - C (2*δ)*X + 1)*x + (X^2-1)*y)

noncomputable def toRealPoly (p : ℚ[X]) : ℝ[X] := p.map (algebraMap ℚ ℝ)

@[simp] theorem toRealPoly_aeval (p : ℚ[X]) (s : ℂ) :
    aeval s (toRealPoly p) = aeval s p := by
  simp [toRealPoly,Polynomial.aeval_def,Polynomial.eval₂_map,← IsScalarTower.algebraMap_eq ℚ ℝ ℂ]

private theorem stable_of_margin (p : ℚ[X])
    (hp : ∀ s : ℂ, -(1/1000000000:ℝ) ≤ s.re → aeval s p ≠ 0) :
    StrictlyStable (toRealPoly p) := by
  constructor
  · intro h
    have hh := hp 0 (by norm_num)
    rw [← toRealPoly_aeval, h, map_zero] at hh
    exact hh rfl
  · intro s h
    by_contra! hs
    exact hp s (by linarith) (by simpa using h)

/-- The manuscript's rational controller is feasible as a real-polynomial controller. -/
theorem witness_feasible : Feasible (98236947/100000000) := by
  refine ⟨toRealPoly controllerX,toRealPoly controllerY,
    stable_of_margin _ (fun _ h => (controller_root_margin h).1),
    stable_of_margin _ (fun _ h => (controller_root_margin h).2.1),?_,?_⟩
  · simp [toRealPoly,controller_degrees.1,controller_degrees.2.1]
  · have hz := stable_of_margin controllerZ (fun _ h => (controller_root_margin h).2.2)
    rw [controllerZ_relation] at hz
    simpa [toRealPoly,witnessDelta,deltaNum,deltaDen] using hz

noncomputable def witnessT : ℝ := Real.sqrt (1763053/198236947)

theorem witnessT_spec : witnessT^2 = (1-(98236947/100000000:ℝ))/(1+98236947/100000000) ∧
    0 < witnessT ∧ witnessT < 1/10 := by
  have h : witnessT^2 = (1763053/198236947:ℝ) := Real.sq_sqrt (by norm_num)
  have hpos : 0 < witnessT := Real.sqrt_pos.2 (by norm_num)
  refine ⟨by rw [h]; norm_num,hpos,?_⟩
  nlinarith

end BelgianChocolate.ControlWitness

