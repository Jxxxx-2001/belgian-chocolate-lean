import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

namespace BelgianChocolate.ControlWitness
open Complex Set

private theorem dslope_factor {f : ℂ → ℂ} (v z : ℂ) :
    (z-v)*dslope f v z = f z-f v := sub_smul_dslope f v z

/-- An analytic function with one simple zero has a nonvanishing analytic factor. -/
theorem one_simple_factor {s : Set ℂ} {f : ℂ → ℂ} {v : ℂ}
    (hf : ∀ z ∈ s, AnalyticAt ℂ f z) (hv : f v = 0) (hd : deriv f v ≠ 0)
    (hzero : ∀ z ∈ s, f z = 0 → z=v) :
    ∃ a : ℂ → ℂ, (∀ z, f z=(z-v)*a z) ∧
      ∀ z ∈ s, AnalyticAt ℂ a z ∧ a z ≠ 0 := by
  refine ⟨dslope f v,fun z => ?_,fun z hz => ⟨(hf z hz).dslope v,?_⟩⟩
  · simpa [hv] using (dslope_factor (f := f) v z).symm
  · by_cases he : z=v
    · simpa [he,dslope_same] using hd
    · intro e
      have hh := dslope_factor (f := f) v z
      rw [e,hv,mul_zero,sub_zero] at hh
      exact he (hzero z hz hh.symm)

/-- Removing two distinct simple zeros gives a global factorization with an analytic
unit on the region containing those zeros. -/
theorem two_simple_factors {s : Set ℂ} {f : ℂ → ℂ} {v w : ℂ}
    (hvw : v ≠ w) (hw : w ∈ s) (hf : ∀ z ∈ s, AnalyticAt ℂ f z)
    (hv0 : f v = 0) (hw0 : f w = 0) (hdv : deriv f v ≠ 0) (hdw : deriv f w ≠ 0)
    (hzero : ∀ z ∈ s, f z = 0 → z=v ∨ z=w) :
    ∃ b : ℂ → ℂ, (∀ z, f z=(z-v)*(z-w)*b z) ∧
      ∀ z ∈ s, AnalyticAt ℂ b z ∧ b z ≠ 0 := by
  let g := dslope f v
  have hfac (z : ℂ) : f z=(z-v)*g z := by
    simpa [g,hv0] using (dslope_factor (f := f) v z).symm
  have hgw : g w=0 := (mul_eq_zero.mp ((hfac w).symm.trans hw0)).resolve_left
    (sub_ne_zero.mpr hvw.symm)
  have hga (z : ℂ) (hz : z∈s) : AnalyticAt ℂ g z := (hf z hz).dslope v
  have hgd : deriv g w ≠ 0 := by
    intro e
    have hlin : HasDerivAt (fun z : ℂ => z-v) 1 w := (hasDerivAt_id w).sub_const v
    have hh := hlin.mul (hga w hw).differentiableAt.hasDerivAt
    have he : f = (fun z : ℂ => z-v)*g := funext hfac
    apply hdw
    rw [he,hh.deriv,hgw,e]
    simp
  have hgz (z : ℂ) (hz : z∈s) (hg : g z=0) : z=w := by
    rcases hzero z hz (by rw [hfac z,hg,mul_zero]) with h|h
    · subst z
      exact (hdv (by simpa [g,dslope_same] using hg)).elim
    · exact h
  obtain ⟨b,hb,hu⟩ := one_simple_factor hga hgw hgd hgz
  exact ⟨b,fun z => by rw [hfac,hb,mul_assoc],hu⟩

end BelgianChocolate.ControlWitness

