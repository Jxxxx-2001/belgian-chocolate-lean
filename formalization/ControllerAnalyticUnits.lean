import ControllerRemovableFactors

namespace BelgianChocolate.ControlWitness
open Complex Set
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Fill all removable values of the two auxiliary units on the marked domain.
At `u=it` the displayed numerator equals `1+z²/t²`. -/
theorem marked_analytic_units {s : Set ℂ} {f : ℂ → ℂ} {u : ℂ} (hu : u ≠ 0)
    (hum : -u ∈ s) (hf : ∀ z ∈ s, AnalyticAt ℂ f z)
    (h0 : f 0=0) (hp : f u=1) (hm : f (-u)=1)
    (hd0 : deriv f 0 ≠ 0) (hdp : deriv f u ≠ 0) (hdm : deriv f (-u) ≠ 0)
    (hz : ∀ z ∈ s, f z=0 → z=0)
    (ho : ∀ z ∈ s, f z=1 → z=u ∨ z= -u) :
    ∃ g a : ℂ → ℂ, ∀ z ∈ s, AnalyticAt ℂ g z ∧ AnalyticAt ℂ a z ∧
      g z ≠ 0 ∧ a z ≠ 0 ∧ g z*(1-f z)=1-z^2/u^2 ∧ g z-(1-z^2/u^2)=z*a z := by
  obtain ⟨v,hv,hvu⟩ := one_simple_factor hf h0 hd0 hz
  have hu' : u ≠ -u := by intro h; apply hu; linear_combination (1/2:ℂ)*h
  let q := fun z => f z-1
  have hd (z : ℂ) (hs : deriv f z ≠ 0) : deriv q z ≠ 0 := by
    simpa [q,deriv_sub_const] using hs
  obtain ⟨b,hb,hbu⟩ := two_simple_factors (f := q) hu' hum
    (fun z hz => (hf z hz).sub (show AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) z from analyticAt_const)) (by simp [q,hp]) (by simp [q,hm])
    (hd u hdp) (hd (-u) hdm) (fun z hz he => ho z hz (sub_eq_zero.mp he))
  let g := fun z => (1:ℂ)/(u^2*b z)
  refine ⟨g,fun z => g z*v z,fun z hzs => ?_⟩
  have hbn := (hbu z hzs).2
  have hdne := mul_ne_zero (pow_ne_zero 2 hu) hbn
  have hc : AnalyticAt ℂ (fun _ : ℂ => u^2) z := analyticAt_const
  have hc1 : AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) z := analyticAt_const
  have hga : AnalyticAt ℂ g z := hc1.div (hc.mul (hbu z hzs).1) hdne
  have hgn : g z ≠ 0 := div_ne_zero one_ne_zero hdne
  have he : g z*(1-f z)=1-z^2/u^2 := by
    have eq := hb z
    change f z-1 = _ at eq
    dsimp [g]
    field_simp [hu,hbn]
    linear_combination -eq
  refine ⟨hga,hga.mul (hvu z hzs).1,hgn,mul_ne_zero hgn (hvu z hzs).2,he,?_⟩
  have he' : f z=z*v z := by simpa using hv z
  rw [← he,he']
  ring

end BelgianChocolate.ControlWitness

