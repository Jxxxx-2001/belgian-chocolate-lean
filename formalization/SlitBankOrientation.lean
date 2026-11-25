import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! Boundary order on a straight real arc of a holomorphic upper half-plane
map. The vertical difference quotients are nonnegative at real boundary values. -/
namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Filter Topology

theorem monotoneOn_real_boundary {g : ℂ → ℂ} {D : Set ℝ}
    (hD : IsOpen D) (hconv : Convex ℝ D)
    (hcont : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hhol : DifferentiableOn ℂ g {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (g z).im)
    (hreal : ∀ x ∈ D, (g (x : ℂ)).im = 0) :
    MonotoneOn (fun x : ℝ => (g (x : ℂ)).re) D := by
  let V : Set ℂ := Complex.re ⁻¹' D
  have hVo : IsOpen V := hD.preimage continuous_re
  have hsym : MapsTo (starRingEnd ℂ) V V := by intro z hz; simpa [V] using hz
  let G := TauCeti.schwarzReflection g
  have hG : DifferentiableOn ℂ G V :=
    TauCeti.differentiableOn_schwarzReflection_of_symmetric hVo hsym
      (hcont.mono inter_subset_right) (hhol.mono inter_subset_right) (by
        intro z hz hzre
        have he : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [hzre])
        simpa only [he] using hreal z.re hz)
  have hagree (x : ℝ) : G (x : ℂ) = g (x : ℂ) :=
    TauCeti.schwarzReflection_of_im_nonneg (by simp)
  have hdiff (x : ℝ) (hx : x ∈ D) : HasDerivAt G (deriv G (x : ℂ)) (x : ℂ) :=
    (hG.differentiableAt (hVo.mem_nhds (show (x : ℂ) ∈ V from hx))).hasDerivAt
  have hrealder (x : ℝ) (hx : x ∈ D) :
      HasDerivAt (fun t : ℝ => (g (t : ℂ)).re) (deriv G (x : ℂ)).re x := by
    simpa only [hagree] using (hdiff x hx).real_of_complex
  apply monotoneOn_of_deriv_nonneg hconv
  · exact fun x hx ↦ (hrealder x hx).continuousAt.continuousWithinAt
  · exact fun x hx ↦ (hrealder x (interior_subset hx)).differentiableAt.differentiableWithinAt
  intro x hx
  have hxD := interior_subset hx
  rw [(hrealder x hxD).deriv]
  let v : ℂ → ℂ := fun t ↦ (x : ℂ) + I * t
  have hv : HasDerivAt v I 0 := by
    simpa [v] using (((hasDerivAt_id (0 : ℂ)).const_mul I).const_add (x : ℂ))
  have hcx : v 0 = (x : ℂ) := by simp [v]
  have hgc : HasDerivAt G (deriv G (x : ℂ)) (v 0) := hcx.symm ▸ hdiff x hxD
  have hline : HasDerivAt (fun t : ℂ ↦ -I * G (v t)) (deriv G (x : ℂ)) 0 := by
    have ke (k : ℂ) : -I * (k * I) = k := by
      calc
        _ = -(I^2) * k := by ring
        _ = k := by simp
    convert (hgc.comp 0 hv).const_mul (-I) using 1 <;> first | rfl | exact (ke _).symm
  let f : ℝ → ℝ := fun t ↦ (-I * G (v (t : ℂ))).re
  have hf : HasDerivAt f (deriv G (x : ℂ)).re 0 := hline.real_of_complex
  have hf₀ : f 0 = 0 := by simp [f, v, hagree, Complex.mul_re, hreal x hxD]
  apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hiv : (v (t : ℂ)).im = t := by simp [v, Complex.mul_im]
  have he : G (v (t : ℂ)) = g (v (t : ℂ)) :=
    TauCeti.schwarzReflection_of_im_nonneg (by rw [hiv]; exact ht.le)
  have hfpos : 0 ≤ f t := by
    simpa [f, he, Complex.mul_re] using hpos (v (t : ℂ)) (hiv.symm ▸ ht)
  simpa [slope, hf₀, smul_eq_mul] using mul_nonneg (inv_nonneg.mpr ht.le) hfpos

end BelgianChocolate.SlitBoundaryGeometry
