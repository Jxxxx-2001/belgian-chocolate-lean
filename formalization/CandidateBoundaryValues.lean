import CandidateModularBoundary
import CuspSectorSign

namespace BelgianChocolate.CandidateModularBoundary
open Complex Real Set
open UpperHalfPlane hiding I I_re I_im
open scoped ComplexConjugate
open BelgianChocolate.ModularLambdaRatio BelgianChocolate.MarkedRealAxis

/-- Every point of the geometric curved edge is on the marked modular line
`re τ = 1`; this is the converse of the forward cusp parametrization. -/
theorem curvedEdge_exists_markedCusp {w : ℂ} (hw : w ∈ curvedEdge) :
    ∃ τ : ℍ, τ.re = 1 ∧ cusp (τ : ℂ) = w := by
  obtain ⟨θ, hθ, rfl⟩ := hw
  let a := Real.sqrt (θ * (Real.pi - θ))
  have ha : 0 < a := Real.sqrt_pos.2 (mul_pos hθ.1 (sub_pos.mpr hθ.2))
  have ha2 : a ^ 2 = θ * (Real.pi - θ) :=
    Real.sq_sqrt (mul_nonneg hθ.1.le (sub_nonneg.mpr hθ.2.le))
  let y := θ / a
  have hy : 0 < y := div_pos hθ.1 ha
  have hd : 0 < 1 + y^2 := by positivity
  have hA : Real.pi * y / (1+y^2) = a := by
    dsimp [y]
    field_simp
    nlinarith [ha2]
  have hB : Real.pi * y^2 / (1+y^2) = θ := by
    dsimp [y]
    field_simp
    rw [ha2]
    ring
  let τ : ℍ := ⟨⟨1,y⟩,hy⟩
  refine ⟨τ, rfl, ?_⟩
  have hn : Complex.normSq (τ : ℂ) = 1+y^2 := by simp [τ, Complex.normSq_apply, pow_two]
  have he : -((Real.pi : ℂ) * I) / (τ : ℂ) + (Real.pi : ℂ) * I =
      ((-a : ℝ) : ℂ) + (θ : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.div_re, hn, τ]
      rw [neg_div, hA]
    · simp [Complex.div_im, hn, τ]
      field_simp at hB ⊢
      nlinarith
  unfold cusp
  calc
    -Complex.exp _ = Complex.exp (-((Real.pi : ℂ) * I) / (τ : ℂ) + (Real.pi : ℂ) * I) := by
      rw [Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    _ = _ := by rw [he, Complex.exp_add, Complex.ofReal_exp]

theorem cuspU_curvedEdge_negative {w : ℂ} (hw : w ∈ curvedEdge) :
    (cuspU w).im = 0 ∧ (cuspU w).re < 0 := by
  obtain ⟨τ, hτ, rfl⟩ := curvedEdge_exists_markedCusp hw
  exact cuspU_marked_one_axis τ hτ

theorem cuspU_conj {w : ℂ} (hw : ‖w‖ < 1) : cuspU (conj w) = conj (cuspU w) := by
  unfold cuspU
  rw [← map_neg, BelgianChocolate.CuspSectorSign.cuspLambda_conj
    (by simpa only [norm_neg] using hw), map_sub, map_one]

theorem cuspU_real_interval {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 0) :
    (cuspU (x : ℂ)).im = 0 ∧ cuspU (x : ℂ) ∈ ({0,1}ᶜ : Set ℂ) := by
  have hn : ‖(x : ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨hx.1, by linarith [hx.2]⟩
  have hs := cuspU_conj hn
  simp only [conj_ofReal] at hs
  refine ⟨(Complex.conj_eq_iff_im.mp hs.symm), ?_⟩
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨cuspU_ne_zero hn, fun h => (Complex.ofReal_ne_zero.mpr hx.2.ne)
    ((cuspU_eq_one_iff hn).mp h)⟩

end BelgianChocolate.CandidateModularBoundary
