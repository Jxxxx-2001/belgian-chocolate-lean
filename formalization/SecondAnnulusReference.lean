import SourceDiskPaths
import FirstAnnulusEmbedding
import FirstAnnulusHomotopySupport

namespace BelgianChocolate.SecondAnnulusTopology
open Complex Metric Set unitInterval
open BelgianChocolate.SourceDiskPaths
open BelgianChocolate.FirstAnnulus (positiveCircleLoop halfTurn)
open BelgianChocolate.FirstAnnulusHomotopySupport

/-- The positive reference circle meets the two outermost marked peripheral
circles at their own outer real intercepts. -/
noncomputable def referenceCircle {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    C(Circle, scaledDisk t) where
  toFun ζ := ⟨(6/5:ℂ)*(ζ:ℂ), by
    have h : ‖(6/5:ℂ)*(ζ:ℂ)‖ = 6/5 := by
      rw [norm_mul, Circle.norm_coe]; norm_num
    have hR : 10 ≤ 1/t := (le_div_iff₀ ht).mpr (by linarith)
    refine ⟨by rw [h]; linarith, ?_, ?_, ?_⟩ <;> intro he <;> rw [he] at h <;> norm_num at h⟩
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

noncomputable def referenceLoop {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :=
  positiveCircleLoop.map (referenceCircle ht ht').continuous

theorem referenceLoop_formula {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (s : unitInterval) :
    (((referenceLoop ht ht') s : scaledDisk t):ℂ) =
      (6/5:ℂ)*Complex.exp ((((2*Real.pi)*(s:ℝ):ℝ):ℂ)*Complex.I) := rfl

theorem referenceLoop_im {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (s : unitInterval) :
    (((referenceLoop ht ht') s : scaledDisk t):ℂ).im = (6/5)*Real.sin (2*Real.pi*(s:ℝ)) := by
  have he (u : ℝ) : (Complex.exp ((u:ℂ)*Complex.I)).im = Real.sin u := by
    simp [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [referenceLoop_formula]
  generalize 2*Real.pi*(s:ℝ) = θ
  simp only [Complex.mul_im]
  norm_num [he]

theorem referenceLoop_gate_values {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    (((referenceLoop ht ht') 0 : scaledDisk t):ℂ) = 6/5 ∧
    (((referenceLoop ht ht') halfTurn : scaledDisk t):ℂ) = -6/5 ∧
    (((referenceLoop ht ht') 1 : scaledDisk t):ℂ) = 6/5 := by
  have hz : (((referenceLoop ht ht') 0 : scaledDisk t):ℂ) = 6/5 := by
    rw [referenceLoop_formula]
    norm_num
  refine ⟨hz, ?_, ?_⟩
  · rw [referenceLoop_formula]
    change (6/5:ℂ)*Complex.exp ((((2*Real.pi)*(1/2):ℝ):ℂ)*Complex.I) = -6/5
    rw [show (2*Real.pi)*(1/2:ℝ) = Real.pi by ring, Complex.exp_pi_mul_I]
    ring
  · rw [show (referenceLoop ht ht') 1 = (referenceLoop ht ht') 0 from
      (referenceLoop ht ht').target.trans (referenceLoop ht ht').source.symm]
    exact hz

theorem referenceLoop_halves {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    let γ := referenceLoop ht ht'
    ((γ.subpath 0 halfTurn).trans (γ.subpath halfTurn 1)).Homotopic
      (γ.cast γ.source γ.target) := by
  dsimp only
  rw [← Path.subpath_zero_one]
  exact Path.Homotopic.subpath_trans_subpath _ _ _ _

theorem referenceLoop_upper_im {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {s : unitInterval} (hs : (s:ℝ) ∈ Ioo 0 1) :
    0 < ((((referenceLoop ht ht').subpath 0 halfTurn s : scaledDisk t):ℂ)).im := by
  change 0 < (((referenceLoop ht ht') (Icc.convexComb 0 halfTurn s) : scaledDisk t):ℂ).im
  rw [referenceLoop_im, Icc.coe_convexComb]
  apply mul_pos (by norm_num)
  apply Real.sin_pos_of_pos_of_lt_pi <;> dsimp [halfTurn] <;>
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos hs.1,
      mul_pos Real.pi_pos (sub_pos.mpr hs.2)]

theorem referenceLoop_lower_im {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {s : unitInterval} (hs : (s:ℝ) ∈ Ioo 0 1) :
    ((((referenceLoop ht ht').subpath halfTurn 1 s : scaledDisk t):ℂ)).im < 0 := by
  change (((referenceLoop ht ht') (Icc.convexComb halfTurn 1 s) : scaledDisk t):ℂ).im < 0
  rw [referenceLoop_im, Icc.coe_convexComb]
  apply mul_neg_of_pos_of_neg (by norm_num)
  let θ := 2*Real.pi*((1-(s:ℝ))*(1/2)+(s:ℝ)*1)
  change Real.sin θ < 0
  rw [← Real.sin_sub_two_pi]
  apply Real.sin_neg_of_neg_of_neg_pi_lt <;> dsimp [θ] <;>
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos hs.1,
      mul_pos Real.pi_pos (sub_pos.mpr hs.2)]


theorem disk_of_strict_im {t : ℝ} {z : ℂ} (hz : z ∈ ball 0 (1/t))
    (hi : z.im ≠ 0) : z ∈ scaledDisk t := by
  refine ⟨mem_ball_zero_iff.mp hz, ?_, ?_, ?_⟩ <;> intro he <;> exact hi (by simp [he])

private theorem param_mem {u : unitInterval} (hu₀ : u ≠ 0) (hu₁ : u ≠ 1) : (u:ℝ) ∈ Ioo 0 1 :=
  ⟨lt_of_le_of_ne u.2.1 (fun h ↦ hu₀ (Subtype.ext h.symm)),
    lt_of_le_of_ne u.2.2 (fun h ↦ hu₁ (Subtype.ext h))⟩

/-- Weak upper and lower paths between the two real gates have the homotopy
class of the actual reference circle when traversed in that order. -/
theorem reference_class_of_weak_half_paths {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    (p : Path (referenceLoop ht ht' 0) (referenceLoop ht ht' halfTurn))
    (q : Path (referenceLoop ht ht' halfTurn) (referenceLoop ht ht' 1))
    (hup : ∀ u : unitInterval, u ≠ 0 → u ≠ 1 → 0 ≤ (p u : ℂ).im)
    (hlo : ∀ u : unitInterval, u ≠ 0 → u ≠ 1 → (q u : ℂ).im ≤ 0) :
    (p.trans q).Homotopic ((referenceLoop ht ht').cast (referenceLoop ht ht').source
      (referenceLoop ht ht').target) := by
  let γ := referenceLoop ht ht'
  have hs : scaledDisk t ⊆ ball (0:ℂ) (1/t) := fun _ hx ↦ mem_ball_zero_iff.mpr hx.1
  have hp : p.Homotopic (γ.subpath 0 halfTurn) := by
    apply homotopic_of_weak_strict_linear_side (convex_ball (0:ℂ) (1/t)) hs imCLM.toLinearMap
    · intro z hz hi
      exact disk_of_strict_im hz (ne_of_gt hi)
    · exact hup
    · intro u hu₀ hu₁
      exact referenceLoop_upper_im ht ht' (param_mem hu₀ hu₁)
  have hq : q.Homotopic (γ.subpath halfTurn 1) := by
    apply homotopic_of_weak_strict_linear_side (convex_ball (0:ℂ) (1/t)) hs (-imCLM.toLinearMap)
    · intro z hz hi
      exact disk_of_strict_im hz (ne_of_lt (neg_pos.mp hi))
    · intro u hu₀ hu₁
      exact neg_nonneg.mpr (hlo u hu₀ hu₁)
    · intro u hu₀ hu₁
      exact neg_pos.mpr (referenceLoop_lower_im ht ht' (param_mem hu₀ hu₁))
  exact (hp.hcomp hq).trans (referenceLoop_halves ht ht')

end BelgianChocolate.SecondAnnulusTopology

