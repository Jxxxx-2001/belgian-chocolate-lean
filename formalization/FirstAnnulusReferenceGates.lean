import FirstAnnulusEmbedding
import FirstAnnulusHomotopySupport

namespace BelgianChocolate.FirstAnnulus
open Complex Metric Set unitInterval
open BelgianChocolate.FirstAnnulusPaths BelgianChocolate.FirstAnnulusHomotopySupport

private theorem cut_of_strict_im {t : ℝ} {z : ℂ} (hz : z ∈ ball 0 (1/t))
    (hi : z.im ≠ 0) : z ∈ cutDomain t := by
  refine ⟨mem_ball_zero_iff.mp hz, fun h ↦ hi h.1, ?_, ?_⟩
  · intro he
    exact hi (by simp [he])
  · intro he
    exact hi (by simp [he])

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
  have hs : cutDomain t ⊆ ball (0:ℂ) (1/t) := fun _ hx ↦ mem_ball_zero_iff.mpr hx.1
  have hp : p.Homotopic (γ.subpath 0 halfTurn) := by
    apply homotopic_of_weak_strict_linear_side (convex_ball (0:ℂ) (1/t)) hs imCLM.toLinearMap
    · intro z hz hi
      exact cut_of_strict_im hz (ne_of_gt hi)
    · exact hup
    · intro u hu₀ hu₁
      exact referenceLoop_upper_im ht ht' (param_mem hu₀ hu₁)
  have hq : q.Homotopic (γ.subpath halfTurn 1) := by
    apply homotopic_of_weak_strict_linear_side (convex_ball (0:ℂ) (1/t)) hs (-imCLM.toLinearMap)
    · intro z hz hi
      exact cut_of_strict_im hz (ne_of_lt (neg_pos.mp hi))
    · intro u hu₀ hu₁
      exact neg_nonneg.mpr (hlo u hu₀ hu₁)
    · intro u hu₀ hu₁
      exact neg_pos.mpr (referenceLoop_lower_im ht ht' (param_mem hu₀ hu₁))
  exact (hp.hcomp hq).trans (referenceLoop_halves ht ht')

end BelgianChocolate.FirstAnnulus
