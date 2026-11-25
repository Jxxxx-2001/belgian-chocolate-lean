import CandidateBalancedChart

namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set
open BelgianChocolate.SlitHarmonicMeasure BelgianChocolate.HarmonicComparison
open BelgianChocolate.CandidateReflection

/-- The strict inclusion is witnessed by the longer slit tip itself. -/
theorem candidateSlit_ne_of_lt {α β : ℝ} (hl : -1 < α) (hab : α < β) (hr : β < 0) :
    candidateSlit α ≠ candidateSlit β := by
  have hb : (β : ℂ) ∈ radialDomain := by
    change ‖(β : ℂ)‖ < radialRadius _
    simp [radialRadius, abs_of_neg hr]; linarith
  have hA : (β : ℂ) ∈ candidateSlit α := ⟨hb, fun hs => hab.not_ge hs.2.2⟩
  have hB : (β : ℂ) ∉ candidateSlit β :=
    fun hs => hs.2 ⟨by simp,(hl.trans hab).le,le_rfl⟩
  exact fun he => hB (he ▸ hA)

/-- Two balanced slits produce realized candidates; rigidity identifies their
physical images and hence their slit tips. -/
theorem balanced_slit_parameter_unique {α β : ℝ} {F G : ℂ → ℂ}
    (hα : α ∈ Ioo (-1 : ℝ) 0) (hβ : β ∈ Ioo (-1 : ℝ) 0)
    (hF : CenteredUnfoldedChart α F) (hG : CenteredUnfoldedChart β G)
    (ha : a α F = b α F) (hb : a β G = b β G) : α = β := by
  obtain ⟨t,ht,Φ,hΦb,hΦ,hP,-,-⟩ := exists_candidate_of_balanced_slit hα.1 hα.2 hF ha
  obtain ⟨u,hu,Ψ,hΨb,hΨ,hQ,-,-⟩ := exists_candidate_of_balanced_slit hβ.1 hβ.2 hG hb
  obtain ⟨f,hf,hs,hrep,-⟩ := exists_marked_realization_of_comparisonCandidate ht.1 ht.2 hα.1
    hΦ hΦb.injOn hΦb.mapsTo hP
  obtain ⟨g,hg,hs',hrep',-⟩ := exists_marked_realization_of_comparisonCandidate hu.1 hu.2 hβ.1
    hΨ hΨb.injOn hΨb.mapsTo hQ
  obtain ⟨-,he,-⟩ := comparison_candidate_unique ht.1 ht.2 hu.1 hu.2 hΦ hΨ hf hg hs hs' hrep hrep'
  have hr : candidateSlit α = candidateSlit β := hΦb.image_eq.symm.trans
    ((image_congr he).trans hΨb.image_eq)
  exact le_antisymm (le_of_not_gt fun h => candidateSlit_ne_of_lt hβ.1 h hα.2 hr.symm)
    (le_of_not_gt fun h => candidateSlit_ne_of_lt hα.1 h hβ.2 hr)

end BelgianChocolate.SlitBoundaryGeometry
