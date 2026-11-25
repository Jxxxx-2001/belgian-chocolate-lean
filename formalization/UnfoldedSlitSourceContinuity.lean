import UnfoldedSlitPhysicalSides
import JoukowskiHalfDisk
import ComparisonSourceBoundary

/-! Continuous extension of the three-point-normalized unfolded chart at
the pole of the half-disc Joukowski coordinate. -/
namespace BelgianChocolate.SlitBoundaryGeometry
open Complex Set Filter Metric Topology Bornology
open BelgianChocolate.HarmonicComparison
open BelgianChocolate.NormalizationCenter
open BelgianChocolate.SlitSquareRoot

noncomputable def diskUnfoldedExtension (α : ℝ) (F : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ F (-joukowski z)) 0 (upperBankEnd α)

@[simp] theorem diskUnfoldedExtension_zero (α : ℝ) (F : ℂ → ℂ) :
    diskUnfoldedExtension α F 0 = upperBankEnd α := by simp [diskUnfoldedExtension]

theorem diskUnfoldedExtension_of_ne_zero (α : ℝ) (F : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    diskUnfoldedExtension α F z = F (-joukowski z) := by simp [diskUnfoldedExtension,hz]

theorem tendsto_neg_joukowski_pole :
    Tendsto (fun z : ℂ ↦ -joukowski z) (𝓝[≠] 0) (cobounded ℂ) := by
  apply tendsto_norm_atTop_iff_cobounded.mp
  have hinv : Tendsto (fun z : ℂ ↦ ‖z⁻¹‖) (𝓝[≠] 0) atTop :=
    tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero
  have hsmall : ∀ᶠ z : ℂ in 𝓝[≠] 0, ‖z‖ < 1 :=
    Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) zero_lt_one))
      (fun _ hz ↦ mem_ball_zero_iff.mp hz)
  refine tendsto_atTop.mpr fun A ↦ ?_
  filter_upwards [hsmall,hinv.eventually (eventually_ge_atTop (A+1))] with z hz hz'
  have htri := norm_sub_le (z + z⁻¹) z
  rw [add_sub_cancel_left] at htri
  simp only [norm_neg,joukowski]
  linarith

private theorem neg_joukowski_closed_maps :
    MapsTo (fun z : ℂ ↦ -joukowski z) (closure comparisonHalfDisk \ {0}) {w : ℂ | 0 ≤ w.im} := by
  rintro z ⟨hz,hne⟩
  rw [closure_comparisonHalfDisk] at hz
  change z ≠ 0 at hne
  have hpos : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) _
  have hsq : ‖z‖ ^ 2 ≤ 1 := by nlinarith [hz.1, norm_nonneg z]
  have hinv : 1 ≤ (‖z‖ ^ 2)⁻¹ := by
    rw [inv_eq_one_div,le_div_iff₀ hpos,one_mul]; exact hsq
  change 0 ≤ (-joukowski z).im
  rw [Complex.neg_im, neg_nonneg,joukowski_im]
  exact mul_nonpos_of_nonneg_of_nonpos hz.2 (sub_nonpos.mpr hinv)

theorem UnfoldedHalfPlaneChart.continuousOn_diskUnfoldedExtension {α : ℝ} {F : ℂ → ℂ}
    (h : UnfoldedHalfPlaneChart α F) : ContinuousOn (diskUnfoldedExtension α F) (closure comparisonHalfDisk) := by
  rw [diskUnfoldedExtension,continuousOn_update_iff]
  constructor
  · apply h.cont.comp _ neg_joukowski_closed_maps
    exact fun z hz ↦ (hasDerivAt_joukowski (show z ≠ 0 from hz.2)).continuousAt.neg.continuousWithinAt
  · intro _
    apply h.at_infty.comp
    refine tendsto_inf.mpr ⟨tendsto_neg_joukowski_pole.mono_left (nhdsWithin_mono _ fun _ hx ↦ hx.2), ?_⟩
    exact tendsto_principal.mpr (Filter.mem_of_superset self_mem_nhdsWithin neg_joukowski_closed_maps)

private theorem upper_eventually_halfDisk :
    ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] 0, z ∈ comparisonHalfDisk := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) zero_lt_one)] with z hz hb
  exact ⟨hb,hz⟩

theorem UnfoldedHalfPlaneChart.unfolding_folded_extension_at_zero {α : ℝ} {F : ℂ → ℂ}
    (h : UnfoldedHalfPlaneChart α F) :
    Tendsto (fun z ↦ unfolding α (folding α (diskUnfoldedExtension α F z)))
      (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝 (upperBankEnd α)) := by
  have hzero : (0 : ℂ) ∈ closure comparisonHalfDisk := by rw [closure_comparisonHalfDisk]; simp
  have hId : Tendsto id (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝[closure comparisonHalfDisk] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left nhdsWithin_le_nhds,
      upper_eventually_halfDisk.mono fun _ hz ↦ subset_closure hz⟩
  have hlim := (h.continuousOn_diskUnfoldedExtension 0 hzero).tendsto.comp hId
  rw [diskUnfoldedExtension_zero] at hlim
  apply hlim.congr'
  filter_upwards [upper_eventually_halfDisk] with z hz
  have hnorm : z ∈ UpperHalfDisk.domain := by
    rw [comparisonHalfDisk_eq_norm] at hz
    exact hz
  have hne : z ≠ 0 := by rintro rfl; exact (lt_irrefl 0) hnorm.2
  have him : 0 < (-joukowski z).im := by
    rw [Complex.neg_im,neg_pos]
    exact joukowski_mapsTo hnorm
  change diskUnfoldedExtension α F z = unfolding α (folding α (diskUnfoldedExtension α F z))
  rw [diskUnfoldedExtension_of_ne_zero _ _ hne,
    unfolding_folding_of_re_pos (h.interior_bij.mapsTo him).1]

end BelgianChocolate.SlitBoundaryGeometry
