import SlitMassTransfer
import SlitPhysicalIndicator
import SlitChartTransition

namespace BelgianChocolate.SlitHarmonicMeasure

open Complex Set Metric
open BelgianChocolate.SlitBoundaryGeometry

/-- Increasing the slit strictly decreases the upper arc mass, with an
explicit two-parameter bound on the loss. -/
theorem upper_mass_variation {α β : ℝ} {A B : ℂ → ℂ} (hl : -1 < α) (hab : α < β)
    (hr : β < 0) (ha : CenteredUnfoldedChart α A) (hb : CenteredUnfoldedChart β B) :
    a β B < a α A ∧
    a α A - a β B ≤ 2 * Real.sqrt (β-α)/(Real.sqrt (β-α)+Real.sqrt (-β)) := by
  obtain ⟨K,hK⟩ := exists_slitChartTransition hab.le ha hb
  obtain ⟨H,hd,hpos,hlim⟩ := exists_upper_indicator hl (hab.trans hr) ha
  exact mass_outer_transfer hl hab hr ha hb curvedEdge_measurableSet curvedEdge_subset_frontier
    hK.holomorphic hK.continuous hK.mapsInterior hK.mapsClosed hK.center hK.physical hd hpos hlim

/-- Increasing the slit strictly decreases the lower arc mass by at most
the same moving-tip bound. -/
theorem lower_mass_variation {α β : ℝ} {A B : ℂ → ℂ} (hl : -1 < α) (hab : α < β)
    (hr : β < 0) (ha : CenteredUnfoldedChart α A) (hb : CenteredUnfoldedChart β B) :
    d β B < d α A ∧
    d α A - d β B ≤ 2 * Real.sqrt (β-α)/(Real.sqrt (β-α)+Real.sqrt (-β)) := by
  obtain ⟨K,hK⟩ := exists_slitChartTransition hab.le ha hb
  obtain ⟨H,hd,hpos,hlim⟩ := exists_lower_indicator hl (hab.trans hr) ha
  exact mass_outer_transfer hl hab hr ha hb lowerEdge_measurableSet lowerEdge_subset_frontier
    hK.holomorphic hK.continuous hK.mapsInterior hK.mapsClosed hK.center hK.physical hd hpos hlim

end BelgianChocolate.SlitHarmonicMeasure
