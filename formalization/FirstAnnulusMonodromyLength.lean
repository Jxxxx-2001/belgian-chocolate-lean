import FirstAnnulusStrip

namespace BelgianChocolate.FirstAnnulus
open Complex Set
open scoped MatrixGroups

/-- The positive loop in the logarithmic annulus runs upward through a height of `2π`. -/
noncomputable def logCenterSegment (L t : ℝ) (u : unitInterval) : ℂ :=
  ⟨L / 2, t + 2*Real.pi*(u : ℝ)⟩

private theorem logCenterSegment_mem {L : ℝ} (hL : 0 < L) (t : ℝ) (u : unitInterval) :
    logCenterSegment L t u ∈ logStrip L := by
  change 0 < L/2 ∧ L/2 < L
  constructor <;> linarith

/-- The path in the half-plane traced out by the chosen holomorphic lift along the center loop. -/
noncomputable def liftCenterSegment {L : ℝ} (hL : 0 < L) (t : ℝ) {F : ℂ → ℂ}
    (hf : ContinuousOn F (logStrip L)) (hm : MapsTo F (logStrip L) {w | 0 < w.im}) :
    C(unitInterval, UpperHalfPlane) := by
  let c : C(unitInterval, ℂ) := ⟨logCenterSegment L t, by unfold logCenterSegment; simp_rw [Complex.mk_eq_add_mul_I]; fun_prop⟩
  refine ⟨fun u => ⟨F (c u), hm (logCenterSegment_mem hL t u)⟩, ?_⟩
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  exact hf.comp_continuous c.continuous (logCenterSegment_mem hL t)

@[simp] theorem liftCenterSegment_zero {L : ℝ} (hL : 0 < L) (t : ℝ) {F : ℂ → ℂ}
    (hf : ContinuousOn F (logStrip L)) (hm : MapsTo F (logStrip L) {w | 0 < w.im}) :
    ((liftCenterSegment hL t hf hm 0 : UpperHalfPlane) : ℂ) = F ⟨L/2,t⟩ := by
  simp [liftCenterSegment, logCenterSegment]

@[simp] theorem liftCenterSegment_one {L : ℝ} (hL : 0 < L) (t : ℝ) {F : ℂ → ℂ}
    (hf : ContinuousOn F (logStrip L)) (hm : MapsTo F (logStrip L) {w | 0 < w.im}) :
    ((liftCenterSegment hL t hf hm 1 : UpperHalfPlane) : ℂ) = F ⟨L/2,t + 2*Real.pi⟩ := by
  simp [liftCenterSegment, logCenterSegment]

/-- A matrix representing the covering monodromy of the projected center path satisfies
the length estimate, with its endpoint identified by path-lift uniqueness. -/
theorem logStrip_trace_length_le_of_monodromy {R : ℝ} (hR : 1 < R) (t : ℝ) {F : ℂ → ℂ}
    (hf : DifferentiableOn ℂ F (logStrip (Real.log R)))
    (hm : MapsTo F (logStrip (Real.log R)) {w | 0 < w.im})
    {X : Type*} [TopologicalSpace X] {P : UpperHalfPlane → X} (hc : IsCoveringMap P)
    (p : UpperHalfPlane) (h₀ : (p : ℂ) = F ⟨Real.log R/2,t⟩)
    (γ : Path (P p) (P p))
    (hγ : ∀ u, P (liftCenterSegment (Real.log_pos hR) t hf.continuousOn hm u) = γ u)
    (g : SL(2, ℝ))
    (hg : g • p = (hc.monodromy (.mk γ) ⟨p, rfl⟩ : UpperHalfPlane)) :
    2 * Real.arcosh (|(g : Matrix (Fin 2) (Fin 2) ℝ).trace|/2) ≤
      2*Real.pi^2/Real.log R := by
  let c := liftCenterSegment (Real.log_pos hR) t hf.continuousOn hm
  have hs : c 0 = p := UpperHalfPlane.ext ((liftCenterSegment_zero ..).trans h₀.symm)
  have he := hc.monodromy_eq_apply_one (e := ⟨p,rfl⟩) (γ := γ) (Γ := c) (funext hγ) hs
  exact logStrip_trace_length_le hR t hf hm g p h₀
    ((congrArg UpperHalfPlane.coe (hg.trans he)).trans (liftCenterSegment_one ..))

end BelgianChocolate.FirstAnnulus

