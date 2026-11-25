import ModularLambdaCuspCover
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.Topology.Homotopy.Monodromy.Basic
import Mathlib.Analysis.Convex.PathConnected

/-! The punctured half-disc has a positive circle generator. A lift along that
circle is sufficient for the based lifting criterion on the whole punctured half-disc. -/

namespace BelgianChocolate.UpperHalfDisk

open Complex Metric Set Topology
open scoped Topology

/-- The open upper half of the unit disc. -/
def domain : Set ℂ := {z | ‖z‖ < 1 ∧ 0 < z.im}

/-- We use the point `it` as the puncture. -/
def puncture (t : ℝ) : ℂ := (t : ℂ) * Complex.I

abbrev Punctured (t : ℝ) := ↥(domain \ {puncture t})

theorem domain_isOpen : IsOpen domain := by
  change IsOpen ({z : ℂ | ‖z‖ < 1} ∩ {z : ℂ | 0 < z.im})
  exact (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const continuous_im)

theorem domain_convex : Convex ℝ domain := by
  have hd : domain = ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < z.im} := by
    ext z
    simp [domain]
  rw [hd]
  exact (convex_ball _ _).inter (convex_halfSpace_im_gt 0)

theorem puncture_mem {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : puncture t ∈ domain := by
  simp [domain, puncture, abs_of_pos ht, ht, ht1]

theorem exists_ball_subset {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ r : ℝ, 0 < r ∧ ball (puncture t) r ⊆ domain :=
  Metric.isOpen_iff.mp domain_isOpen (puncture t) (puncture_mem ht ht1)

private theorem star {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : StarConvex ℝ (puncture t) domain :=
  domain_convex.starConvex (puncture_mem ht ht1)

instance (t : ℝ) : LocallyPathConnectedSpace (Punctured t) :=
  (domain_isOpen.sdiff isClosed_singleton).locallyPathConnectedSpace

theorem pathConnectedSpace {t r : ℝ} (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain) : PathConnectedSpace (Punctured t) :=
  (star ht ht1).pathConnectedSpace_diff_singleton (by simp [Complex.rank_real_complex]) hr hS

/-- Radial projection onto a sufficiently small sphere is inverse to inclusion up to homotopy. -/
noncomputable def sphereEquiv {t r : ℝ} (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain) :
    ContinuousMap.HomotopyEquiv (sphere (puncture t) r) (Punctured t) :=
  (star ht ht1).sphereHomotopyEquiv hr hS

/-- Start on the right of the puncture. -/
noncomputable def circleBase {t r : ℝ} (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain) : Punctured t :=
  sphereEquiv ht ht1 hr hS ((TauCeti.sphereCircleHomeomorph (puncture t) hr).symm 1)

/-- A counterclockwise positive circuit around the puncture. -/
noncomputable def positiveCircle {t r : ℝ} (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain) :
    Path (circleBase ht ht1 hr hS) (circleBase ht ht1 hr hS) :=
  ((puncture t).sphereLoop hr).map (sphereEquiv ht ht1 hr hS).toFun.continuous

@[simp]
theorem coe_positiveCircle {t r : ℝ} (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain) (u : unitInterval) :
    (positiveCircle ht ht1 hr hS u : ℂ) = circleMap (puncture t) r (2 * Real.pi * u) := by
  change (sphereEquiv ht ht1 hr hS ((puncture t).sphereLoop hr u) : ℂ) = _
  rw [sphereEquiv, StarConvex.coe_sphereHomotopyEquiv_apply, Complex.coe_sphereLoop_apply]

theorem positiveCircle_generates {t r : ℝ} (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain) :
    Subgroup.zpowers (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (positiveCircle ht ht1 hr hS))) = ⊤ := by
  let x : sphere (puncture t) r := (TauCeti.sphereCircleHomeomorph (puncture t) hr).symm 1
  let W := (star ht ht1).fundamentalGroupMulEquivInt hr hS x
  apply W.zpowers_eq_top_of_apply_eq_ofAdd_one
  exact (star ht ht1).fundamentalGroupMulEquivInt_sphereLoop hr hS

section Lifting

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- A chosen fibre point extends to a lift when monodromy along a generating loop fixes it. -/
theorem existsUnique_lift_of_generatingLoop_monodromy {A : Type*} [TopologicalSpace A]
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] {a : A} (γ : Path a a)
    (hgen : Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = ⊤)
    {p : E → X} (hp : IsCoveringMap p) (f : C(A, X)) {e : E}
    (he : p e = f a)
    (hfix : hp.monodromy (.mk (γ.map f.continuous)) ⟨e, he⟩ = ⟨e, he⟩) :
    ∃! F : C(A, E), F a = e ∧ p ∘ F = f := by
  let g := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
  let J := (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range
  have hg : (FundamentalGroup.map f a) g ∈ J := by
    apply (hp.monodromy_eq_self_iff_mem_range ⟨e, he⟩ _).1
    simpa [g, Path.Homotopic.Quotient.mk_map] using hfix
  apply hp.existsUnique_continuousMap_lifts_of_range_le he
  rintro _ ⟨k, rfl⟩
  have hk : k ∈ Subgroup.zpowers g := by
    change k ∈ Subgroup.zpowers (FundamentalGroup.fromPath (.mk γ))
    rw [hgen]
    exact Subgroup.mem_top _
  obtain ⟨n, rfl⟩ := hk
  rw [map_zpow]
  exact J.zpow_mem hg n

/-- A based lift on the punctured upper half-disc exists uniquely if monodromy along the
positive circle fixes the chosen initial point. -/
theorem existsUnique_lift_of_positiveCircle_monodromy {t r : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain)
    {p : E → X} (hp : IsCoveringMap p) (f : C(Punctured t, X)) {e : E}
    (he : p e = f (circleBase ht ht1 hr hS))
    (hfix : hp.monodromy (.mk ((positiveCircle ht ht1 hr hS).map f.continuous))
      ⟨e, he⟩ = ⟨e, he⟩) :
    ∃! F : C(Punctured t, E), F (circleBase ht ht1 hr hS) = e ∧ p ∘ F = f := by
  let _ := pathConnectedSpace ht ht1 hr hS
  exact existsUnique_lift_of_generatingLoop_monodromy _ (positiveCircle_generates ht ht1 hr hS)
    hp f he hfix

/-- A closed lift of the single positive source circle suffices for a global based lift. -/
theorem existsUnique_lift_of_positiveCircle {t r : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain)
    {p : E → X} (hp : IsCoveringMap p) (f : C(Punctured t, X)) {e : E}
    (he : p e = f (circleBase ht ht1 hr hS))
    (η : Path e e) (hη : p ∘ η = f ∘ positiveCircle ht ht1 hr hS) :
    ∃! F : C(Punctured t, E), F (circleBase ht ht1 hr hS) = e ∧ p ∘ F = f := by
  apply existsUnique_lift_of_positiveCircle_monodromy ht ht1 hr hS hp f he
  apply Subtype.ext
  have hmap : p ∘ (η.toContinuousMap : unitInterval → E) =
      (((positiveCircle ht ht1 hr hS).map f.continuous) : unitInterval → X) := by
    exact hη
  exact (hp.monodromy_eq_apply_one (Γ := η.toContinuousMap)
    (e := (⟨e, he⟩ : p ⁻¹' {f (circleBase ht ht1 hr hS)})) hmap η.source).trans η.target

end Lifting

open BelgianChocolate.ModularLambdaRatio

/-- The positive-circle criterion for the actual modular cusp covering `U`. -/
theorem existsUnique_cuspULift_of_positiveCircle {t r : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain)
    (f : C(Punctured t, ({0,1}ᶜ : Set ℂ))) {e : PuncturedUnitDisc}
    (he : cuspUPunctured e = f (circleBase ht ht1 hr hS))
    (η : Path e e) (hη : cuspUPunctured ∘ η = f ∘ positiveCircle ht ht1 hr hS) :
    ∃! F : C(Punctured t, PuncturedUnitDisc),
      F (circleBase ht ht1 hr hS) = e ∧ cuspUPunctured ∘ F = f :=
  existsUnique_lift_of_positiveCircle ht ht1 hr hS cuspUPunctured_isCoveringMap f he η hη

#print axioms positiveCircle_generates
#print axioms existsUnique_lift_of_positiveCircle_monodromy
#print axioms existsUnique_cuspULift_of_positiveCircle

end BelgianChocolate.UpperHalfDisk




