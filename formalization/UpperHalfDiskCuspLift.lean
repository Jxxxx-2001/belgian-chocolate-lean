import UpperHalfDiskPuncture
import ModularLambdaCuspMonodromy
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import Mathlib.Tactic.Ring

/-! A physical positive circle may start at any phase. A modular one-cusp deck
step along that circle supplies a based lift to the cusp cover on the half-disc. -/

namespace BelgianChocolate.UpperHalfDisk

open Complex Metric Set UpperHalfPlane
open scoped MatrixGroups
open BelgianChocolate.ModularLambdaRatio

/-- The known orientation of a concrete circle makes it a generator, even when
the source basepoint is the left foot instead of the right foot. -/
theorem circleMap_generates_of_starConvex {V : Set ℂ} {p : ℂ} {r : ℝ}
    (hstar : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) {a : ↥(V \ {p})} (γ : Path a a)
    (θ : ℝ) (hγ : ∀ u : unitInterval,
      (γ u : ℂ) = circleMap p r (θ + 2 * Real.pi * u)) :
    Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = ⊤ := by
  have hi := (hstar.fundamentalGroup_map_directionFrom_bijective hr hS a).injective
  apply Circle.zpowers_fromPath_eq_top_of_degree_map_eq_one hi
  let angle (u : unitInterval) : ℝ := θ + 2 * Real.pi * u
  apply Circle.degree_eq_of_sub_eq _ (θ := angle) (by unfold angle; fun_prop)
  · intro u
    apply Subtype.ext
    change (Circle.exp (angle u) : ℂ) = (p.directionFrom V (γ u) : ℂ)
    rw [Circle.coe_exp, Complex.coe_directionFrom_apply, hγ, circleMap, add_sub_cancel_left]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr, norm_exp_ofReal_mul_I, mul_one]
    apply (eq_div_iff (ofReal_ne_zero.mpr hr.ne')).2
    exact mul_comm _ _
  · simp [angle]

theorem circleMap_generates {t r : ℝ} (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain) {a : Punctured t} (γ : Path a a)
    (θ : ℝ) (hγ : ∀ u : unitInterval,
      (γ u : ℂ) = circleMap (puncture t) r (θ + 2 * Real.pi * u)) :
    Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = ⊤ :=
  circleMap_generates_of_starConvex (domain_convex.starConvex (puncture_mem ht ht1)) hr hS γ θ hγ

/-- A B-labelled positive circle produces the single-valued lift to the filled
cusp coordinate, initially valued in the punctured disc. The initial value is
the marked projection of the specified modular fibre point. -/
theorem existsUnique_cuspULift_of_circleMap_oneCuspDeck {t r : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hr : 0 < r)
    (hS : sphere (puncture t) r ⊆ domain) (f : C(Punctured t, ({0,1}ᶜ : Set ℂ)))
    {a : Punctured t} (γ : Path a a) (θ : ℝ)
    (hγ : ∀ u : unitInterval, (γ u : ℂ) = circleMap (puncture t) r (θ + 2 * Real.pi * u))
    (e : lambdaPunctured ⁻¹' {f a})
    (hdeck : (lambdaPunctured_isCoveringMap.monodromy (.mk (γ.map f.continuous)) e : ℍ) =
      oneCuspDeck • (e : ℍ)) :
    ∃! F : C(Punctured t, PuncturedUnitDisc),
      F a = markedCuspDisc e ∧ cuspUPunctured ∘ F = f := by
  let _ := pathConnectedSpace ht ht1 hr hS
  exact existsUnique_lift_of_generatingLoop_monodromy γ
    (circleMap_generates ht ht1 hr hS γ θ hγ) cuspUPunctured_isCoveringMap f
    ((cuspUPunctured_markedCuspDisc e).trans e.2)
    (cuspU_monodromy_eq_self_of_oneCuspDeck (γ.map f.continuous) e hdeck)

#print axioms circleMap_generates
#print axioms existsUnique_cuspULift_of_circleMap_oneCuspDeck

/-- Transporting a generating circle along a tail gives a generator at its initial point. -/
theorem tailedLoop_generates {A : Type*} [TopologicalSpace A] {b c : A}
    (tail : Path b c) (round : Path c c)
    (hgen : Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk round)) = ⊤) :
    Subgroup.zpowers (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((tail.trans round).trans tail.symm))) = ⊤ := by
  let E := (FundamentalGroup.fundamentalGroupMulEquivOfPath tail).symm
  have hclass :
      E (FundamentalGroup.fromPath (.mk round)) =
        FundamentalGroup.fromPath (.mk ((tail.trans round).trans tail.symm)) := by
    dsimp only [E]
    rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc]
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := E.surjective x
  have hy : y ∈ Subgroup.zpowers (FundamentalGroup.fromPath (.mk round)) := by
    rw [hgen]
    exact Subgroup.mem_top _
  obtain ⟨n, rfl⟩ := hy
  rw [map_zpow, hclass]
  exact Subgroup.zpow_mem_zpowers _ _

/-- A B-labelled positive tailed circle gives a based cusp lift on an open star-convex domain. -/
theorem existsUnique_cuspULift_of_tailed_circleMap_oneCuspDeck
    {V : Set ℂ} {p : ℂ} {r : ℝ}
    (hstar : StarConvex ℝ p V) (hOpen : IsOpen V)
    (hr : 0 < r) (hS : sphere p r ⊆ V)
    (f : C(↥(V \ {p}), ({0,1}ᶜ : Set ℂ)))
    {b a : ↥(V \ {p})} (tail : Path b a) (round : Path a a) (θ : ℝ)
    (hγ : ∀ u : unitInterval, (round u : ℂ) = circleMap p r (θ + 2 * Real.pi * u))
    (e : lambdaPunctured ⁻¹' {f b})
    (hdeck : (lambdaPunctured_isCoveringMap.monodromy
      (.mk (((tail.trans round).trans tail.symm).map f.continuous)) e : ℍ) =
      oneCuspDeck • (e : ℍ)) :
    ∃! F : C(↥(V \ {p}), PuncturedUnitDisc),
      F b = markedCuspDisc e ∧ cuspUPunctured ∘ F = f := by
  let _ := hstar.pathConnectedSpace_diff_singleton (by simp [Complex.rank_real_complex]) hr hS
  let _ : LocallyPathConnectedSpace ↥(V \ {p}) :=
    (hOpen.sdiff isClosed_singleton).locallyPathConnectedSpace
  exact existsUnique_lift_of_generatingLoop_monodromy _
    (tailedLoop_generates tail round (circleMap_generates_of_starConvex hstar hr hS round θ hγ))
    cuspUPunctured_isCoveringMap f ((cuspUPunctured_markedCuspDisc e).trans e.2)
    (cuspU_monodromy_eq_self_of_oneCuspDeck
      (((tail.trans round).trans tail.symm).map f.continuous) e hdeck)

#print axioms existsUnique_cuspULift_of_tailed_circleMap_oneCuspDeck

end BelgianChocolate.UpperHalfDisk




