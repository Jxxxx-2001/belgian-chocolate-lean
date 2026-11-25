import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-! Conditional transport for the first annulus.
The geometric homotopy and the modular covering are separate obligations.
`Path.trans` follows its left path first.
-/
namespace BelgianChocolate.FirstAnnulusTransport

open Path.Homotopic

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable {p : E → X}

/-- Covering transport follows paths in execution order. -/
theorem transport_trans (hp : IsCoveringMap p) {a b c : X}
    (γ : Path a b) (δ : Path b c) (e : p ⁻¹' {a}) :
    hp.monodromy (.mk (γ.trans δ)) e =
      hp.monodromy (.mk δ) (hp.monodromy (.mk γ) e) := by
  rw [Path.Homotopic.Quotient.mk_trans, hp.monodromy_trans_apply]

/-- A relative homotopy of a tailed core with the marked pair word gives
an equality in the fundamental groupoid. The relative homotopy is an input. -/
theorem core_transport_square {b c : X} (tail : Path b c) (core : Path c c)
    (γ₀ γPlus : Path b b)
    (h : ((tail.trans core).trans tail.symm).Homotopic (γ₀.trans γPlus)) :
    (Path.Homotopic.Quotient.mk tail).trans (Path.Homotopic.Quotient.mk core) =
      ((Path.Homotopic.Quotient.mk γ₀).trans (Path.Homotopic.Quotient.mk γPlus)).trans (Path.Homotopic.Quotient.mk tail) := by
  have hq : ((Path.Homotopic.Quotient.mk tail).trans (Path.Homotopic.Quotient.mk core)).trans
      (Path.Homotopic.Quotient.mk tail).symm = (Path.Homotopic.Quotient.mk γ₀).trans (Path.Homotopic.Quotient.mk γPlus) := by
    simpa only [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_symm] using Path.Homotopic.Quotient.eq.mpr h
  have ht := congrArg (fun q => q.trans (Path.Homotopic.Quotient.mk tail)) hq
  simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl] using ht

/-- Conditional first-annulus transport: lift the tail, then the core, or
execute the two marked loops and then lift the tail; the endpoints agree. -/
theorem monodromy_core_of_tailed_homotopy (hp : IsCoveringMap p) {b c : X}
    (tail : Path b c) (core : Path c c) (γ₀ γPlus : Path b b)
    (h : ((tail.trans core).trans tail.symm).Homotopic (γ₀.trans γPlus))
    (e : p ⁻¹' {b}) :
    hp.monodromy (.mk core) (hp.monodromy (.mk tail) e) =
      hp.monodromy (.mk tail)
        (hp.monodromy (.mk γPlus) (hp.monodromy (.mk γ₀) e)) := by
  have ht := congrArg (fun q => hp.monodromy q e)
    (core_transport_square tail core γ₀ γPlus h)
  simpa only [hp.monodromy_trans_apply] using ht

/-- A homotopy in the source punctured domain can be transported through
any continuous competitor map before applying the covering transport formula. -/
theorem monodromy_mapped_core_of_tailed_homotopy (hp : IsCoveringMap p)
    {Y : Type*} [TopologicalSpace Y] (f : C(Y, X)) {b c : Y}
    (tail : Path b c) (core : Path c c) (γ₀ γPlus : Path b b)
    (h : ((tail.trans core).trans tail.symm).Homotopic (γ₀.trans γPlus))
    (e : p ⁻¹' {f b}) :
    hp.monodromy (.mk (core.map f.continuous))
        (hp.monodromy (.mk (tail.map f.continuous)) e) =
      hp.monodromy (.mk (tail.map f.continuous))
        (hp.monodromy (.mk (γPlus.map f.continuous))
          (hp.monodromy (.mk (γ₀.map f.continuous)) e)) := by
  apply monodromy_core_of_tailed_homotopy hp
  simpa only [Path.map_trans, ← Path.map_symm] using h.map f



/-- A homotopy of maps conjugates images of every loop by the trajectory
of its basepoint. In particular this applies to a free homotopy of circle maps. -/
theorem free_homotopy_conjugacy {Y : Type*} [TopologicalSpace Y]
    {f g : C(Y, X)} (H : f.Homotopy g) {a : Y} (loop : Path a a) :
    ((Path.Homotopic.Quotient.mk (H.evalAt a)).trans
      (Path.Homotopic.Quotient.mk (loop.map g.continuous))).trans
      (Path.Homotopic.Quotient.mk (H.evalAt a)).symm =
      Path.Homotopic.Quotient.mk (loop.map f.continuous) := by
  have hq := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H loop)
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans] at hq
  have ht := congrArg (fun q => q.trans (Path.Homotopic.Quotient.mk (H.evalAt a)).symm) hq
  simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] using ht.symm

section DeckOrder
variable {G : Type*} [Group G] [MulAction G E]

/-- Although transport acts by composition in execution order, its deck labels
at a fixed initial lift multiply left-to-right, because deck action commutes
with transport. No matrix or modular covering is asserted here. -/
theorem deck_labels_trans (hp : IsQuotientCoveringMap p G) {b : X}
    (γ δ : Path b b) (e : p ⁻¹' {b}) (g h : G)
    (hγ : hp.isCoveringMap.monodromy (.mk γ) e = hp.toPermFiber b g e)
    (hδ : hp.isCoveringMap.monodromy (.mk δ) e = hp.toPermFiber b h e) :
    hp.isCoveringMap.monodromy (.mk (γ.trans δ)) e = hp.toPermFiber b (g * h) e := by
  rw [transport_trans hp.isCoveringMap, hγ, hp.monodromy_toPermFiber, hδ]
  rw [map_mul]
  rfl



/-- The first-annulus core has the pair-word deck label at the lift obtained
by transporting the original lift along the tail. All geometric and label
identification hypotheses remain explicit. -/
theorem first_annulus_core_deck_label (hp : IsQuotientCoveringMap p G) {b c : X}
    (tail : Path b c) (core : Path c c) (γ₀ γPlus : Path b b)
    (hcore : ((tail.trans core).trans tail.symm).Homotopic (γ₀.trans γPlus))
    (e : p ⁻¹' {b}) (g h : G)
    (hγ₀ : hp.isCoveringMap.monodromy (.mk γ₀) e = hp.toPermFiber b g e)
    (hγPlus : hp.isCoveringMap.monodromy (.mk γPlus) e = hp.toPermFiber b h e) :
    hp.isCoveringMap.monodromy (.mk core) (hp.isCoveringMap.monodromy (.mk tail) e) =
      hp.toPermFiber c (g * h) (hp.isCoveringMap.monodromy (.mk tail) e) := by
  rw [monodromy_core_of_tailed_homotopy hp.isCoveringMap tail core γ₀ γPlus hcore]
  rw [← transport_trans hp.isCoveringMap γ₀ γPlus e,
    deck_labels_trans hp γ₀ γPlus e g h hγ₀ hγPlus, hp.monodromy_toPermFiber]

/-- Changing the chosen initial lift by a left deck transformation conjugates
its loop label. This separates fiber transport from the matrix convention. -/
theorem deck_label_change_initial_lift (hp : IsQuotientCoveringMap p G) {b : X}
    (γ : Path b b) (e : p ⁻¹' {b}) (g k : G)
    (hγ : hp.isCoveringMap.monodromy (.mk γ) e = hp.toPermFiber b g e) :
    hp.isCoveringMap.monodromy (.mk γ) (hp.toPermFiber b k e) =
      hp.toPermFiber b (k * g * k⁻¹) (hp.toPermFiber b k e) := by
  rw [hp.monodromy_toPermFiber, hγ]
  have hprod : (k * g * k⁻¹) * k = k * g := by simp [mul_assoc]
  calc
    hp.toPermFiber b k (hp.toPermFiber b g e) = hp.toPermFiber b (k * g) e := by
      rw [map_mul]; rfl
    _ = hp.toPermFiber b ((k * g * k⁻¹) * k) e :=
      congrArg (fun u => hp.toPermFiber b u e) hprod.symm
    _ = hp.toPermFiber b (k * g * k⁻¹) (hp.toPermFiber b k e) := by
      rw [map_mul]; rfl

end DeckOrder

/-- A free homotopy supplies the relative homotopy of a tailed loop,
with the basepoint trajectory as the tail. -/
theorem free_homotopy_tailed_homotopy {Y : Type*} [TopologicalSpace Y]
    {f g : C(Y, X)} (H : f.Homotopy g) {a : Y} (loop : Path a a) :
    (((H.evalAt a).trans (loop.map g.continuous)).trans
      (H.evalAt a).symm).Homotopic (loop.map f.continuous) := by
  apply Path.Homotopic.Quotient.eq.mp
  simpa only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
    using free_homotopy_conjugacy H loop

/-- Covering transport is natural under a free homotopy of loop maps. -/
theorem monodromy_free_homotopy (hp : IsCoveringMap p)
    {Y : Type*} [TopologicalSpace Y] {f g : C(Y, X)}
    (H : f.Homotopy g) {a : Y} (loop : Path a a) (e : p ⁻¹' {f a}) :
    hp.monodromy (.mk (loop.map g.continuous))
        (hp.monodromy (.mk (H.evalAt a)) e) =
      hp.monodromy (.mk (H.evalAt a))
        (hp.monodromy (.mk (loop.map f.continuous)) e) := by
  have hq := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H loop)
  have ht := congrArg (fun q => hp.monodromy q e) hq
  simpa only [transport_trans] using ht.symm

end BelgianChocolate.FirstAnnulusTransport

