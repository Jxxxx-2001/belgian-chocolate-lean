import Mathlib.Topology.Covering.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Ordinary boundary values of a covering projection cannot cause a
continuous lift to escape its evenly covered sheet on a connected cap. -/

open Filter Metric Set Topology
open scoped Topology

namespace IsCoveringMap

variable {A E X : Type*} [PseudoMetricSpace A] [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X} {S : Set A}

/-- If the base map has a limit and the source has arbitrarily small preconnected
caps at the boundary point, the lift converges to a point over the base limit. -/
theorem exists_tendsto_at_boundary_of_preconnected_caps
    (hp : IsCoveringMap p) (F : C(S, E)) {a : A} (ha : a ∈ closure S)
    (hcap : ∀ R > 0, ∃ r ∈ Ioo 0 R, IsPreconnected (S ∩ ball a r)) {x : X}
    (hf : Tendsto (p ∘ F) (comap (Subtype.val : S → A) (𝓝 a)) (𝓝 x)) :
    ∃ e : E, p e = x ∧ Tendsto F (comap (Subtype.val : S → A) (𝓝 a)) (𝓝 e) := by
  classical
  obtain ⟨hdisc, U, hxU, hU, _, H, hH⟩ := hp x
  let _ := hdisc
  let L := comap (Subtype.val : S → A) (𝓝 a)
  have hw : {z : S | p (F z) ∈ U} ∈ L := hf (hU.mem_nhds hxU)
  obtain ⟨W, hW, hsub⟩ := Filter.mem_comap.mp hw
  obtain ⟨R, hR, hRW⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨r, hr, hpre⟩ := hcap R hR
  let K := S ∩ ball a r
  have hOK (z : K) : p (F ⟨z, z.2.1⟩) ∈ U := by
    apply hsub
    exact hRW (ball_subset_ball hr.2.le z.2.2)
  let incl : C(K, S) := ⟨fun z => ⟨z, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩
  let FK : C(K, p ⁻¹' U) := ⟨fun z => ⟨F (incl z), hOK z⟩,
    (F.continuous.comp incl.continuous).subtype_mk _⟩
  obtain ⟨a₀, ha₀, hdist⟩ := Metric.mem_closure_iff.mp ha r hr.1
  let k₀ : K := ⟨a₀, ha₀, by simpa only [mem_ball, dist_comm] using hdist⟩
  let idx := (H (FK k₀)).2
  have hsheet (k : K) : (H (FK k)).2 = idx :=
    PreconnectedSpace.constant (isPreconnected_iff_preconnectedSpace.mp hpre)
      (continuous_snd.comp (H.continuous.comp FK.continuous)) (x := k) (y := k₀)
  let xU : U := ⟨x, hxU⟩
  let g (z : S) : U := if h : p (F z) ∈ U then ⟨p (F z), h⟩ else xU
  have hgEq : (Subtype.val ∘ g) =ᶠ[L] p ∘ F := by
    filter_upwards [hw] with z hz
    simp only [Function.comp_apply, g, dite_eq_left hz]
  have hg : Tendsto g L (𝓝 xU) :=
    IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr (hf.congr' hgEq.symm)
  let e : E := (H.symm (xU, idx) : E)
  refine ⟨e, ?_, ?_⟩
  · have h := hH (H.symm (xU, idx))
    simpa only [H.apply_symm_apply] using h.symm
  · have hlim : Tendsto (fun z => (H.symm (g z, idx) : E)) L (𝓝 e) :=
      (continuous_subtype_val.comp H.symm.continuous).continuousAt.tendsto.comp
        (hg.prodMk_nhds tendsto_const_nhds)
    apply hlim.congr'
    have hsmall : {z : S | (z : A) ∈ ball a r} ∈ L :=
      Filter.mem_comap.mpr ⟨ball a r, ball_mem_nhds a hr.1, Subset.rfl⟩
    filter_upwards [hsmall] with z hz
    let k : K := ⟨z, z.2, hz⟩
    have hK : FK k = H.symm (g z, idx) := by
      apply H.injective
      rw [H.apply_symm_apply]
      apply Prod.ext
      · apply Subtype.ext
        have hkz : incl k = z := Subtype.ext rfl
        have hFK : (FK k : E) = F z := congrArg F hkz
        have hFz := Set.mem_preimage.mp (FK k).property
        rw [hFK] at hFz
        rw [hH (FK k), hFK]
        simp only [g, dite_eq_left hFz]
      · exact hsheet k
    exact congrArg Subtype.val hK.symm

/-- Convex subsets of a normed real space have preconnected metric caps. -/
theorem exists_tendsto_at_boundary_of_convex
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {T : Set B}
    (hp : IsCoveringMap p) (F : C(T, E)) (hT : Convex ℝ T) {a : B} (ha : a ∈ closure T)
    {x : X} (hf : Tendsto (p ∘ F) (comap (Subtype.val : T → B) (𝓝 a)) (𝓝 x)) :
    ∃ e : E, p e = x ∧ Tendsto F (comap (Subtype.val : T → B) (𝓝 a)) (𝓝 e) :=
  hp.exists_tendsto_at_boundary_of_preconnected_caps F ha
    (fun R hR => ⟨R / 2, ⟨half_pos hR, half_lt_self hR⟩,
      (hT.inter (convex_ball _ _)).isPreconnected⟩) hf

#print axioms exists_tendsto_at_boundary_of_preconnected_caps
#print axioms exists_tendsto_at_boundary_of_convex

end IsCoveringMap


