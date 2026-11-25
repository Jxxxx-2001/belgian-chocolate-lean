import FirstAnnulusOuterAlgebra

/-! The source-domain homotopy for the actual positive core of the first annulus. -/

namespace BelgianChocolate.FirstAnnulus

open BelgianChocolate.FirstAnnulusPaths

theorem cast_tailed_loop {X : Type*} [TopologicalSpace X] {b c d : X}
    (q : Path b d) (loop : Path c c) (e : d = c) :
    let q' := q.cast rfl e.symm
    ((q'.trans loop).trans q'.symm) =
      ((q.trans (loop.cast e e)).trans q.symm) := by
  subst d
  rfl

open Path.Homotopic.Quotient in
/-- With the specified tails and orientations, the actual positive core has
the marked pair-word class after transport to the marked basepoint. -/
theorem firstAnnulus_core_pairWord {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    let core := positiveCircleLoop.map (coreCircle t ht ht').continuous
    ∃ tail : Path (basepoint ht) (core 0),
      ((tail.trans (core.cast core.source core.source)).trans tail.symm).Homotopic
        (pairWord ht ht') := by
  let H := coreToReferenceHomotopy t ht ht'
  let core := positiveCircleLoop.map (coreCircle t ht ht').continuous
  let ref := referenceLoop ht ht'
  obtain ⟨q, hq⟩ := pairWord_reference ht ht'
  let r := H.evalAt 1
  let q' := q.cast rfl ref.source.symm
  have hq' : (pairWord ht ht').Homotopic ((q'.trans ref).trans q'.symm) := by
    rw [cast_tailed_loop q ref ref.source]
    exact hq
  have hr : ((r.trans ref).trans r.symm).Homotopic core :=
    core_reference_tailed ht ht'
  refine ⟨(q'.trans r.symm).cast rfl core.source, ?_⟩
  rw [← cast_tailed_loop ((q'.trans r.symm).cast rfl core.source) core core.source]
  have htail : ((q'.trans r.symm).cast rfl core.source).cast rfl core.source.symm =
      q'.trans r.symm := by ext u; rfl
  rw [htail]
  apply Path.Homotopic.Quotient.eq.mp
  rw [Path.Homotopic.Quotient.eq.mpr hq']
  have hsym : mk (q'.trans r.symm).symm = (mk r).trans (mk q').symm := by
    rw [Path.trans_symm, Path.symm_symm, mk_trans, mk_symm]
  simp only [mk_trans, hsym, mk_symm]
  have hrq := Path.Homotopic.Quotient.eq.mpr hr
  simp only [mk_trans, mk_symm] at hrq
  rw [← hrq]
  have cancel {a b c : cutDomain t}
      (f : Path.Homotopic.Quotient a b) (g : Path.Homotopic.Quotient b c) :
      f.symm.trans (f.trans g) = g := by
    rw [← trans_assoc, symm_trans, refl_trans]
  simp only [trans_assoc, cancel]

open Set in
/-- A continuous competitor sends the concrete source homotopy to the
corresponding equality of lifted endpoints for any covering. -/
theorem firstAnnulus_monodromy_core_pairWord
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {p : E → X} (hp : IsCoveringMap p) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    (f : C(cutDomain t, X)) (e : p ⁻¹' {f (basepoint ht)}) :
    let core := positiveCircleLoop.map (coreCircle t ht ht').continuous
    ∃ tail : Path (basepoint ht) (core 0),
      hp.monodromy (.mk ((core.cast core.source core.source).map f.continuous))
          (hp.monodromy (.mk (tail.map f.continuous)) e) =
        hp.monodromy (.mk (tail.map f.continuous))
          (hp.monodromy (.mk ((gammaPlus ht ht').map f.continuous))
            (hp.monodromy (.mk ((gammaZero ht ht').map f.continuous)) e)) := by
  obtain ⟨tail, htail⟩ := firstAnnulus_core_pairWord ht ht'
  refine ⟨tail, ?_⟩
  exact FirstAnnulusTransport.monodromy_mapped_core_of_tailed_homotopy
    hp f tail _ (gammaZero ht ht') (gammaPlus ht ht') htail e


end BelgianChocolate.FirstAnnulus
