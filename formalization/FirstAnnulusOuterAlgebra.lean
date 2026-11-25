import FirstAnnulusOuterGates
namespace BelgianChocolate.FirstAnnulus
open Complex Metric Set unitInterval
open BelgianChocolate.FirstAnnulusPaths

open Path.Homotopic.Quotient in
private theorem outer_algebra {X : Type*} [TopologicalSpace X] {o R R' r l L : X}
    (e : R' = R) (Q : Path R R') (A : Path o r) (U : Path r l) (B : Path o l)
    (i : Path R r) (j : Path l L)
    (h : (((i.trans U).trans j).trans (((j.symm.trans B.symm).trans A).trans (i.symm.cast rfl e))).Homotopic Q) :
    ((A.trans U).trans B.symm).Homotopic
      ((((A.trans i.symm).trans (Q.cast rfl e.symm)).trans (A.trans i.symm).symm)) := by
  subst R'
  have hcat := Path.Homotopic.Quotient.eq.mpr h
  change mk (((i.trans U).trans j).trans (((j.symm.trans B.symm).trans A).trans i.symm)) = mk Q at hcat
  apply Path.Homotopic.Quotient.eq.mp
  have c₁ {x y z : X} (f : Path.Homotopic.Quotient x y) (g : Path.Homotopic.Quotient y z) :
      f.symm.trans (f.trans g) = g := by rw [← trans_assoc, symm_trans, refl_trans]
  have c₂ {x y z : X} (f : Path.Homotopic.Quotient x y) (g : Path.Homotopic.Quotient x z) :
      f.trans (f.symm.trans g) = g := by rw [← trans_assoc, trans_symm, refl_trans]
  change mk ((A.trans U).trans B.symm) = mk (((A.trans i.symm).trans Q).trans (A.trans i.symm).symm)
  simp only [Path.trans_symm, Path.symm_symm, mk_trans, mk_symm, ← hcat, trans_assoc, c₁, c₂,
    trans_symm, trans_refl]

theorem pairWord_reference {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    :
    let γ := referenceLoop ht ht'
    ∃ tail : Path (basepoint ht) (γ 0), (pairWord ht ht').Homotopic
      ((tail.trans (γ.cast γ.source γ.source)).trans tail.symm) := by
  let γ := referenceLoop ht ht'
  obtain ⟨r,l,h⟩ := outerGate_reference_class ht ht'
  let A := rightApproach ht ht' (p:=0) (Or.inl rfl)
  let B := leftApproach ht ht' (p:=-1) (Or.inr rfl)
  let e : γ 1 = γ 0 := γ.target.trans γ.source.symm
  refine ⟨A.trans r.symm, (pairWord_homotopic_upperBridge ht ht').trans ?_⟩
  exact outer_algebra e (γ.cast γ.source γ.target) A (upperBridge ht ht') B r l h

end BelgianChocolate.FirstAnnulus
