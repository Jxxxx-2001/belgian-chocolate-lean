import FirstAnnulusReferenceGates
namespace BelgianChocolate.FirstAnnulus
open Complex Metric Set unitInterval
open BelgianChocolate.FirstAnnulusPaths

private theorem link_of_real_gate {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {a b : cutDomain t} {x y : ℝ} (ha : (a:ℂ)=(x:ℂ)) (hb : (b:ℂ)=(y:ℂ))
    (hbox : uIcc x y ⊆ Icc (-5/4:ℝ) (1/4))
    (hne : ∀ z ∈ uIcc x y, z ≠ 0 ∧ z ≠ -1) :
    ∃ p : Path a b, ∀ u, (p u : ℂ).im = 0 := by
  have hia : (a:ℂ).im=0 := by rw [ha]; rfl
  have hib : (b:ℂ).im=0 := by rw [hb]; rfl
  have hr : (a:ℂ).re = x := by rw [ha]; rfl
  have hr' : (b:ℂ).re = y := by rw [hb]; rfl
  have b₁ : uIcc (a:ℂ).re (b:ℂ).re ⊆ Icc (-5/4:ℝ) (1/4) := by rwa [hr,hr']
  have b₂ : ∀ z ∈ uIcc (a:ℂ).re (b:ℂ).re, z ≠ 0 ∧ z ≠ -1 := by rwa [hr,hr']
  exact ⟨realLink ht ht' hia hib b₁ b₂, realLink_im ht ht' hia hib b₁ b₂⟩

/-- Turn the two actual outer real crossings into the fixed reference gates
by paths on the real intervals. -/
theorem outerGateLinks {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    (∃ r : Path (referenceLoop ht ht' 0) (round ht ht' (p:=0) (Or.inl rfl) quarter),
      ∀ u, (r u : ℂ).im = 0) ∧
    (∃ l : Path (round ht ht' (p:=-1) (Or.inr rfl) threeQuarters)
      (referenceLoop ht ht' halfTurn), ∀ u, (l u : ℂ).im = 0) := by
  have hg := referenceLoop_gate_values ht ht'
  constructor
  · apply link_of_real_gate ht ht' (x:=1/4) (y:=1/5)
    · simpa using hg.1
    · rw [round_quarter]; norm_num
    · rw [uIcc_of_ge (by norm_num)]
      exact Icc_subset_Icc (by norm_num) (by norm_num)
    · intro z hz
      rw [uIcc_of_ge (by norm_num)] at hz
      exact ⟨by linarith [hz.1],by linarith [hz.1]⟩
  · apply link_of_real_gate ht ht' (x:=-6/5) (y:=-5/4)
    · rw [round_threeQuarters]; norm_num
    · simpa using hg.2.1
    · rw [uIcc_of_ge (by norm_num)]
      exact Icc_subset_Icc (by norm_num) (by norm_num)
    · intro z hz
      rw [uIcc_of_ge (by norm_num)] at hz
      exact ⟨by linarith [hz.2],by linarith [hz.2]⟩

theorem outerGate_reference_class {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    ∃ (r : Path (referenceLoop ht ht' 0) (round ht ht' (p:=0) (Or.inl rfl) quarter))
      (l : Path (round ht ht' (p:=-1) (Or.inr rfl) threeQuarters) (referenceLoop ht ht' halfTurn)),
    let A := rightApproach ht ht' (p:=0) (Or.inl rfl)
    let B := leftApproach ht ht' (p:=-1) (Or.inr rfl)
    let γ := referenceLoop ht ht'
    let e : γ 1 = γ 0 := γ.target.trans γ.source.symm
    (((r.trans (upperBridge ht ht')).trans l).trans
      (((l.symm.trans B.symm).trans A).trans (r.symm.cast rfl e))).Homotopic
      (γ.cast γ.source γ.target) := by
  obtain ⟨⟨r,hr⟩,⟨l,hl⟩⟩ := outerGateLinks ht ht'
  refine ⟨r,l,?_⟩
  dsimp only
  apply reference_class_of_weak_half_paths
  · intro u _ _
    apply path_trans_property (P := fun z : cutDomain t ↦ 0 ≤ (z:ℂ).im) _ (fun v ↦ (hl v).ge)
    exact path_trans_property (P := fun z : cutDomain t ↦ 0 ≤ (z:ℂ).im)
      (fun v ↦ (hr v).ge) (upperBridge_im_nonneg ht ht')
  · intro u _ _
    let A := rightApproach ht ht' (p:=0) (Or.inl rfl)
    let B := leftApproach ht ht' (p:=-1) (Or.inr rfl)
    let P : cutDomain t → Prop := fun z ↦ (z:ℂ).im ≤ 0
    have hl' : ∀ v, P (l.symm v) := fun v ↦ (hl (unitInterval.symm v)).le
    have hB : ∀ v, P (B.symm v) := fun v ↦
      leftApproach_im_nonpos ht ht' (Or.inr (rfl : (-1:ℂ) = -1)) (unitInterval.symm v)
    have hA : ∀ v, P (A v) := rightApproach_im_nonpos ht ht' (Or.inl (rfl : (0:ℂ) = 0))
    let γ := referenceLoop ht ht'
    let e : γ 1 = γ 0 := γ.target.trans γ.source.symm
    have hr' : ∀ v, P ((r.symm.cast rfl e) v) := fun v ↦ (hr (unitInterval.symm v)).le
    exact path_trans_property (P := P) (p := (l.symm.trans B.symm).trans A) (q := r.symm.cast rfl e)
      (path_trans_property (P := P) (p := l.symm.trans B.symm) (q := A)
        (path_trans_property (P := P) (p := l.symm) (q := B.symm) hl' hB) hA) hr' u

end BelgianChocolate.FirstAnnulus
