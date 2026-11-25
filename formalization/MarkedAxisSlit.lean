import SourceDiskCompetitor
import UpperHalfDiskPuncture

/-! Enlarging the upper half disk across the open real intervals keeps the
positive marked circle as the only peripheral generator. -/

namespace BelgianChocolate.MarkedAxisSlit
open Complex Metric Set Topology unitInterval
open BelgianChocolate.SourceDiskPaths

/-- The unit disk cut along its downward imaginary radius. -/
def slit : Set ℂ := {z | ‖z‖ < 1 ∧ (z.re ≠ 0 ∨ 0 < z.im)}

abbrev Domain (t : ℝ) := ↥(slit \ {UpperHalfDisk.puncture t})

theorem isOpen_slit : IsOpen slit := by
  change IsOpen ({z : ℂ | ‖z‖ < 1} ∩ ({z : ℂ | z.re ≠ 0} ∪ {z : ℂ | 0 < z.im}))
  exact (isOpen_lt continuous_norm continuous_const).inter
    ((isOpen_ne_fun continuous_re continuous_const).union (isOpen_lt continuous_const continuous_im))

instance (t : ℝ) : LocallyPathConnectedSpace (Domain t) :=
  (isOpen_slit.sdiff isClosed_singleton).locallyPathConnectedSpace

theorem slit_star {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    StarConvex ℝ (UpperHalfDisk.puncture t) slit := by
  intro z hz a b ha hb hab
  have hP := UpperHalfDisk.puncture_mem ht ht1
  have hn : a • UpperHalfDisk.puncture t + b • z ∈ ball (0:ℂ) 1 :=
    (convex_ball (0:ℂ) 1) (mem_ball_zero_iff.mpr hP.1) (mem_ball_zero_iff.mpr hz.1) ha hb hab
  refine ⟨mem_ball_zero_iff.mp hn,?_⟩
  by_cases hb₀ : b = 0
  · subst b
    have ha₁ : a=1 := by linarith
    simpa [ha₁] using Or.inr hP.2
  have hr : (a • UpperHalfDisk.puncture t + b • z).re = b*z.re := by
    simp [UpperHalfDisk.puncture,Complex.real_smul,Complex.mul_re,Complex.mul_im]
  have hi : (a • UpperHalfDisk.puncture t + b • z).im = a*t+b*z.im := by
    simp [UpperHalfDisk.puncture,Complex.real_smul,Complex.mul_re,Complex.mul_im]
  rcases hz.2 with hx|hx
  · exact Or.inl (hr.trans_ne (mul_ne_zero hb₀ hx))
  · exact Or.inr (hi.symm ▸ add_pos_of_nonneg_of_pos (mul_nonneg ha ht.le) (mul_pos (lt_of_le_of_ne hb (Ne.symm hb₀)) hx))

theorem upper_subset_slit : UpperHalfDisk.domain ⊆ slit := fun _ hz ↦ ⟨hz.1,Or.inr hz.2⟩

theorem slit_subset_source {t : ℝ} (ht : 0 < t) :
    slit \ {UpperHalfDisk.puncture t} ⊆ sourceDisk t := by
  rintro z ⟨hz,hp⟩
  refine ⟨hz.1,?_,hp,?_⟩
  · rintro rfl
    rcases hz.2 with h|h <;> simp at h
  · rintro rfl
    rcases hz.2 with h|h <;> simp at h
    linarith

noncomputable def inclusion {t : ℝ} (ht : 0 < t) : C(Domain t,sourceDisk t) :=
  ⟨fun z ↦ ⟨z,slit_subset_source ht z.property⟩,Continuous.subtype_mk continuous_subtype_val _⟩

theorem mem_of_im_nonneg {t : ℝ} (z : sourceDisk t) (h : 0 ≤ (z:ℂ).im) :
    (z:ℂ) ∈ slit \ {UpperHalfDisk.puncture t} := by
  refine ⟨⟨z.property.1,?_⟩,z.property.2.2.1⟩
  by_cases hr : (z:ℂ).re=0
  · right
    apply lt_of_le_of_ne h
    intro he
    exact z.property.2.1 (Complex.ext (by simpa using hr) (by simpa using he.symm))
  · exact Or.inl hr

theorem sphere_subset {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    sphere (UpperHalfDisk.puncture t) (t/5) ⊆ slit := by
  intro z hz
  have hn : ‖z-UpperHalfDisk.puncture t‖=t/5 := by simpa only [mem_sphere,dist_eq_norm] using hz
  have hp : ‖UpperHalfDisk.puncture t‖=t := by simp [UpperHalfDisk.puncture,abs_of_pos ht]
  have hb := norm_add_le (z-UpperHalfDisk.puncture t) (UpperHalfDisk.puncture t)
  rw [sub_add_cancel,hn,hp] at hb
  have hi := (z-UpperHalfDisk.puncture t).abs_im_le_norm
  have him : (UpperHalfDisk.puncture t).im=t := by simp [UpperHalfDisk.puncture]
  rw [hn,Complex.sub_im,him] at hi
  exact ⟨by linarith,Or.inr (by linarith [(abs_le.mp hi).1])⟩

noncomputable def basepoint {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) : Domain t :=
  ⟨sourceBasepoint ht ht', mem_of_im_nonneg _ (by rw [sourceBasepoint_coe]; norm_num)⟩

/-- A physical path in the closed upper half disk is also a path in the
open slit disk, including points on the real intervals. -/
noncomputable def restrictPath {t : ℝ} {a b : sourceDisk t} (p : Path a b)
    (h : ∀ u, (p u:ℂ) ∈ slit \ {UpperHalfDisk.puncture t})
    {a' b' : Domain t} (ha : (a':ℂ)=(a:ℂ)) (hb : (b':ℂ)=(b:ℂ)) : Path a' b' where
  toFun u := ⟨p u,h u⟩
  continuous_toFun := (continuous_subtype_val.comp p.continuous).subtype_mk _
  source' := by apply Subtype.ext; simpa using ha.symm
  target' := by apply Subtype.ext; simpa using hb.symm

theorem plus_paths {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    ∃ (c : Domain t) (T : Path (basepoint ht ht') c) (R : Path c c),
      (∀ u, (R u:ℂ)=circleMap (UpperHalfDisk.puncture t) (t/5) (Real.pi+2*Real.pi*(u:ℝ))) ∧
      (((T.trans R).trans T.symm).map (inclusion ht).continuous) = sourceGammaPlus ht ht' := by
  obtain ⟨c,T,R,hT,hR,hword⟩ := sourceGammaPlus_directed ht ht'
  have hTail (u : I) : 0 ≤ (T u:ℂ).im := by
    rw [hT,AffineMap.lineMap_apply_module]
    simp [Complex.real_smul,Complex.mul_im,Complex.sub_im]
    exact mul_nonneg u.2.1 ht.le
  have hRound (u : I) : (R u:ℂ) ∈ slit \ {UpperHalfDisk.puncture t} :=
    ⟨sphere_subset ht ht' (hR u ▸ circleMap_mem_sphere _ (by positivity) _),
      (R u).property.2.2.1⟩
  let c' : Domain t := ⟨c,by simpa using hRound 0⟩
  let T' : Path (basepoint ht ht') c' := restrictPath T (fun u ↦ mem_of_im_nonneg _ (hTail u)) rfl rfl
  let R' : Path c' c' := restrictPath R hRound rfl rfl
  refine ⟨c',T',R',hR,?_⟩
  have hT' : T'.map (inclusion ht).continuous = T := by apply Path.ext; rfl
  have hR' : R'.map (inclusion ht).continuous = R := by apply Path.ext; rfl
  rw [Path.map_trans,Path.map_trans,← Path.map_symm,hT',hR']
  exact hword.symm

end BelgianChocolate.MarkedAxisSlit

