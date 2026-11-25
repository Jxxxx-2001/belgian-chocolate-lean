import SecondAnnulusReference

/-! The positive three-peripheral word in the full scaled disk. -/
namespace BelgianChocolate.SecondAnnulusTopology
open Complex Metric Set unitInterval
open BelgianChocolate.SourceDiskPaths
open BelgianChocolate.FirstAnnulusHomotopySupport

private noncomputable def gapValue (k u : ℝ) : ℂ := ⟨4/5 - (3/5)*u, -k*u*(1-u)⟩

private theorem gap_mem {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (k u : I) :
    gapValue k u ∈ scaledDisk t := by
  have hx : 0 < (gapValue k u).re ∧ (gapValue k u).re < 1 := by
    change 0 < 4/5 - 3/5*(u:ℝ) ∧ 4/5 - 3/5*(u:ℝ) < 1
    constructor <;> linarith [u.property.1,u.property.2]
  have hm : 0 ≤ (k:ℝ)*(u:ℝ)*(1-(u:ℝ)) := by
    exact mul_nonneg (mul_nonneg k.property.1 u.property.1) (sub_nonneg.mpr u.property.2)
  have hm' : (k:ℝ)*(u:ℝ)*(1-(u:ℝ)) ≤ 1 :=
    calc
      _ ≤ (1:ℝ)*1*(1-(u:ℝ)) := by
        gcongr <;> first | exact k.property.2 | exact u.property.2 | exact u.property.1 | exact sub_nonneg.mpr u.property.2
      _ ≤ 1 := by linarith [u.property.1]
  have hi : |(gapValue k u).im| ≤ 1 := by
    change |-(k:ℝ)*(u:ℝ)*(1-(u:ℝ))| ≤ 1
    rw [neg_mul, neg_mul, abs_neg, abs_of_nonneg hm]; exact hm'
  have hR : 10 ≤ 1/t := (le_div_iff₀ ht).mpr (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hb := Complex.norm_le_abs_re_add_abs_im (gapValue k u)
    rw [abs_of_pos hx.1] at hb
    linarith
  all_goals intro he; rw [he] at hx; norm_num at hx

private noncomputable def gapPath {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {a b : scaledDisk t} (ha : (a:ℂ)=4/5) (hb : (b:ℂ)=1/5) (k : I) : Path a b where
  toFun u := ⟨gapValue k u, gap_mem ht ht' k u⟩
  continuous_toFun := Continuous.subtype_mk (by
    have he (u : I) : gapValue k u = ((4/5-(3/5)*(u:ℝ):ℝ):ℂ) +
        ((-(k:ℝ)*(u:ℝ)*(1-(u:ℝ)):ℝ):ℂ)*Complex.I := by
      apply Complex.ext <;> simp [gapValue]
    simp_rw [he]
    fun_prop) _
  source' := by
    apply Subtype.ext
    change gapValue (k:ℝ) 0 = (a:ℂ)
    rw [ha]
    apply Complex.ext <;> norm_num [gapValue,Complex.div_re,Complex.div_im,Complex.normSq_apply]
  target' := by
    apply Subtype.ext
    change gapValue (k:ℝ) 1 = (b:ℂ)
    rw [hb]
    apply Complex.ext <;> norm_num [gapValue,Complex.div_re,Complex.div_im,Complex.normSq_apply]

/-- Any weakly lower path between the adjacent inner gates is homotopic
relative its endpoints to a real path lying in the gap between zero and one. -/
theorem lower_gap_homotopic_real {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {a b : scaledDisk t} (ha : (a:ℂ)=4/5) (hb : (b:ℂ)=1/5)
    (p : Path a b) (hp : ∀ u, (p u:ℂ).im ≤ 0) :
    ∃ q : Path a b, (∀ u, (q u:ℂ).im = 0) ∧ p.Homotopic q := by
  let q := gapPath ht ht' ha hb 0
  let v := gapPath ht ht' ha hb 1
  have hq : ∀ u, (q u:ℂ).im = 0 := by
    intro u; change -(0:ℝ)*(u:ℝ)*(1-(u:ℝ))=0; ring
  have hv : ∀ u : I, u ≠ 0 → u ≠ 1 → (v u:ℂ).im < 0 := by
    intro u h0 h1
    have hu₀ : 0 < (u:ℝ) := lt_of_le_of_ne u.2.1 (fun he ↦ h0 (Subtype.ext he.symm))
    have hu₁ : (u:ℝ) < 1 := lt_of_le_of_ne u.2.2 (fun he ↦ h1 (Subtype.ext he))
    change -(1:ℝ)*(u:ℝ)*(1-(u:ℝ)) < 0
    nlinarith [mul_pos hu₀ (sub_pos.mpr hu₁)]
  have hweak (c : Path a b) (hc : ∀ u, (c u:ℂ).im ≤ 0) : c.Homotopic v := by
    apply homotopic_of_weak_strict_linear_side (Ω:=scaledDisk t) (convex_ball (0:ℂ) (1/t))
      (fun _ h ↦ mem_ball_zero_iff.mpr h.1) (-imCLM.toLinearMap)
    · intro z hz h; exact mem_scaledDisk_of_im_ne_zero (mem_ball_zero_iff.mp hz) (neg_pos.mp h).ne
    · intro u _ _; exact neg_nonneg.mpr (hc u)
    · intro u h0 h1; exact neg_pos.mpr (hv u h0 h1)
  exact ⟨q,hq,(hweak p hp).trans (hweak q (fun u ↦ (hq u).le)).symm⟩

end BelgianChocolate.SecondAnnulusTopology

namespace BelgianChocolate.SecondAnnulusTopology
open Complex Metric Set unitInterval
open BelgianChocolate.SourceDiskPaths BelgianChocolate.FirstAnnulusPaths

noncomputable def minusRightApproach {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    Path (scaledBasepoint ht ht') (minusRound ht ht' quarter) :=
  (minusTail ht ht').trans (((minusRound ht ht').subpath 0 quarter).cast
    (minusRound ht ht').source.symm rfl)

noncomputable def minusLeftApproach {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    Path (scaledBasepoint ht ht') (minusRound ht ht' threeQuarters) :=
  (minusTail ht ht').trans (((minusRound ht ht').subpath threeQuarters 1).cast
    rfl (minusRound ht ht').target.symm).symm

theorem minusRound_quarter {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    (minusRound ht ht' quarter : ℂ) = 6/5 := by
  change circleMap 1 (1/5) (-(Real.pi / 2) + 2*Real.pi*(1/4)) = _
  rw [show -(Real.pi / 2) + 2 * Real.pi * (1 / 4) = 0 by ring]
  norm_num [circleMap]

theorem minusRound_threeQuarters {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    (minusRound ht ht' threeQuarters : ℂ) = 4/5 := by
  change circleMap 1 (1/5) (-(Real.pi / 2) + 2*Real.pi*(3/4)) = _
  rw [show -(Real.pi / 2) + 2 * Real.pi * (3 / 4) = Real.pi by ring]
  norm_num [circleMap, Complex.exp_pi_mul_I]

private theorem minusRound_im_eq_zeroRound {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (u : I) :
    (minusRound ht ht' u:ℂ).im = (round ht ht' (p:=0) (Or.inl rfl) u:ℂ).im := by
  change (circleMap 1 (1/5) _).im = (circleMap 0 (1/5) _).im
  simp [circleMap]

theorem minusRightApproach_im_nonpos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (u : I) :
    (minusRightApproach ht ht' u:ℂ).im ≤ 0 := by
  apply path_trans_property (P:=fun z : scaledDisk t ↦ (z:ℂ).im ≤ 0)
  · exact fun v ↦ (minus_tail_mem ht ht' v).2.le
  · intro v
    rw [show ((((minusRound ht ht').subpath 0 quarter).cast
        (minusRound ht ht').source.symm rfl v : scaledDisk t):ℂ).im =
      (((round ht ht' (p:=0) (Or.inl rfl)).subpath 0 quarter v:cutDomain t):ℂ).im
      from minusRound_im_eq_zeroRound ht ht' (Icc.convexComb 0 quarter v)]
    exact round_initial_subpath_im_nonpos ht ht' (Or.inl rfl) v

theorem minusLeftApproach_im_nonpos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (u : I) :
    (minusLeftApproach ht ht' u:ℂ).im ≤ 0 := by
  apply path_trans_property (P:=fun z : scaledDisk t ↦ (z:ℂ).im ≤ 0)
  · exact fun v ↦ (minus_tail_mem ht ht' v).2.le
  · intro v
    exact (minusRound_im_eq_zeroRound ht ht' (Icc.convexComb threeQuarters 1 (unitInterval.symm v))).trans_le
      (round_final_subpath_im_nonpos ht ht' (Or.inl rfl) (unitInterval.symm v))

theorem minusUpper_im_nonneg {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) (u : I) :
    0 ≤ (((minusRound ht ht').subpath quarter threeQuarters u:scaledDisk t):ℂ).im := by
  apply le_of_le_of_eq _ (minusRound_im_eq_zeroRound ht ht' (Icc.convexComb quarter threeQuarters u)).symm
  change 0 ≤ (((round ht ht' (p:=0) (Or.inl rfl)).subpath quarter threeQuarters u : cutDomain t):ℂ).im
  rw [round_upper_subpath_im]
  exact mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le u.2.1)
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left u.2.2 Real.pi_pos.le))

open Path.Homotopic.Quotient in
theorem minus_homotopic_approaches {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    (scaledGammaMinus ht ht').Homotopic
      (((minusRightApproach ht ht').trans ((minusRound ht ht').subpath quarter threeQuarters)).trans
        (minusLeftApproach ht ht').symm) := by
  let rou := minusRound ht ht'
  let ini := (rou.subpath 0 quarter).cast rou.source.symm rfl
  let top := rou.subpath quarter threeQuarters
  let fin := (rou.subpath threeQuarters 1).cast rfl rou.target.symm
  have hs := ((Path.Homotopic.subpath_trans_subpath rou 0 quarter threeQuarters).hcomp
    (Path.Homotopic.refl _)).trans (Path.Homotopic.subpath_trans_subpath rou 0 threeQuarters 1)
  have h : ((ini.trans top).trans fin).Homotopic rou := by
    have hsub := hs.pathCast rou.source.symm rou.target.symm
    rw [Path.subpath_zero_one] at hsub
    convert hsub using 1 <;> exact Path.ext (by rfl)
  have h' := ((Path.Homotopic.refl (minusTail ht ht')).hcomp h.symm).hcomp
    (Path.Homotopic.refl (minusTail ht ht').symm)
  apply h'.trans
  apply eq.mp
  simp only [minusRightApproach, minusLeftApproach, Path.trans_symm, Path.symm_symm,
    mk_trans, ← trans_assoc, ini, top, fin, rou]

end BelgianChocolate.SecondAnnulusTopology

namespace BelgianChocolate.SecondAnnulusTopology
open Complex Metric Set unitInterval
open BelgianChocolate.SourceDiskPaths
open BelgianChocolate.FirstAnnulus (positiveCircleLoop halfTurn)
open BelgianChocolate.FirstAnnulusPaths (path_trans_property)

open Path.Homotopic.Quotient in
/-- Regrouping two based peripheral factors replaces their common inner
approach by its representative in the real gap. -/
theorem join_based_bridges {X : Type*} [TopologicalSpace X] {o r l r' l' : X}
    (A : Path o r) (U : Path r l) (B : Path o l)
    (A' : Path o r') (U' : Path r' l') (B' : Path o l') (M : Path l r')
    (hM : (B.symm.trans A').Homotopic M) :
    (((A.trans U).trans B.symm).trans ((A'.trans U').trans B'.symm)).Homotopic
      ((A.trans ((U.trans M).trans U')).trans B'.symm) := by
  apply eq.mp
  have hm := eq.mpr hM
  simp only [mk_trans, mk_symm] at hm
  simp only [mk_trans, mk_symm, ← trans_assoc]
  rw [trans_assoc _ (mk B).symm (mk A'), hm]

open Path.Homotopic.Quotient in
private theorem based_bridge_conjugate {X : Type*} [TopologicalSpace X] {o a b : X}
    (A : Path o a) (U : Path a b) (B : Path o b) (γ : Path a a)
    (h : (U.trans (B.symm.trans A)).Homotopic γ) :
    ((A.trans U).trans B.symm).Homotopic ((A.trans γ).trans A.symm) := by
  apply eq.mp
  have hc := eq.mpr h
  simp only [mk_trans, mk_symm] at hc ⊢
  rw [← hc]
  simp only [← trans_assoc]
  rw [trans_assoc _ (mk A) (mk A).symm, trans_symm, trans_refl]

/-- If the upper bridge and the two lower approaches have the actual outer
gate coordinates, the resulting based word is a conjugate of the reference circle. -/
theorem based_reference_of_bridge {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {o a b : scaledDisk t} (ha : (a:ℂ)=6/5) (hb : (b:ℂ)=-6/5)
    (A : Path o a) (U : Path a b) (B : Path o b)
    (hA : ∀ u, (A u:ℂ).im ≤ 0) (hU : ∀ u, 0 ≤ (U u:ℂ).im)
    (hB : ∀ u, (B u:ℂ).im ≤ 0) :
    ∃ tail : Path o (referenceCircle ht ht' 1), ((A.trans U).trans B.symm).Homotopic
      ((tail.trans (referenceLoop ht ht')).trans tail.symm) := by
  let γ := referenceLoop ht ht'
  have hg := referenceLoop_gate_values ht ht'
  have h₀ : γ 0 = a := Subtype.ext (hg.1.trans ha.symm)
  have hL : γ halfTurn = b := Subtype.ext (hg.2.1.trans hb.symm)
  have hR : a = referenceCircle ht ht' 1 := h₀.symm.trans γ.source
  clear h₀
  subst a
  let V := B.symm.trans A
  have hV (u : I) : (V u:ℂ).im ≤ 0 :=
    path_trans_property (P:=fun z : scaledDisk t ↦ (z:ℂ).im ≤ 0)
      (p:=B.symm) (q:=A) (fun v ↦ hB (unitInterval.symm v)) hA u
  have hc := reference_class_of_weak_half_paths ht ht' (U.cast γ.source hL)
    (V.cast hL γ.target) (fun u _ _ ↦ hU u) (fun u _ _ ↦ hV u)
  have hc' := hc.pathCast γ.source.symm γ.target.symm
  have h : (U.trans V).Homotopic γ := by
    convert hc' using 1 <;> exact Path.ext (by rfl)
  exact ⟨A,based_bridge_conjugate A U B γ h⟩

end BelgianChocolate.SecondAnnulusTopology

namespace BelgianChocolate.SecondAnnulusTopology
open Complex Metric Set unitInterval
open BelgianChocolate.FirstAnnulusPaths BelgianChocolate.SourceDiskPaths

/-- The three *specified* positive peripheral loops in manuscript execution
order give a transported positive turn around the three punctures. -/
theorem scaledTripleWord_reference {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    ∃ tail : Path (scaledBasepoint ht ht') (referenceCircle ht ht' 1),
      (scaledTripleWord ht ht').Homotopic
        ((tail.trans (referenceLoop ht ht')).trans tail.symm) := by
  let inc := cutInclusion t
  let A := minusRightApproach ht ht'
  let B := minusLeftApproach ht ht'
  let U := (minusRound ht ht').subpath quarter threeQuarters
  let A' := (rightApproach ht ht' (p:=0) (Or.inl rfl)).map inc.continuous
  let B' := (leftApproach ht ht' (p:=-1) (Or.inr rfl)).map inc.continuous
  let U' := (upperBridge ht ht').map inc.continuous
  have hA' (u : I) : (A' u:ℂ).im ≤ 0 := rightApproach_im_nonpos ht ht' (p:=0) (Or.inl rfl) u
  have hB' (u : I) : (B' u:ℂ).im ≤ 0 := leftApproach_im_nonpos ht ht' (p:=-1) (Or.inr rfl) u
  have hU' (u : I) : 0 ≤ (U' u:ℂ).im := upperBridge_im_nonneg ht ht' u
  have hmiddle (u : I) : ((B.symm.trans A') u:ℂ).im ≤ 0 :=
    path_trans_property (P:=fun z : scaledDisk t ↦ (z:ℂ).im ≤ 0) (p:=B.symm) (q:=A')
      (fun v ↦ minusLeftApproach_im_nonpos ht ht' (unitInterval.symm v)) hA' u
  have hright : (inc (round ht ht' (p:=0) (Or.inl rfl) quarter):ℂ)=1/5 := by
    change (round ht ht' (p:=0) (Or.inl rfl) quarter:ℂ)=1/5
    rw [round_quarter, zero_add]
  obtain ⟨M,hM,hm⟩ := lower_gap_homotopic_real ht ht'
    (minusRound_threeQuarters ht ht') hright (B.symm.trans A') hmiddle
  let top := (U.trans M).trans U'
  have htop (u : I) : 0 ≤ (top u:ℂ).im :=
    path_trans_property (P:=fun z : scaledDisk t ↦ 0 ≤ (z:ℂ).im) (p:=U.trans M) (q:=U')
      (path_trans_property (P:=fun z : scaledDisk t ↦ 0 ≤ (z:ℂ).im) (p:=U) (q:=M)
        (minusUpper_im_nonneg ht ht') (fun v ↦ (hM v).ge)) hU' u
  have hleft : (inc (round ht ht' (p:=-1) (Or.inr rfl) threeQuarters):ℂ)=-6/5 := by
    change (round ht ht' (p:=-1) (Or.inr rfl) threeQuarters:ℂ)=-6/5
    rw [round_threeQuarters]
    norm_num
  obtain ⟨tail,htail⟩ := based_reference_of_bridge ht ht' (minusRound_quarter ht ht') hleft
    A top B' (minusRightApproach_im_nonpos ht ht') htop hB'
  have hpair : ((scaledGammaZero ht ht').trans (scaledGammaPlus ht ht')).Homotopic
      ((A'.trans U').trans B'.symm) := by
    rw [← scaled_pairWord]
    simpa only [A', U', B', inc, scaledBasepoint, Path.map_trans, ← Path.map_symm] using
      (pairWord_homotopic_upperBridge ht ht').map inc
  have hregroup : (scaledTripleWord ht ht').Homotopic ((scaledGammaMinus ht ht').trans
      ((scaledGammaZero ht ht').trans (scaledGammaPlus ht ht'))) := by
    apply Path.Homotopic.Quotient.eq.mp
    simp only [scaledTripleWord, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]
  exact ⟨tail,hregroup.trans (((minus_homotopic_approaches ht ht').hcomp hpair).trans
    ((join_based_bridges A U B A' U' B' M hm).trans htail))⟩

end BelgianChocolate.SecondAnnulusTopology


