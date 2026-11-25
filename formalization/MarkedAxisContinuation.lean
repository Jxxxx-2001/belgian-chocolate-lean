import SourceDiskRealNormalization
import ModularLambdaDeckReflection
import ModularLambdaCuspMarked
import FirstAnnulusEmbedding

/-! Compute both marked real intervals by lifting one common upper continuation. -/
namespace BelgianChocolate.MarkedAxisTransport
open Complex Set Metric Topology UpperHalfPlane
open scoped MatrixGroups ComplexConjugate
open BelgianChocolate.SourceDiskPaths BelgianChocolate.ModularLambdaRatio
open BelgianChocolate.ModularLambdaReflection

/-- A level-two translation followed by modular reflection fixes exactly one
vertical line. -/
theorem axisReflection_fixed_iff (n : ℤ) (τ : ℍ) :
    deckReflection (cuspPeriod ^ n) τ = τ ↔ τ.re = (n:ℝ) := by
  have h : ((deckReflection (cuspPeriod ^ n) τ:ℍ):ℂ) =
      (((2*(n:ℝ):ℝ):ℂ) - (starRingEnd ℂ) (τ:ℂ)) := by
    change ((cuspPeriod ^ n • (J • τ) : ℍ):ℂ) = _
    rw [cuspPeriod_zpow_smul]
    change (((2*(n:ℝ):ℝ):ℂ) + ((J • τ : ℍ):ℂ)) = _
    rw [UpperHalfPlane.coe_J_smul,sub_eq_add_neg]
  constructor
  · intro he
    rw [he] at h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.conj_re] at hr
    change τ.re = 2*(n:ℝ) - τ.re at hr
    linarith
  · intro hr
    apply UpperHalfPlane.ext
    rw [h]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re]
      change 2*(n:ℝ)-τ.re = τ.re
      linarith
    · simp

/-- Along an arbitrary real-valued target path, the actual lambda lift stays
on its initial integer vertical line. -/
theorem liftPath_re_of_real {a b : ({0,1}ᶜ : Set ℂ)} (α : Path a b)
    (hα : ∀ u, (α u:ℂ).im = 0) (e : lambdaPunctured ⁻¹' {a}) (n : ℤ)
    (he : (e:ℍ).re = (n:ℝ)) (u : unitInterval) :
    (lambdaPunctured_isCoveringMap.liftPath α (e:ℍ) (α.source.trans e.property.symm) u).re =
      (n:ℝ) := by
  let hp := lambdaPunctured_isCoveringMap
  let H := hp.liftPath α (e:ℍ) (α.source.trans e.property.symm)
  let R := deckReflection (cuspPeriod ^ n)
  have hproj : lambdaPunctured ∘ (R ∘ H) = lambdaPunctured ∘ H := by
    funext v
    change lambdaPunctured (deckReflection (cuspPeriod^n) (H v)) = lambdaPunctured (H v)
    rw [lambdaPunctured_deckReflection]
    have hh := congrFun (hp.liftPath_lifts α (e:ℍ) (α.source.trans e.property.symm)) v
    change lambdaPunctured (H v) = α v at hh
    rw [hh]
    apply Subtype.ext
    change (starRingEnd ℂ) (α v:ℂ) = (α v:ℂ)
    apply Complex.ext <;> simp [hα v]
  have hfix : R (H 0) = H 0 := by
    change deckReflection (cuspPeriod^n) (hp.liftPath α (e:ℍ) _ 0) = hp.liftPath α (e:ℍ) _ 0
    rw [hp.liftPath_zero]
    exact (axisReflection_fixed_iff n _).mpr he
  have hRH := hp.eq_of_comp_eq (R.continuous.comp H.continuous) H.continuous hproj 0 hfix
  exact (axisReflection_fixed_iff n _).mp (congrFun hRH u)

theorem real_mem_sourceDisk {t x : ℝ} (ht : 0 < t) (hx : |x| < 1) (h₀ : x ≠ 0) :
    (x:ℂ) ∈ sourceDisk t := by
  refine ⟨by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx, by exact_mod_cast h₀, ?_, ?_⟩
  all_goals intro h; have hi := congrArg Complex.im h; simp at hi; linarith

noncomputable def realIntervalPath {t l r : ℝ} (hI : ∀ x ∈ Ioo l r, (x:ℂ) ∈ sourceDisk t)
    {a b : sourceDisk t} {x y : ℝ} (ha : (a:ℂ)=(x:ℂ)) (hb : (b:ℂ)=(y:ℂ))
    (hx : x ∈ Ioo l r) (hy : y ∈ Ioo l r) : Path a b where
  toFun u := ⟨((AffineMap.lineMap x y (u:ℝ) : ℝ):ℂ),
    hI _ ((convex_Ioo l r).lineMap_mem hx hy u.property)⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  source' := by apply Subtype.ext; simpa using ha.symm
  target' := by apply Subtype.ext; simpa using hb.symm

set_option maxHeartbeats 600000 in
/-- In physical coordinates, transport from the normalized common lift at
−1/2 along the negative segment lands on the curved marked edge. -/

theorem negative_source_marking {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (hre : ∀ x ∈ Ioo (-1:ℝ) 0, (f (x:ℂ)).im = 0)
    (e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')})
    (he : (e:ℍ).re=1) (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 0) :
    ∃ (a : sourceDisk t) (p : Path (sourceBasepoint ht ht') a),
      (a:ℂ)=(x:ℂ) ∧ (∀ u, (p u:ℂ).im=0) ∧
      let τ := (lambdaPunctured_isCoveringMap.monodromy (.mk (p.map (sourceMap hf).continuous)) e : ℍ)
      τ.re=1 ∧ MarkedRealAxis.cusp (τ:ℂ) ∈ MarkedRealAxis.curvedEdge := by
  have hI (s : ℝ) (hs : s ∈ Ioo (-1:ℝ) 0) : (s:ℂ) ∈ sourceDisk t :=
    real_mem_sourceDisk ht (abs_lt.mpr ⟨hs.1,by linarith [hs.2]⟩) hs.2.ne
  let a : sourceDisk t := ⟨x,hI x hx⟩
  have hb : (sourceBasepoint ht ht':ℂ)=((-1/2:ℝ):ℂ) := by
    rw [sourceBasepoint_coe]; norm_num
  let p := realIntervalPath hI hb (a:=sourceBasepoint ht ht') (b:=a) (y:=x) rfl
    (show (-1/2:ℝ) ∈ Ioo (-1:ℝ) 0 by constructor <;> norm_num) hx
  let α := p.map (sourceMap hf).continuous
  have hα (u : unitInterval) : (α u:ℂ).im=0 :=
    hre _ ((convex_Ioo (-1:ℝ) 0).lineMap_mem (x:=(-1/2:ℝ)) (y:=x)
      (by constructor <;> norm_num) hx u.property)
  have hh := liftPath_re_of_real α hα e 1 (by simpa using he) 1
  let τ := (lambdaPunctured_isCoveringMap.monodromy (.mk α) e : ℍ)
  have hτ : τ.re=1 := by
    simpa only [τ,lambdaPunctured_isCoveringMap.coe_monodromy_mk,Int.cast_one] using hh
  refine ⟨a,p,rfl,fun _ ↦ rfl,hτ,?_⟩
  let vals (y : ℝ) : ℂ := if y < 0 then (τ:ℂ) else Complex.I
  have hn (y : ℝ) (hy : y ∈ Ioo (-1:ℝ) 0) : (vals y).re=1 ∧ 0 < (vals y).im := by
    simp only [vals,ite_eq_left hy.2]
    exact ⟨hτ,τ.im_pos⟩
  have hp (y : ℝ) (hy : y ∈ Ioo (0:ℝ) 1) : (vals y).re=0 ∧ 0 < (vals y).im := by
    simp [vals,not_lt.mpr hy.1.le]
  simpa only [vals,ite_eq_left hx.2] using (MarkedRealAxis.marked_real_axes hn hp).1 x hx

end BelgianChocolate.MarkedAxisTransport




namespace BelgianChocolate.MarkedAxisTransport
open Complex Metric Set unitInterval
open scoped ComplexConjugate
open BelgianChocolate.SourceDiskPaths
open BelgianChocolate.FirstAnnulus (halfTurn)
open BelgianChocolate.FirstAnnulusPaths (path_trans_property)

open Path.Homotopic.Quotient in
/-- Splitting the actual positive zero circle in physical coordinates gives two
paths from −1/2 to +t/5. The outward upper path is the reflection of the lower,
and the lower path followed by the reversed upper path has the prescribed zero label. -/
theorem source_zero_half_paths {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    ∃ (a : sourceDisk t) (U L : Path (sourceBasepoint ht ht') a),
      (a:ℂ)=((t/5:ℝ):ℂ) ∧
      (∀ u, 0 ≤ (U u:ℂ).im) ∧ (∀ u, (L u:ℂ) = conj (U u:ℂ)) ∧
      (L.trans U.symm).Homotopic (sourceGammaZero ht ht') := by
  obtain ⟨c,T,R,hT,hR,hword⟩ := sourceGammaZero_directed ht ht'
  let a := R halfTurn
  let lo := (R.subpath 0 halfTurn).cast R.source.symm rfl
  let hi := (R.subpath halfTurn 1).cast rfl R.target.symm
  let L := T.trans lo
  let U := T.trans hi.symm
  refine ⟨a,U,L,?_,?_,?_,?_⟩
  · change (R halfTurn:ℂ)=_
    rw [hR]
    change circleMap 0 (t/5) (Real.pi+2*Real.pi*(1/2))=_
    rw [show Real.pi+2*Real.pi*(1/2)=0+2*Real.pi by ring,periodic_circleMap]
    simp [circleMap]
  · have hTreal (v : I) : (T v:ℂ).im=0 := by
      rw [hT,AffineMap.lineMap_apply_module]
      simp [Complex.real_smul,Complex.mul_im]
    have hHi (v : I) : 0 ≤ (hi.symm v:ℂ).im := by
      change 0 ≤ (R (Icc.convexComb halfTurn 1 (unitInterval.symm v)):ℂ).im
      rw [hR,circleMap_zero_im,Icc.coe_convexComb]
      apply mul_nonneg (by positivity)
      rw [← Real.sin_sub_two_pi]
      change 0 ≤ Real.sin (Real.pi + 2*Real.pi*((1-(1-(v:ℝ)))*(1/2)+(1-(v:ℝ))*1)-2*Real.pi)
      apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
        nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le v.2.1,
          mul_nonneg Real.pi_pos.le (sub_nonneg.mpr v.2.2)]
    exact path_trans_property (P:=fun z : sourceDisk t ↦ 0 ≤ (z:ℂ).im) (p:=T) (q:=hi.symm)
      (fun v ↦ (hTreal v).ge) hHi
  · intro u
    change ((T.trans lo) u:ℂ)=conj ((T.trans hi.symm) u:ℂ)
    rw [Path.trans_apply,Path.trans_apply]
    split
    · rw [hT,AffineMap.lineMap_apply_module]
      simp [Complex.real_smul, map_ofNat]
    · change (R (Icc.convexComb 0 halfTurn _):ℂ) =
        conj (R (Icc.convexComb halfTurn 1 (unitInterval.symm _)):ℂ)
      rw [hR,hR,conj_circleMap,map_zero, Icc.coe_convexComb,Icc.coe_convexComb]
      generalize (⟨2 * (u:ℝ) - 1, _⟩ : I) = v
      change circleMap 0 (t/5) (Real.pi+2*Real.pi*((1-(v:ℝ))*0+(v:ℝ)*(1/2))) =
        circleMap 0 (t/5) (-(Real.pi+2*Real.pi*((1-(1-(v:ℝ)))*(1/2)+(1-(v:ℝ))*1)))
      rw [show Real.pi+2*Real.pi*((1-(v:ℝ))*0+(v:ℝ)*(1/2)) =
        -(Real.pi+2*Real.pi*((1-(1-(v:ℝ)))*(1/2)+(1-(v:ℝ))*1))+2*Real.pi+2*Real.pi by ring,
        periodic_circleMap,periodic_circleMap]
  · have h := (Path.Homotopic.subpath_trans_subpath R 0 halfTurn 1).pathCast
      R.source.symm R.target.symm
    rw [Path.subpath_zero_one] at h
    have hc : (lo.trans hi).Homotopic R := by
      convert h using 1 <;> exact Path.ext (by rfl)
    rw [hword]
    apply eq.mp
    have hq := eq.mpr hc
    simp only [mk_trans] at hq
    simp only [L,U,Path.trans_symm,Path.symm_symm,mk_trans,mk_symm,← hq,trans_assoc]

end BelgianChocolate.MarkedAxisTransport


namespace BelgianChocolate.MarkedAxisTransport
open Complex Set Metric Topology UpperHalfPlane
open scoped MatrixGroups ComplexConjugate
open BelgianChocolate.SourceDiskPaths BelgianChocolate.ModularLambdaRatio
open BelgianChocolate.ModularLambdaReflection

private theorem cuspPeriod_eq_zeroCuspDeck : cuspPeriod = zeroCuspDeck := by
  apply Subtype.ext
  change sl2zToPSL2R (ModularGroup.T ^ (2:ℤ)) = sl2zToPSL2R BelgianChocolate.FirstAnnulus.zeroGenerator
  rw [BelgianChocolate.FirstAnnulus.zeroGenerator_eq_T_sq]
  rfl

/-- Reflecting a path with two real endpoints transports the corrected
reflection of its initial lift to the corrected reflection of its final lift. -/
theorem reflected_path_endpoint {a b : ({0,1}ᶜ : Set ℂ)}
    (α β : Path a b) (e : lambdaPunctured ⁻¹' {a}) (g : gammaTwoProjective)
    (hfix : deckReflection g (e:ℍ) = e)
    (href : ∀ u, (β u:ℂ) = conj (α u:ℂ)) :
    (lambdaPunctured_isCoveringMap.monodromy (.mk β) e:ℍ) =
      deckReflection g (lambdaPunctured_isCoveringMap.monodromy (.mk α) e:ℍ) := by
  let hp := lambdaPunctured_isCoveringMap
  let Γ := hp.liftPath α (e:ℍ) (α.source.trans e.property.symm)
  let Δ := (deckReflection g).comp Γ
  have hproj : lambdaPunctured ∘ Δ = β := by
    funext u
    change lambdaPunctured (deckReflection g (Γ u)) = β u
    rw [lambdaPunctured_deckReflection]
    apply Subtype.ext
    change conj (lambdaRatio (Γ u)) = (β u:ℂ)
    have hh : lambdaRatio (Γ u) = (α u:ℂ) :=
      congrArg Subtype.val (congrFun (hp.liftPath_lifts α (e:ℍ) _) u)
    rw [hh,href]
  have hfirst : Δ 0 = (e:ℍ) := by
    change deckReflection g (Γ 0) = (e:ℍ)
    rw [show Γ 0 = e from hp.liftPath_zero ..]
    exact hfix
  calc
    (hp.monodromy (.mk β) e:ℍ) = Δ 1 := hp.monodromy_eq_apply_one hproj hfirst
    _ = deckReflection g (hp.monodromy (.mk α) e:ℍ) := by
      rw [hp.coe_monodromy_mk]
      rfl

open Path.Homotopic.Quotient in
/-- Crossing above zero through half of the actual peripheral loop changes
the real part of the lifted branch from one to zero. -/
theorem upper_half_endpoint_re {a b : ({0,1}ᶜ : Set ℂ)}
    (U L : Path a b) (e : lambdaPunctured ⁻¹' {a}) (he : (e:ℍ).re=1)
    (href : ∀ u, (L u:ℂ)=conj (U u:ℂ))
    (hloop : lambdaPunctured_isCoveringMap.monodromy (.mk (L.trans U.symm)) e =
      lambdaPunctured_quotientCovering.toPermFiber a zeroCuspDeck e) :
    (lambdaPunctured_isCoveringMap.monodromy (.mk U) e:ℍ).re=0 := by
  let hp := lambdaPunctured_isCoveringMap
  let hq := lambdaPunctured_quotientCovering
  have hfix : deckReflection zeroCuspDeck (e:ℍ) = e := by
    have h := (axisReflection_fixed_iff 1 (e:ℍ)).mpr (by simpa using he)
    simpa only [zpow_one,cuspPeriod_eq_zeroCuspDeck] using h
  have hR := reflected_path_endpoint U L e zeroCuspDeck hfix href
  have halg : (mk (L.trans U.symm)).trans (mk U) = mk L := by
    simp only [mk_trans,mk_symm,trans_assoc,symm_trans,trans_refl]
  have h : hp.monodromy (.mk L) e = hq.toPermFiber b zeroCuspDeck (hp.monodromy (.mk U) e) := by
    rw [← halg,hp.monodromy_trans_apply,hloop,hq.monodromy_toPermFiber]
  let w : ℍ := hp.monodromy (.mk U) e
  have hev : zeroCuspDeck • (J • w) = zeroCuspDeck • w :=
    hR.symm.trans (congrArg Subtype.val h)
  have hw : J • w = w := MulAction.injective zeroCuspDeck hev
  have hw' := congrArg (fun y : ℍ ↦ (y:ℂ).re) hw
  simp only [UpperHalfPlane.coe_J_smul,Complex.neg_re,Complex.conj_re] at hw'
  change (w:ℂ).re=0
  linarith

theorem positive_anchor {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) (hreal : RealSymmetricOnDisk f)
    (e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')})
    (he : (e:ℍ).re=1)
    (hA : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((sourceGammaZero ht ht').map (sourceMap hf).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e) :
    ∃ (a : sourceDisk t) (U : Path (sourceBasepoint ht ht') a),
      (a:ℂ)=((t/5:ℝ):ℂ) ∧ (∀ u, 0 ≤ (U u:ℂ).im) ∧
      (lambdaPunctured_isCoveringMap.monodromy (.mk (U.map (sourceMap hf).continuous)) e:ℍ).re=0 := by
  obtain ⟨a,U,L,ha,hU,href,h⟩ := source_zero_half_paths ht ht'
  let F := sourceMap hf
  refine ⟨a,U,ha,hU,upper_half_endpoint_re (U.map F.continuous) (L.map F.continuous) e he ?_ ?_⟩
  · intro u
    change f (L u:ℂ)=conj (f (U u:ℂ))
    rw [href,hreal _ (mem_ball_zero_iff.mpr (U u).property.1)]
  · have hm := Path.Homotopic.Quotient.eq.mpr (h.map F)
    rw [Path.map_trans,← Path.map_symm] at hm
    rw [hm]
    exact hA

end BelgianChocolate.MarkedAxisTransport

namespace BelgianChocolate.MarkedAxisTransport
open Complex Set Metric Topology UpperHalfPlane
open scoped MatrixGroups ComplexConjugate
open BelgianChocolate.SourceDiskPaths BelgianChocolate.ModularLambdaRatio
open BelgianChocolate.ModularLambdaReflection

theorem real_target_on_diameter {f : ℂ → ℂ} (hreal : RealSymmetricOnDisk f)
    {x : ℝ} (hx : |x| < 1) : (f (x:ℂ)).im=0 := by
  have h := hreal (x:ℂ) (mem_ball_zero_iff.mpr (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx))
  rw [Complex.conj_ofReal] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

private theorem cusp_zero_axis (τ : ℂ) (hr : τ.re=0) (hi : 0<τ.im) :
    ∃ r ∈ Ioo (-1:ℝ) 0, MarkedRealAxis.cusp (τ:ℂ)=(r:ℂ) := by


  have hnorm : Complex.normSq (τ:ℂ) = (τ:ℂ).im ^ 2 := by
    simp [Complex.normSq_apply, hr, pow_two]
  have he : -((Real.pi : ℂ) * Complex.I) / (τ:ℂ) = ((-(Real.pi / (τ:ℂ).im) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.div_re, hr, hnorm]
      field_simp
    · simp [Complex.div_im, hr, hnorm]
  refine ⟨-Real.exp (-(Real.pi / (τ:ℂ).im)), ⟨?_, neg_lt_zero.mpr (Real.exp_pos _)⟩, ?_⟩
  · have h := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos Real.pi_pos hi))
    linarith
  · simp [MarkedRealAxis.cusp, he, Complex.ofReal_exp]

/-- One common initial lift determines both axis markings. The positive
paths all share the upper half-circle continuation from the negative basepoint. -/
theorem source_axis_markings {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) (hreal : RealSymmetricOnDisk f)
    (e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')})
    (he : (e:ℍ).re=1)
    (hA : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((sourceGammaZero ht ht').map (sourceMap hf).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e) :
    (∀ x ∈ Ioo (-1:ℝ) 0, ∃ (a : sourceDisk t) (p : Path (sourceBasepoint ht ht') a),
      (a:ℂ)=(x:ℂ) ∧ (∀ u, (p u:ℂ).im=0) ∧
      let τ := (lambdaPunctured_isCoveringMap.monodromy (.mk (p.map (sourceMap hf).continuous)) e:ℍ)
      τ.re=1 ∧ MarkedRealAxis.cusp (τ:ℂ) ∈ MarkedRealAxis.curvedEdge) ∧
    (∃ (c : sourceDisk t) (U : Path (sourceBasepoint ht ht') c),
      (c:ℂ)=((t/5:ℝ):ℂ) ∧ (∀ u, 0 ≤ (U u:ℂ).im) ∧
      ∀ x ∈ Ioo (0:ℝ) 1, ∃ (a : sourceDisk t) (p : Path c a),
        (a:ℂ)=(x:ℂ) ∧ (∀ u, (p u:ℂ).im=0) ∧
        let τ := (lambdaPunctured_isCoveringMap.monodromy
          (.mk ((U.trans p).map (sourceMap hf).continuous)) e:ℍ)
        τ.re=0 ∧ ∃ r ∈ Ioo (-1:ℝ) 0, MarkedRealAxis.cusp (τ:ℂ)=(r:ℂ)) := by
  constructor
  · exact negative_source_marking ht ht' hf (fun x hx ↦ real_target_on_diameter hreal
      (abs_lt.mpr ⟨hx.1,by linarith [hx.2]⟩)) e he
  · obtain ⟨c,U,hc,hU,hAnchor⟩ := positive_anchor ht ht' hf hreal e he hA
    refine ⟨c,U,hc,hU,?_⟩
    intro x hx
    have hI (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) : (s:ℂ) ∈ sourceDisk t :=
      real_mem_sourceDisk ht (abs_lt.mpr ⟨by linarith [hs.1],hs.2⟩) hs.1.ne'
    have ht₅ : t/5 ∈ Ioo (0:ℝ) 1 := ⟨by positivity,by linarith⟩
    let a : sourceDisk t := ⟨x,hI x hx⟩
    let p := realIntervalPath hI hc (a:=c) (b:=a) (y:=x) rfl ht₅ hx
    let F := sourceMap hf
    let hp := lambdaPunctured_isCoveringMap
    let e' := hp.monodromy (.mk (U.map F.continuous)) e
    have hα (u : unitInterval) : ((p.map F.continuous) u:ℂ).im=0 := by
      have hIu := (convex_Ioo (0:ℝ) 1).lineMap_mem ht₅ hx u.property
      exact real_target_on_diameter hreal (abs_lt.mpr ⟨by linarith [hIu.1],hIu.2⟩)
    have hh := liftPath_re_of_real (p.map F.continuous) hα e' 0 (by simpa [e',hp,F] using hAnchor) 1
    let τ : ℍ := hp.monodromy (.mk ((U.trans p).map F.continuous)) e
    have hτ : τ.re=0 := by
      dsimp only [τ]
      rw [Path.map_trans, FirstAnnulusTransport.transport_trans, hp.coe_monodromy_mk]
      exact hh
    exact ⟨a,p,rfl,fun _ ↦ rfl,hτ,cusp_zero_axis (τ:ℂ) hτ τ.im_pos⟩

end BelgianChocolate.MarkedAxisTransport



