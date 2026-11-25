import MarkedAxisSlit
import MarkedAxisContinuation
import ModularLambdaCuspMonodromy

namespace BelgianChocolate.MarkedAxisSlit
open Complex Set Metric Topology UpperHalfPlane
open scoped MatrixGroups
open BelgianChocolate.SourceDiskPaths BelgianChocolate.ModularLambdaRatio
open BelgianChocolate.MarkedAxisTransport

/-- Evaluation of a single based cusp lift agrees with modular transport
along any physical path contained in the closed upper half disk. -/
theorem eval_lift_on_upper_path {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f)
    (e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')})
    (Φ : C(Domain t,PuncturedUnitDisc))
    (hbase : Φ (basepoint ht ht') = markedCuspDisc e)
    (hΦ : cuspUPunctured ∘ Φ = (sourceMap hf) ∘ (inclusion ht))
    {a : sourceDisk t} (p : Path (sourceBasepoint ht ht') a)
    (hU : ∀ u, 0 ≤ (p u:ℂ).im) {v : Domain t} (hv : (v:ℂ)=(a:ℂ)) :
    Φ v = markedCuspDisc (lambdaPunctured_isCoveringMap.monodromy
      (.mk (p.map (sourceMap hf).continuous)) e) := by
  let p' : Path (basepoint ht ht') v := restrictPath p (fun u ↦ mem_of_im_nonneg _ (hU u)) rfl hv
  let α := p.map (sourceMap hf).continuous
  let hp := lambdaPunctured_isCoveringMap
  let Γ := hp.liftPath α (e:ℍ) (α.source.trans e.property.symm)
  have hp' (u : unitInterval) : inclusion ht (p' u) = p u := Subtype.ext rfl
  have hl : cuspUPunctured ∘ (Φ ∘ p') = cuspUPunctured ∘ (markedCuspDisc ∘ Γ) := by
    funext u
    change cuspUPunctured (Φ (p' u)) = cuspUPunctured (markedCuspDisc (Γ u))
    rw [cuspUPunctured_markedCuspDisc,show cuspUPunctured (Φ (p' u)) =
        sourceMap hf (inclusion ht (p' u)) from congrFun hΦ (p' u),hp']
    exact (congrFun (hp.liftPath_lifts α (e:ℍ) _) u).symm
  have h0 : Φ (p' 0) = markedCuspDisc (Γ 0) := by
    rw [p'.source,show Γ 0 = e from hp.liftPath_zero ..,hbase]
  have h := cuspUPunctured_isCoveringMap.eq_of_comp_eq (Φ.continuous.comp p'.continuous)
    (markedCuspDisc_continuous.comp Γ.continuous) hl 0 h0
  have he := congrFun h 1
  change Φ (p' 1) = markedCuspDisc (Γ 1) at he
  rw [p'.target] at he
  exact he

/-- A single lift on the open slit neighborhood has the manuscript's two
boundary markings. Both follow from the same normalized lift at −1/2. -/
theorem lift_marked_real_axes {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {f : ℂ → ℂ} (hf : MarkedCompetitor t f) (hreal : RealSymmetricOnDisk f)
    (e : lambdaPunctured ⁻¹' {sourceMap hf (sourceBasepoint ht ht')}) (he : (e:ℍ).re=1)
    (hA : lambdaPunctured_isCoveringMap.monodromy
      (.mk ((sourceGammaZero ht ht').map (sourceMap hf).continuous)) e =
      lambdaPunctured_quotientCovering.toPermFiber _ zeroCuspDeck e)
    (Φ : C(Domain t,PuncturedUnitDisc)) (hbase : Φ (basepoint ht ht') = markedCuspDisc e)
    (hΦ : cuspUPunctured ∘ Φ = (sourceMap hf) ∘ (inclusion ht)) :
    ∀ v : Domain t, (v:ℂ).im=0 →
      ((v:ℂ).re < 0 → (Φ v:ℂ) ∈ MarkedRealAxis.curvedEdge) ∧
      (0 < (v:ℂ).re → ∃ r ∈ Ioo (-1:ℝ) 0, (Φ v:ℂ)=(r:ℂ)) := by
  obtain ⟨hneg,c,U,_,hU,hpos⟩ := source_axis_markings ht ht' hf hreal e he hA
  intro v him
  have hr : |(v:ℂ).re|<1 := (v:ℂ).abs_re_le_norm.trans_lt v.property.1.1
  have hv : (v:ℂ)=((v:ℂ).re:ℂ) := Complex.ext rfl (by simpa using him)
  constructor
  · intro hneg'
    obtain ⟨a,p,ha,hp,_,hcurve⟩ := hneg (v:ℂ).re ⟨(abs_lt.mp hr).1,hneg'⟩
    have hh := eval_lift_on_upper_path ht ht' hf e Φ hbase hΦ p (fun u ↦ (hp u).ge) (hv.trans ha.symm)
    rw [hh]
    exact hcurve
  · intro hpos'
    obtain ⟨a,p,ha,hp,_,haxis⟩ := hpos (v:ℂ).re ⟨hpos',(abs_lt.mp hr).2⟩
    have hpath := FirstAnnulusPaths.path_trans_property
      (P:=fun z : sourceDisk t ↦ 0 ≤ (z:ℂ).im) (p:=U) (q:=p) hU (fun u ↦ (hp u).ge)
    have hh := eval_lift_on_upper_path ht ht' hf e Φ hbase hΦ (U.trans p) hpath (hv.trans ha.symm)
    rw [hh]
    exact haxis

end BelgianChocolate.MarkedAxisSlit

