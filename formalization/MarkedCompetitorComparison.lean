import ControllerDiskCompetitor
import MarkedCompetitorLift
import DiskFeasibility
import SourceDiskRealNormalization
import MarkedBoundaryComparison
import ComparisonSourceChart
import MarkedAxisSlit

namespace BelgianChocolate.HarmonicComparison
open Complex Filter Metric Set Topology
open BelgianChocolate.MarkedAxisSlit

/-- Markings required of the candidate on the upper half-disk and its three
open edges. The endpoint condition refers to either end of the curved edge. -/
structure ComparisonCandidate (ts : ℝ) (Φ : ℂ → ℂ) : Prop where
  differentiable : DifferentiableOn ℂ Φ comparisonHalfDisk
  maps : MapsTo Φ comparisonHalfDisk (ball 0 1)
  center : Φ ((ts:ℂ)*Complex.I) = 0
  continuous : ContinuousOn Φ (closure comparisonHalfDisk)
  negative : ∀ x ∈ Ioo (-1:ℝ) 0, Φ (x:ℂ) ∈ MarkedRealAxis.curvedEdge
  positive : ∀ x ∈ Ioo (0:ℝ) 1, ∃ y ∈ Ioo (-1:ℝ) 0, Φ (x:ℂ)=(y:ℂ)
  outer : MapsTo Φ comparisonOuterArc {p | ‖p‖=1 ∧ p.im<0}
  endValues : ∀ x ∈ ({-1,0}:Set ℂ), Φ x=1 ∨ Φ x= -1

private noncomputable def graphArc (η : ℂ → ℂ) : Set ℂ := sphere 0 1 ∩ η ⁻¹' (Complex.ofReal '' Ioo (-1:ℝ) 0)
private noncomputable def seamSet (η : ℂ → ℂ) : Set ℂ := sphere 0 1 ∩ η ⁻¹' comparisonSeams

private theorem candidate_seam {ts : ℝ} {η Φ : ℂ → ℂ} (hη : CenteredComparisonChart ts η)
    (hΦ : ComparisonCandidate ts Φ) {ξ : ℂ} (he : ξ ∈ seamSet η) :
    𝓝[graphArc η] ξ = ⊥ ∨
      Tendsto (fun z ↦ Φ (η z)) (𝓝[graphArc η] ξ) (𝓝[MarkedRealAxis.curvedEdge] (1:ℂ)) ∨
      Tendsto (fun z ↦ Φ (η z)) (𝓝[graphArc η] ξ) (𝓝[MarkedRealAxis.curvedEdge] (-1:ℂ)) := by
  by_cases hb : 𝓝[graphArc η] ξ = ⊥
  · exact Or.inl hb
  let _ : NeBot (𝓝[graphArc η] ξ) := ⟨hb⟩
  have hsub : graphArc η ⊆ closedBall (0:ℂ) 1 := fun _ hz ↦ sphere_subset_closedBall hz.1
  have hξ : ξ ∈ closedBall (0:ℂ) 1 := sphere_subset_closedBall he.1
  have hηlim := (hη.closed_continuous ξ hξ).mono hsub
  have hr : (η ξ).re ≤ 0 := by
    apply le_of_tendsto ((Complex.continuous_re.continuousAt).tendsto.comp hηlim)
    filter_upwards [self_mem_nhdsWithin] with z hz
    obtain ⟨x,hx,hh⟩ := hz.2
    change (η z).re ≤ 0
    rw [← hh]
    exact hx.2.le
  have hh : η ξ ∈ ({-1,0}:Set ℂ) := by
    have hs := he.2
    change η ξ ∈ ({-1,0,1}:Set ℂ) at hs
    simp only [mem_insert_iff,mem_singleton_iff] at hs ⊢
    rcases hs with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hr; norm_num at hr
  have hlim : Tendsto (fun z ↦ Φ (η z)) (𝓝[graphArc η] ξ) (𝓝[MarkedRealAxis.curvedEdge] (Φ (η ξ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((hΦ.continuous.comp hη.closed_continuous hη.closed_bij.mapsTo) ξ hξ).mono hsub,?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    obtain ⟨x,hx,hh⟩ := hz.2
    rw [← hh]
    exact hΦ.negative x hx
  exact Or.inr (by rcases hΦ.endValues _ hh with h|h; exact Or.inl (h ▸ hlim); exact Or.inr (h ▸ hlim))

private theorem scale_neg_range {r x : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (hx : x ∈ Ioo (-1:ℝ) 0) :
    r*x ∈ Ioo (-1:ℝ) 0 :=
  ⟨by nlinarith [hx.1,mul_nonneg (sub_nonneg.mpr hr') (neg_nonneg.mpr hx.2.le)],mul_neg_of_pos_of_neg hr hx.2⟩

private theorem scale_pos_range {r x : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (hx : x ∈ Ioo (0:ℝ) 1) :
    r*x ∈ Ioo (0:ℝ) 1 := ⟨mul_pos hr hx.1, (mul_le_of_le_one_left hx.1.le hr').trans_lt hx.2⟩

private theorem real_scaled_cont {r x : ℝ} {φ η : ℂ → ℂ} {ξ : ℂ}
    (hd : DifferentiableOn ℂ φ slit) (hη : ContinuousWithinAt η (closedBall 0 1) ξ)
    (hξ : η ξ=(x:ℂ)) (hrx : |r*x|<1) (hn : r*x ≠ 0) :
    ContinuousWithinAt (fun z ↦ φ ((r:ℂ)*η z)) (closedBall 0 1) ξ := by
  have he : (r:ℂ)*η ξ=((r*x:ℝ):ℂ) := by rw [hξ,Complex.ofReal_mul]
  have hz : (r:ℂ)*η ξ ∈ slit := by
    rw [he]
    exact ⟨by simpa only [Complex.norm_real,Real.norm_eq_abs] using hrx, Or.inl hn⟩
  exact ContinuousAt.comp_continuousWithinAt (g:=φ) (f:=fun z ↦ (r:ℂ)*η z)
    (hd.differentiableAt (isOpen_slit.mem_nhds hz)).continuousAt (continuousWithinAt_const.mul hη)

/-- Once the candidate and the centered chart supply their boundary data,
the scaled comparison forces the parameter and lifts to coincide. -/
theorem eq_parameter_and_lift_of_marked_competitor {t ts : ℝ} (ht : 0<t) (hts : 0<ts) (hle : t≤ts)
    {η Φ φ : ℂ → ℂ} (hη : CenteredComparisonChart ts η) (hΦ : ComparisonCandidate ts Φ)
    (hd : DifferentiableOn ℂ φ slit) (hm : ∀ z ∈ slit, ‖φ z‖<1)
    (hz : φ ((t:ℂ)*Complex.I)=0)
    (hn : ∀ x ∈ Ioo (-1:ℝ) 0, φ (x:ℂ) ∈ MarkedRealAxis.curvedEdge)
    (hp : ∀ x ∈ Ioo (0:ℝ) 1, ∃ y ∈ Ioo (-1:ℝ) 0, φ (x:ℂ)=(y:ℂ)) :
    t=ts ∧ EqOn φ Φ comparisonHalfDisk := by
  let r := t/ts
  have hr : 0<r := div_pos ht hts
  have hr' : r≤1 := (div_le_one hts).mpr hle
  have hs : comparisonHalfDisk ⊆ slit := fun _ h ↦ ⟨mem_ball_zero_iff.mp h.1,Or.inr h.2⟩
  have hd' := hd.mono hs
  have hm' : MapsTo φ comparisonHalfDisk (ball 0 1) := fun z h ↦ mem_ball_zero_iff.mpr (hm z (hs h))
  have hfin : (seamSet η).Finite :=
    (comparisonSeams_finite.subset (show η '' seamSet η ⊆ comparisonSeams from
      image_subset_iff.mpr (fun _ h ↦ h.2))).of_finite_image
      (hη.frontier_bij.injOn.mono inter_subset_left)
  apply eq_parameter_and_lifts_of_closedDisc_comparison ht hts hle hη.interior_bij.surjOn hη.outer_surjOn hη.closed_continuous
    (hΦ.continuous.comp hη.closed_continuous hη.closed_bij.mapsTo) hΦ.outer hd'.continuousOn hm'
  apply eqOn_of_markedLifts (G:=graphArc η) (E:=seamSet η)
    (hΦ.differentiable.comp hη.holomorphic hη.interior_bij.mapsTo) (differentiableOn_shrunkLift hr hr' hη.holomorphic hη.interior_bij.mapsTo hd')
    (by change Φ (η 0)=0; rw [hη.zero,hΦ.center]) (shrunkLift_zero hts hη.zero hz)
    (fun _ h ↦ mem_ball_zero_iff.mp (hΦ.maps (hη.interior_bij.mapsTo h))) (shrunkLift_norm_lt_one hr hr' hη.interior_bij.mapsTo hm') hfin
  · intro ξ hG hNorm _
    obtain ⟨x,hx,he⟩ := hG.2
    have hscaled := scale_neg_range hr hr' hx
    have hval : φ ((r:ℂ)*η ξ)=φ ((r*x:ℝ):ℂ) := by rw [← he,Complex.ofReal_mul]
    exact ⟨real_scaled_cont hd (hη.closed_continuous ξ (sphere_subset_closedBall hG.1)) he.symm
      (abs_lt.mpr ⟨hscaled.1,by linarith [hscaled.2]⟩) hscaled.2.ne,
      (hΦ.continuous.comp hη.closed_continuous hη.closed_bij.mapsTo) ξ (sphere_subset_closedBall hG.1),hval ▸ hn _ hscaled,(by change Φ (η ξ) ∈ _; rw [← he]; exact hΦ.negative _ hx)⟩
  · intro ξ hNorm hG hE
    have hξ : ξ ∈ sphere (0:ℂ) 1 := by simpa [mem_sphere,dist_eq_norm] using hNorm
    have hξcl := sphere_subset_closedBall hξ
    have hpart := frontier_comparisonHalfDisk_other (hη.frontier_bij.mapsTo hξ) (fun h ↦ hE ⟨hξ,h⟩)
    rcases hpart with houter|hneg|⟨x,hx,he⟩
    · exact Or.inr ⟨_,((hΦ.continuous.comp hη.closed_continuous hη.closed_bij.mapsTo) ξ hξcl).mono ball_subset_closedBall,(hΦ.outer houter).1,(hΦ.outer houter).2⟩
    · exact (hG ⟨hξ,hneg⟩).elim
    · have hscaled := scale_pos_range hr hr' hx
      obtain ⟨v,hv,hvφ⟩ := hp _ hscaled
      obtain ⟨q,hq,hqΦ⟩ := hΦ.positive _ hx
      have hval : φ ((r:ℂ)*η ξ)=(v:ℂ) := by rw [← he,← Complex.ofReal_mul,hvφ]
      have hval' : Φ (η ξ)=(q:ℂ) := he ▸ hqΦ
      have hl := real_scaled_cont hd (hη.closed_continuous ξ hξcl) he.symm
        (abs_lt.mpr ⟨by linarith [hscaled.1],hscaled.2⟩) hscaled.1.ne'
      refine Or.inl ⟨_,_,hl.mono ball_subset_closedBall,((hΦ.continuous.comp hη.closed_continuous hη.closed_bij.mapsTo) ξ hξcl).mono ball_subset_closedBall,?_,?_,?_,?_⟩
      · change ‖φ ((r:ℂ)*η ξ)‖<1
        rw [hval]; simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_lt.mpr ⟨hv.1,by linarith [hv.2]⟩
      · change (φ ((r:ℂ)*η ξ)).im=0
        rw [hval]; rfl
      · change ‖Φ (η ξ)‖<1
        rw [hval']; simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_lt.mpr ⟨hq.1,by linarith [hq.2]⟩
      · change (Φ (η ξ)).im=0
        rw [hval']; rfl
  · exact fun _ he _ ↦ candidate_seam hη hΦ he

end BelgianChocolate.HarmonicComparison


namespace BelgianChocolate.HarmonicComparison
open Complex Filter Metric Set Topology
open BelgianChocolate.SourceDiskPaths BelgianChocolate.ModularLambdaRatio

/-- For an actual, positively normalized competitor, boundary comparison gives
the threshold equality and equality to the candidate everywhere in the unit disk. -/
theorem parameter_and_disk_rigidity_of_candidate {t ts : ℝ}
    (ht : 0<t) (hts : 0<ts) (hts₁ : ts<1) (htSmall : t≤1/10) (hle : t≤ts)
    {Φ f fs : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ)
    (hfs : MarkedCompetitor ts fs) (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z)=fs z)
    (hf : MarkedCompetitor t f) (hreal : RealSymmetricOnDisk f)
    {d : ℝ} (hd : HasDerivAt f (d:ℂ) 0) (hpos : 0<d) :
    t=ts ∧ EqOn f fs (ball 0 1) := by
  obtain ⟨η,hη⟩ := exists_centered_comparisonChart hts hts₁
  obtain ⟨φ,hφ,hmap,hfφ,hzero,_,hn,hp⟩ := exists_marked_competitor_lift ht htSmall hf hreal hd hpos
  obtain ⟨he,heq⟩ := eq_parameter_and_lift_of_marked_competitor ht hts hle hη hΦ hφ hmap hzero hn hp
  refine ⟨he,disk_eqOn_of_upper_halfDisk hf hfs ?_⟩
  intro z hz
  have hz' : z ∈ comparisonHalfDisk := comparisonHalfDisk_eq_norm ▸ hz
  have hzslit : z ∈ MarkedAxisSlit.slit := MarkedAxisSlit.upper_subset_slit hz
  rw [← hfφ z hzslit,heq hz',hrep z hz']

/-- Without imposing the sign of the derivative, the only equality cases
are the candidate and its source reflection. -/
theorem parameter_and_disk_rigidity_up_to_reflection {t ts : ℝ}
    (ht : 0<t) (hts : 0<ts) (hts₁ : ts<1) (htSmall : t≤1/10) (hle : t≤ts)
    {Φ f fs : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ)
    (hfs : MarkedCompetitor ts fs) (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z)=fs z)
    (hf : MarkedCompetitor t f) (hreal : RealSymmetricOnDisk f) :
    t=ts ∧ (EqOn f fs (ball 0 1) ∨ EqOn f (fun z ↦ fs (-z)) (ball 0 1)) := by
  obtain ⟨g,d,hg,hgm,hgr,hgd,him,hpos⟩ := exists_positive_source_derivative hf hreal
  have hd : (d.re:ℂ)=d := Complex.ext rfl (by simpa using him.symm)
  obtain ⟨he,heq⟩ := parameter_and_disk_rigidity_of_candidate ht hts hts₁ htSmall hle hΦ hfs hrep hgm hgr
    (hd.symm ▸ hgd) hpos
  refine ⟨he,?_⟩
  rcases hg with rfl|rfl
  · exact Or.inl heq
  · right
    intro z hz
    simpa only [neg_neg] using heq (x:=-z) (by simpa using hz)

/-- Given a candidate satisfying the chart and boundary conditions, the
disk feasibility set on (0,1) has its lower endpoint at the candidate. -/
theorem disk_feasible_iff_candidate_le {t ts : ℝ}
    (ht : 0<t) (hts : 0<ts) (hsmall : ts≤1/10)
    {Φ fs : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ)
    (hfs : MarkedCompetitor ts fs) (hreal : RealSymmetricOnDisk fs)
    (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z)=fs z) :
    (∃ f : ℂ → ℂ, MarkedCompetitor t f ∧ RealSymmetricOnDisk f) ↔ ts ≤ t := by
  constructor
  · rintro ⟨f,hf,hr⟩
    by_contra! htlt
    exact htlt.ne (parameter_and_disk_rigidity_up_to_reflection ht hts (by linarith) (htlt.le.trans hsmall) htlt.le hΦ hfs hrep hf hr).1
  · intro hle
    exact disk_feasible_of_le hts hle hfs hreal

/-- The physical feasible parameters in (0,1) form the half-open interval
with the candidate endpoint, conditional on the candidate's construction. -/
theorem disk_feasible_set_of_candidate {ts : ℝ} (hts : 0<ts) (hsmall : ts≤1/10)
    {Φ fs : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ)
    (hfs : MarkedCompetitor ts fs) (hreal : RealSymmetricOnDisk fs)
    (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z)=fs z) :
    {t : ℝ | 0<t ∧ t<1 ∧ ∃ f : ℂ → ℂ, MarkedCompetitor t f ∧ RealSymmetricOnDisk f} = Ico ts 1 := by
  ext t
  constructor
  · rintro ⟨ht,ht₁,hf⟩
    exact ⟨(disk_feasible_iff_candidate_le ht hts hsmall hΦ hfs hreal hrep).mp hf,ht₁⟩
  · rintro ⟨hle,ht₁⟩
    exact ⟨hts.trans_le hle,ht₁,disk_feasible_of_le hts hle hfs hreal⟩

/-- Any certified disk witness at or below one tenth puts the constructed
candidate itself into the range covered by the two annulus estimates. -/
theorem candidate_le_of_small_feasible_witness {ts u : ℝ} (hts : 0<ts) (hts₁ : ts<1)
    (hu : 0<u) (huSmall : u≤1/10) {Φ fs g : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ)
    (hfs : MarkedCompetitor ts fs) (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z)=fs z)
    (hg : MarkedCompetitor u g) (hreal : RealSymmetricOnDisk g) : ts≤u := by
  by_contra! hlt
  exact hlt.ne (parameter_and_disk_rigidity_up_to_reflection hu hts hts₁ huSmall
    hlt.le hΦ hfs hrep hg hreal).1

/-- A small disk witness can replace an a priori bound on the candidate
parameter in the description of the entire set of feasible disk parameters. -/
theorem disk_feasible_set_of_candidate_and_witness {ts u : ℝ}
    (hts : 0<ts) (hts₁ : ts<1) (hu : 0<u) (huSmall : u≤1/10)
    {Φ fs g : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ)
    (hfs : MarkedCompetitor ts fs) (hreal : RealSymmetricOnDisk fs)
    (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z)=fs z)
    (hg : MarkedCompetitor u g) (hgReal : RealSymmetricOnDisk g) :
    {t : ℝ | 0<t ∧ t<1 ∧ ∃ f : ℂ → ℂ, MarkedCompetitor t f ∧ RealSymmetricOnDisk f} = Ico ts 1 :=
  disk_feasible_set_of_candidate hts
    ((candidate_le_of_small_feasible_witness hts hts₁ hu huSmall hΦ hfs hrep hg hgReal).trans huSmall)
    hΦ hfs hreal hrep

/-- The certified controller witness supplies the small-parameter bound.
Only the actual candidate's realization and boundary data remain as inputs. -/
theorem disk_threshold_of_certified_witness {ts : ℝ} (hts : 0<ts) (hts₁ : ts<1)
    {Φ fs : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ)
    (hfs : MarkedCompetitor ts fs) (hreal : RealSymmetricOnDisk fs)
    (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z)=fs z) :
    ts ≤ ControlWitness.witnessT ∧ ts < 1/10 ∧
    {t : ℝ | 0<t ∧ t<1 ∧ ∃ f : ℂ → ℂ, MarkedCompetitor t f ∧ RealSymmetricOnDisk f} = Ico ts 1 ∧
    (∀ f : ℂ → ℂ, MarkedCompetitor ts f → RealSymmetricOnDisk f →
      (∀ d : ℝ, HasDerivAt f (d:ℂ) 0 → 0<d → EqOn f fs (ball 0 1)) ∧
      (EqOn f fs (ball 0 1) ∨ EqOn f (fun z ↦ fs (-z)) (ball 0 1))) := by
  obtain ⟨g,hg,hgr⟩ := ControlWitness.witness_marked
  have h := candidate_le_of_small_feasible_witness hts hts₁
    ControlWitness.witnessT_spec.2.1 ControlWitness.witnessT_spec.2.2.le hΦ hfs hrep hg
    (fun z _ ↦ hgr z)
  have hlt := h.trans_lt ControlWitness.witnessT_spec.2.2
  refine ⟨h,hlt,disk_feasible_set_of_candidate hts hlt.le hΦ hfs hreal hrep,?_⟩
  intro f hf hr
  exact ⟨fun d hd hp ↦ (parameter_and_disk_rigidity_of_candidate
    hts hts hts₁ hlt.le le_rfl hΦ hfs hrep hf hr hd hp).2,
    (parameter_and_disk_rigidity_up_to_reflection hts hts hts₁ hlt.le le_rfl
      hΦ hfs hrep hf hr).2⟩

/-- The candidate is itself positively normalized. Normalizing its simple
zero by reflection gives a positively oriented endpoint competitor, and
rigidity identifies that competitor with the original candidate near zero. -/
theorem candidate_positive_derivative {ts : ℝ} (hts : 0<ts) (hts₁ : ts<1)
    {Φ fs : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ)
    (hfs : MarkedCompetitor ts fs) (hreal : RealSymmetricOnDisk fs)
    (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z)=fs z) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt fs (d:ℂ) 0 := by
  obtain ⟨_,_,_,hrigid⟩ := disk_threshold_of_certified_witness hts hts₁ hΦ hfs hreal hrep
  obtain ⟨g,d,_,hg,hgr,hgd,him,hpos⟩ := exists_positive_source_derivative hfs hreal
  have hd : (d.re:ℂ)=d := Complex.ext rfl (by simpa using him.symm)
  have hgd' : HasDerivAt g (d.re:ℂ) 0 := hd.symm ▸ hgd
  have heq := (hrigid g hg hgr).1 d.re hgd' hpos
  have he : fs =ᶠ[𝓝 (0:ℂ)] g := Filter.mem_of_superset
    (ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1)) (fun _ hz ↦ (heq hz).symm)
  exact ⟨d.re,hpos,hgd'.congr_of_eventuallyEq he⟩

/-- Any two realized comparison candidates determine the same parameter and
the same marked lift. The common lift is obtained from an actual endpoint
competitor with positive source derivative. -/
theorem comparison_candidate_unique {ts tu : ℝ}
    (hts : 0 < ts) (hts₁ : ts < 1) (htu : 0 < tu) (htu₁ : tu < 1)
    {Φ Ψ fs fu : ℂ → ℂ} (hΦ : ComparisonCandidate ts Φ) (hΨ : ComparisonCandidate tu Ψ)
    (hfs : MarkedCompetitor ts fs) (hfu : MarkedCompetitor tu fu)
    (hfr : RealSymmetricOnDisk fs) (hur : RealSymmetricOnDisk fu)
    (hrep : ∀ z ∈ comparisonHalfDisk, cuspU (Φ z) = fs z)
    (hrep' : ∀ z ∈ comparisonHalfDisk, cuspU (Ψ z) = fu z) :
    ts = tu ∧ EqOn Φ Ψ comparisonHalfDisk ∧ EqOn fs fu (ball 0 1) := by
  obtain ⟨_, hsSmall, hsSet, _⟩ :=
    disk_threshold_of_certified_witness hts hts₁ hΦ hfs hfr hrep
  obtain ⟨_, _, huSet, _⟩ :=
    disk_threshold_of_certified_witness htu htu₁ hΨ hfu hur hrep'
  have hsu : Ico ts 1 = Ico tu 1 := hsSet.symm.trans huSet
  have hs : ts ∈ Ico tu 1 := hsu ▸ (show ts ∈ Ico ts 1 from ⟨le_rfl, hts₁⟩)
  have hu : tu ∈ Ico ts 1 := hsu.symm ▸ (show tu ∈ Ico tu 1 from ⟨le_rfl, htu₁⟩)
  have hEq : ts = tu := hu.1.antisymm hs.1
  subst tu
  obtain ⟨d, hpos, hd⟩ := candidate_positive_derivative hts hts₁ hΦ hfs hfr hrep
  obtain ⟨φ, hφ, hn, _, hz, _, hneg, hpositive⟩ :=
    exists_marked_competitor_lift hts hsSmall.le hfs hfr hd hpos
  obtain ⟨η, hη⟩ := exists_centered_comparisonChart hts hts₁
  have h₁ := (eq_parameter_and_lift_of_marked_competitor hts hts le_rfl hη hΦ
    hφ hn hz hneg hpositive).2
  have h₂ := (eq_parameter_and_lift_of_marked_competitor hts hts le_rfl hη hΨ
    hφ hn hz hneg hpositive).2
  have heq : EqOn Φ Ψ comparisonHalfDisk := h₁.symm.trans h₂
  refine ⟨rfl, heq, disk_eqOn_of_upper_halfDisk hfs hfu ?_⟩
  intro z hz
  have hz' : z ∈ comparisonHalfDisk := comparisonHalfDisk_eq_norm ▸ hz
  rw [← hrep z hz', ← hrep' z hz', heq hz']

end BelgianChocolate.HarmonicComparison

