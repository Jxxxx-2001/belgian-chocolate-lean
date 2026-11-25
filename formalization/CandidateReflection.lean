import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
import SourceDiskRealNormalization

/-! Reflection and cusp filling for a candidate first given on the upper half-disk.
The hypotheses are one-sided analytic and boundary data, not an assumed disk extension.
-/
namespace BelgianChocolate.CandidateReflection
open Complex Filter Metric Set Topology
open scoped ComplexConjugate

noncomputable def fillReflection (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (TauCeti.schwarzReflection f) 0 0

theorem fillReflection_zero (f : ℂ → ℂ) : fillReflection f 0 = 0 := by
  simp [fillReflection]

theorem fillReflection_upper {f : ℂ → ℂ} {z : ℂ} (hz : 0 < z.im) :
    fillReflection f z = f z := by
  have hn : z ≠ 0 := by intro h; simp [h] at hz
  simp [fillReflection, hn, TauCeti.schwarzReflection_of_im_nonneg hz.le]

theorem fillReflection_axis {f : ℂ → ℂ} {z : ℂ} (hz : z.im = 0) (hn : z ≠ 0) :
    fillReflection f z = f z := by
  simp [fillReflection, hn, TauCeti.schwarzReflection_of_im_zero hz]

/-- A one-sided zero limit at the cusp suffices to fill the reflected function.
Continuity at zero on the real diameter is a conclusion, not an extra hypothesis. -/
theorem fillReflection_differentiableOn {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn f ((ball 0 r \ {0}) ∩ {z : ℂ | 0 ≤ z.im}))
    (hd : DifferentiableOn ℂ f (ball 0 r ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ ball (0 : ℂ) r \ {0}, z.im = 0 → (f z).im = 0)
    (hlim : Tendsto f (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝 0)) :
    DifferentiableOn ℂ (fillReflection f) (ball 0 r) := by
  let Ω : Set ℂ := ball 0 r \ {0}
  have ho : IsOpen Ω := isOpen_ball.sdiff isClosed_singleton
  have hs : MapsTo conj Ω Ω := by
    intro z hz
    exact ⟨by simpa only [mem_ball_zero_iff, norm_conj] using hz.1,
      by simpa only [mem_compl_iff, mem_singleton_iff, map_eq_zero] using hz.2⟩
  have hD : DifferentiableOn ℂ (TauCeti.schwarzReflection f) Ω :=
    TauCeti.differentiableOn_schwarzReflection_of_symmetric ho hs hc
      (hd.mono (fun _ h => ⟨h.1.1, h.2⟩)) hreal
  have hL : Tendsto (TauCeti.schwarzReflection f)
      (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (TauCeti.schwarzReflection_of_im_nonneg hz.le).symm
  have hL' := TauCeti.tendsto_nhdsNE_of_tendsto_nhdsWithin_im_pos hr hD
    (fun z hz => TauCeti.schwarzReflection_conj_of_real_on_axis hreal hz) hL
  have hF : ContinuousAt (fillReflection f) 0 := by
    rw [fillReflection, continuousAt_update_same]
    exact hL'
  apply (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (ball_mem_nhds 0 hr)).mp
  refine ⟨?_, hF⟩
  apply hD.congr
  intro z hz
  exact Function.update_of_ne hz.2 _ _

theorem fillReflection_conj {f : ℂ → ℂ} {r : ℝ}
    (hreal : ∀ z ∈ ball (0 : ℂ) r \ {0}, z.im = 0 → (f z).im = 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    fillReflection f (conj z) = conj (fillReflection f z) := by
  by_cases hn : z = 0
  · simp [hn, fillReflection_zero]
  have hnc : conj z ≠ 0 := by simpa using hn
  simp only [fillReflection, Function.update_of_ne hn, Function.update_of_ne hnc]
  exact TauCeti.schwarzReflection_conj_of_real_on_axis hreal ⟨hz, hn⟩

theorem fillReflection_hasDerivAt_upper {f : ℂ → ℂ} {z d : ℂ}
    (hz : 0 < z.im) (hd : HasDerivAt f d z) :
    HasDerivAt (fillReflection f) d z := by
  apply hd.congr_of_eventuallyEq
  have he : ∀ᶠ w : ℂ in 𝓝 z, 0 < w.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  filter_upwards [he] with w hw
  exact fillReflection_upper hw

theorem fillReflection_hasDerivAt_lower {f : ℂ → ℂ} {z d : ℂ}
    (hz : z.im < 0) (hd : HasDerivAt f d (conj z)) :
    HasDerivAt (fillReflection f) (conj d) z := by
  apply (TauCeti.hasDerivAt_schwarzReflection_of_im_neg hz hd).congr_of_eventuallyEq
  have he : ∀ᶠ w : ℂ in 𝓝 z, w.im < 0 :=
    (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz
  filter_upwards [he] with w hw
  have hn : w ≠ 0 := by intro h; simp [h] at hw
  exact Function.update_of_ne hn _ _

open BelgianChocolate.SourceDiskPaths

/-- All puncture exclusions and the two simple one-points transport through
reflection. The only multiplicity not supplied from the open upper half-disk
is the zero at the cusp, stated separately as `hzero`. -/
theorem fillReflection_marked_of_simple_zero {f : ℂ → ℂ} {t : ℝ} (ht : 0 < t)
    (hdisk : DifferentiableOn ℂ (fillReflection f) (ball 0 1))
    (hreal : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, z.im = 0 → (f z).im = 0)
    (havoid : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ z.im → z ≠ 0 →
      z ≠ (t : ℂ) * I → f z ∈ ({0,1}ᶜ : Set ℂ))
    (hplus : f ((t : ℂ) * I) = 1)
    (hplusSimple : ∃ d, HasDerivAt f d ((t : ℂ) * I) ∧ d ≠ 0)
    (hzero : ∃ d, HasDerivAt (fillReflection f) d 0 ∧ d ≠ 0) :
    MarkedCompetitor t (fillReflection f) ∧ RealSymmetricOnDisk (fillReflection f) := by
  have hp : 0 < ((t : ℂ) * I).im := by simpa using ht
  have hm : ((-(t : ℂ)) * I).im < 0 := by simpa using neg_neg_of_pos ht
  have hconj : conj ((-(t : ℂ)) * I) = (t : ℂ) * I := by simp
  have hn : ((-(t : ℂ)) * I) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr ht.ne')) I_ne_zero
  refine ⟨⟨hdisk, ?_, fillReflection_zero f, ?_, ?_, hzero, ?_, ?_⟩,
    fun z hz => fillReflection_conj hreal hz⟩
  · intro z hz
    have hzball : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz.1
    by_cases hi : 0 ≤ z.im
    · have he : fillReflection f z = f z := by
        simp [fillReflection, Function.update_of_ne hz.2.1,
          TauCeti.schwarzReflection_of_im_nonneg hi]
      rw [he]
      exact havoid z hzball hi hz.2.1 hz.2.2.1
    · have hic : 0 ≤ (conj z).im := by simp only [conj_im]; linarith
      have hzc : conj z ∈ ball (0 : ℂ) 1 := by
        simpa only [mem_ball_zero_iff, norm_conj] using hzball
      have hzc0 : conj z ≠ 0 := by simpa using hz.2.1
      have hzcp : conj z ≠ (t : ℂ) * I := by
        intro he
        apply hz.2.2.2
        have he' := congrArg conj he
        simpa using he'
      have ha := havoid (conj z) hzc hic hzc0 hzcp
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at ha ⊢
      have he : fillReflection f z = conj (f (conj z)) := by
        simp [fillReflection, hz.2.1, TauCeti.schwarzReflection_of_im_neg (lt_of_not_ge hi)]
      rw [he]
      constructor
      · simpa using ha.1
      · intro hh
        apply ha.2
        have hh' := congrArg conj hh
        simpa using hh'
  · rw [fillReflection_upper hp, hplus]
  · simp only [fillReflection, Function.update_of_ne hn,
      TauCeti.schwarzReflection_of_im_neg hm, hconj, hplus, map_one]
  · obtain ⟨d, hd, hne⟩ := hplusSimple
    exact ⟨d, fillReflection_hasDerivAt_upper hp hd, hne⟩
  · obtain ⟨d, hd, hne⟩ := hplusSimple
    exact ⟨conj d, fillReflection_hasDerivAt_lower hm (hconj.symm ▸ hd), by simpa using hne⟩

end BelgianChocolate.CandidateReflection
