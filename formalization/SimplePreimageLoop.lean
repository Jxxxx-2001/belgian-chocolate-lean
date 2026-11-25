import TranslatedCircleHomotopy
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic

namespace BelgianChocolate

open Set Filter Metric Topology unitInterval

/-- Near a simple preimage, the image of a sufficiently small source circle
deforms to the positively oriented complex-linear circle about its value.
The deformation avoids both the center and a specified second puncture. -/
theorem simplePreimage_circleHomotopy {f : ℂ → ℂ} {p d b : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hcont : ContinuousOn f (ball p ε))
    (hder : HasDerivAt f d p) (hd : d ≠ 0) (hb : b ≠ f p) :
    ∃ δ > 0, ∀ r ∈ Ioo (0 : ℝ) δ,
      ∃ F G : C(Circle, ({f p, b}ᶜ : Set ℂ)),
        (∀ u : Circle, (F u : ℂ) = f (p + (r : ℂ) * (u : ℂ))) ∧
        (∀ u : Circle, (G u : ℂ) = f p + ((r : ℂ) * (u : ℂ)) * d) ∧
        Nonempty (F.Homotopy G) := by
  let a := f p
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hbpos : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.mp
    (hder.isLittleO.bound (half_pos hdpos))
  let δ := min ε (min η (‖b - a‖ / (2 * (‖d‖ + 1))))
  have hδ : 0 < δ := lt_min hε (lt_min hη (by positivity))
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  have hrε : r < ε := hr.2.trans_le (min_le_left ..)
  have hrη : r < η := hr.2.trans_le ((min_le_right ..).trans (min_le_left ..))
  have hrB : r < ‖b - a‖ / (2 * (‖d‖ + 1)) :=
    hr.2.trans_le ((min_le_right ..).trans (min_le_right ..))
  have hbig : r * (2 * (‖d‖ + 1)) < ‖b - a‖ :=
    (lt_div_iff₀ (by positivity)).mp hrB
  let z (u : Circle) := p + (r : ℂ) * (u : ℂ)
  let g (u : Circle) := a + ((r : ℂ) * (u : ℂ)) * d
  have hzn (u : Circle) : ‖z u - p‖ = r := by
    simp [z, abs_of_pos hr.1]
  have hgn (u : Circle) : ‖g u - a‖ = r * ‖d‖ := by
    simp [g, abs_of_pos hr.1]
  have herr (u : Circle) : ‖f (z u) - g u‖ ≤ (‖d‖ / 2) * r := by
    have hz : dist (z u) p < η := by rw [dist_eq_norm, hzn]; exact hrη
    have h := hηb hz
    change ‖f (z u) - f p - (z u - p) • d‖ ≤ ‖d‖ / 2 * ‖z u - p‖ at h
    rw [hzn] at h
    have he : f (z u) - g u = f (z u) - f p - (z u - p) • d := by
      simp only [z, g, a, add_sub_cancel_left, smul_eq_mul]
      ring
    simpa only [← he] using h
  have hgb (u : Circle) : g u ∈ ball a ‖b - a‖ := by
    rw [mem_ball, dist_eq_norm, hgn]
    nlinarith [mul_pos hr.1 hdpos]
  have hfb (u : Circle) : f (z u) ∈ ball a ‖b - a‖ := by
    rw [mem_ball, dist_eq_norm, ← sub_add_sub_cancel (f (z u)) (g u) a]
    have h := norm_add_le (f (z u) - g u) (g u - a)
    rw [hgn] at h
    nlinarith [herr u, mul_pos hr.1 hdpos]
  let L (s : unitInterval) (u : Circle) :=
    (1 - (s : ℝ)) • f (z u) + (s : ℝ) • g u
  have hmem (s : unitInterval) (u : Circle) : L s u ∈ ({a,b}ᶜ : Set ℂ) := by
    have hnorm : ‖L s u - g u‖ ≤ (‖d‖ / 2) * r := by
      have he : L s u - g u = (1 - (s : ℝ)) • (f (z u) - g u) := by
        simp only [L, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr s.property.2)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [s.property.1])).trans (herr u)
    have hna : L s u ≠ a := by
      intro he
      rw [he, norm_sub_rev, hgn] at hnorm
      nlinarith [mul_pos hr.1 hdpos]
    have hball : L s u ∈ ball a ‖b - a‖ :=
      (convex_ball a ‖b - a‖) (hfb u) (hgb u) (sub_nonneg.mpr s.property.2)
        s.property.1 (by ring)
    have hnb : L s u ≠ b := by
      intro he
      rw [he, mem_ball, dist_eq_norm] at hball
      exact (lt_irrefl _) hball
    simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using ⟨hna, hnb⟩
  have hcZ : Continuous z := by unfold z; fun_prop
  have hcF : Continuous (f ∘ z) :=
    hcont.comp_continuous hcZ (fun u ↦ by rw [mem_ball, dist_eq_norm, hzn]; exact hrε)
  have hcG : Continuous g := by unfold g; fun_prop
  have hFmem (u : Circle) : f (z u) ∈ ({a,b}ᶜ : Set ℂ) := by
    simpa [L] using hmem 0 u
  have hGmem (u : Circle) : g u ∈ ({a,b}ᶜ : Set ℂ) := by
    simpa [L] using hmem 1 u
  let F : C(Circle, ({a,b}ᶜ : Set ℂ)) :=
    ⟨fun u ↦ ⟨f (z u), hFmem u⟩, hcF.subtype_mk _⟩
  let G : C(Circle, ({a,b}ᶜ : Set ℂ)) :=
    ⟨fun u ↦ ⟨g u, hGmem u⟩, hcG.subtype_mk _⟩
  refine ⟨F, G, fun _ ↦ rfl, fun _ ↦ rfl, ⟨{
    toFun := fun su ↦ ⟨L su.1 su.2, hmem su.1 su.2⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
  }⟩⟩
  · apply Continuous.subtype_mk
    change Continuous (fun su : unitInterval × Circle ↦
      (1 - (su.1 : ℝ)) • (f ∘ z) su.2 + (su.1 : ℝ) • g su.2)
    have ht : Continuous (fun su : unitInterval × Circle ↦ (su.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).smul (hcF.comp continuous_snd)).add
      (ht.smul (hcG.comp continuous_snd))
  · intro u
    apply Subtype.ext
    simp [L, F]
  · intro u
    apply Subtype.ext
    simp [L, G]

/-- The small image circle can be straightened to any prescribed positively
oriented circle of admissible radius around the same puncture. -/
theorem simplePreimage_circleHomotopy_to_circle
    {f : ℂ → ℂ} {p d b c : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hcont : ContinuousOn f (ball p ε))
    (hder : HasDerivAt f d p) (hd : d ≠ 0)
    (hc : c ≠ 0) (hcB : ‖c‖ < ‖b - f p‖) :
    ∃ δ > 0, ∀ r ∈ Ioo (0 : ℝ) δ,
      ∃ F : C(Circle, ({f p, b}ᶜ : Set ℂ)),
        (∀ u : Circle, (F u : ℂ) = f (p + (r : ℂ) * (u : ℂ))) ∧
        Nonempty (F.Homotopy (translatedCircle hc hcB)) := by
  have hn : 0 < ‖b - f p‖ := (norm_nonneg c).trans_lt hcB
  have hb : b ≠ f p := sub_ne_zero.mp (norm_pos_iff.mp hn)
  obtain ⟨δ₀, hδ₀, h⟩ := simplePreimage_circleHomotopy hε hcont hder hd hb
  let δ := min δ₀ (‖b - f p‖ / ‖d‖)
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  refine ⟨δ, lt_min hδ₀ (div_pos hn hdpos), ?_⟩
  intro r hr
  obtain ⟨F, G, hF, hG, ⟨H⟩⟩ :=
    h r ⟨hr.1, hr.2.trans_le (min_le_left ..)⟩
  have hr' : r < ‖b - f p‖ / ‖d‖ := hr.2.trans_le (min_le_right ..)
  have hk : (r : ℂ) * d ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.1.ne') hd
  have hkB : ‖(r : ℂ) * d‖ < ‖b - f p‖ := by
    simpa [abs_of_pos hr.1] using (lt_div_iff₀ hdpos).mp hr'
  have he : G = translatedCircle hk hkB := by
    ext u
    change (G u : ℂ) = f p + ((r : ℂ) * d) * (u : ℂ)
    rw [hG]
    ring
  rw [he] at H
  obtain ⟨K⟩ := translatedCircle_homotopy hk hc hkB hcB
  exact ⟨F, hF, ⟨H.trans K⟩⟩


end BelgianChocolate

