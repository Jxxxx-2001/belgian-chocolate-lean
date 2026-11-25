import FirstAnnulusMarkedCircleHomotopy
import SimplePreimageLoop
import FirstAnnulusCoreWord

namespace BelgianChocolate.FirstAnnulusPaths

open Complex Metric Set Topology
open BelgianChocolate (translatedCircle simplePreimage_circleHomotopy_to_circle)

/-- The actual marked circle in the cut source domain goes around its simple
image puncture positively. The marked radius and its initial phase are built
into the statement. -/
theorem markedCircle_image_homotopy
    {t ε : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} {p d b c : ℂ} (hp : p = 0 ∨ p = -1)
    (hε : 0 < ε) (hcont : ContinuousOn f (ball p ε))
    (hder : HasDerivAt f d p) (hd : d ≠ 0)
    (F : C(cutDomain t, ({f p, b}ᶜ : Set ℂ)))
    (hF : ∀ z : cutDomain t, (F z : ℂ) = f (z : ℂ))
    (hc : c ≠ 0) (hcB : ‖c‖ < ‖b - f p‖) :
    Nonempty ((F.comp (smallMarkedCircle ht ht' hp
      (by norm_num : (0 : ℝ) < 1 / 5) le_rfl)).Homotopy
        (translatedCircle hc hcB)) := by
  let rot : C(Circle, Circle) :=
    ⟨fun u ↦ Circle.exp (-(Real.pi / 2)) * u, continuous_const.mul continuous_id⟩
  have hrot (u : Circle) : (rot u : ℂ) = -Complex.I * (u : ℂ) := by
    change ((Circle.exp (-(Real.pi / 2)) * u : Circle) : ℂ) = _
    rw [Circle.coe_mul, Circle.coe_exp, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_ofNat, ← neg_div, Complex.exp_neg_pi_div_two_mul_I]
  have hci : c * Complex.I ≠ 0 := mul_ne_zero hc Complex.I_ne_zero
  have hciB : ‖c * Complex.I‖ < ‖b - f p‖ := by simpa using hcB
  obtain ⟨δ, hδ, hlocal⟩ :=
    simplePreimage_circleHomotopy_to_circle hε hcont hder hd hci hciB
  let r := min δ (1 / 5 : ℝ) / 2
  have hmin : 0 < min δ (1 / 5 : ℝ) := lt_min hδ (by norm_num)
  have hr : 0 < r := half_pos hmin
  have hrδ : r < δ :=
    (half_lt_self hmin).trans_le (min_le_left _ _)
  have hr₁ : r ≤ 1 / 5 :=
    (half_le_self hmin.le).trans (min_le_right _ _)
  obtain ⟨G, hG, ⟨H⟩⟩ := hlocal r ⟨hr, hrδ⟩
  let small := smallMarkedCircle ht ht' hp hr hr₁
  have hstart : F.comp small = G.comp rot := by
    ext u
    change (F (small u) : ℂ) = (G (rot u) : ℂ)
    rw [hF, hG, hrot]
    rfl
  have hend : (translatedCircle hci hciB).comp rot = translatedCircle hc hcB := by
    ext u
    change f p + (c * Complex.I) * (rot u : ℂ) = f p + c * (u : ℂ)
    rw [hrot]
    have he : (c * Complex.I) * (-Complex.I * (u : ℂ)) =
        -(c * (u : ℂ)) * (Complex.I * Complex.I) := by ring
    rw [he, Complex.I_mul_I]
    ring
  have H' := H.compContinuousMap rot
  rw [← hstart, hend] at H'
  exact ⟨((ContinuousMap.Homotopy.refl F).comp (shrinkMarkedCircle ht ht' hp hr hr₁)).trans H'⟩

/-- After a suitable tail is chosen in the target, the image of the actual
based marked loop is relatively homotopic to the prescribed positive circle. -/
theorem tailedCircle_image_homotopy
    {t ε : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {f : ℂ → ℂ} {p d b c : ℂ} (hp : p = 0 ∨ p = -1)
    (hε : 0 < ε) (hcont : ContinuousOn f (ball p ε))
    (hder : HasDerivAt f d p) (hd : d ≠ 0)
    (F : C(cutDomain t, ({f p, b}ᶜ : Set ℂ)))
    (hF : ∀ z : cutDomain t, (F z : ℂ) = f (z : ℂ))
    (hc : c ≠ 0) (hcB : ‖c‖ < ‖b - f p‖) :
    let G := translatedCircle hc hcB
    ∃ q : Path (F (basepoint ht)) (G 1),
      ((tailedCircle ht ht' hp).map F.continuous).Homotopic
        ((q.trans (BelgianChocolate.FirstAnnulus.positiveCircleLoop.map G.continuous)).trans
          q.symm) := by
  let S := smallMarkedCircle ht ht' hp (by norm_num : (0 : ℝ) < 1 / 5) le_rfl
  let G := translatedCircle hc hcB
  let γ := BelgianChocolate.FirstAnnulus.positiveCircleLoop
  obtain ⟨H⟩ := markedCircle_image_homotopy ht ht' hp hε hcont hder hd F hF hc hcB
  let r := H.evalAt (1 : Circle)
  let Q := (tail ht ht' hp).map F.continuous
  let C := γ.map (F.comp S).continuous
  have hb : footpoint ht ht' hp = S 1 :=
    ((round ht ht' hp).source.symm.trans (round_eq_smallMarkedCircle_positiveLoop ht ht' hp 0)).trans
      (congrArg S γ.source)
  have hbf : F (footpoint ht ht' hp) = (F.comp S) 1 := congrArg F hb
  let q := Q.cast rfl hbf.symm
  have hloop : (round ht ht' hp).map F.continuous = C.cast hbf hbf := by
    ext u
    change (F (round ht ht' hp u) : ℂ) = (F (S (γ u)) : ℂ)
    rw [round_eq_smallMarkedCircle_positiveLoop]
  have hword : (tailedCircle ht ht' hp).map F.continuous = (q.trans C).trans q.symm := by
    rw [tailedCircle, Path.map_trans, Path.map_trans, ← Path.map_symm, hloop]
    exact (BelgianChocolate.FirstAnnulus.cast_tailed_loop Q C hbf).symm
  let L := γ.map G.continuous
  have hcore : ((r.trans L).trans r.symm).Homotopic C :=
    BelgianChocolate.FirstAnnulusTransport.free_homotopy_tailed_homotopy H γ
  refine ⟨q.trans r, ?_⟩
  rw [hword]
  apply Path.Homotopic.Quotient.eq.mp
  have h := Path.Homotopic.Quotient.eq.mpr hcore
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] at h
  simp only [Path.trans_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    ← h, Path.Homotopic.Quotient.trans_assoc]
  rfl

end BelgianChocolate.FirstAnnulusPaths
