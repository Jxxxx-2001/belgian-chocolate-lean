import SecondAnnulusEmbedding
import SecondAnnulusReference
import FirstAnnulusTransport

/-! Deform the actual center ellipse to the positive reference circle within the three-puncture disk. -/

namespace BelgianChocolate.SecondAnnulus

open Complex Set Metric
open BelgianChocolate.SourceDiskPaths
open BelgianChocolate.FirstAnnulus (positiveCircleLoop normalizedCore)
open BelgianChocolate.SecondAnnulusTopology (referenceCircle referenceLoop)

private noncomputable def rotatedDirection (s : unitInterval) (ζ : Circle) : ℂ :=
  Complex.exp (((((1-(s:ℝ))*Real.pi : ℝ) : ℂ))*Complex.I) * (ζ:ℂ)

private theorem continuous_rotatedDirection :
    Continuous (fun v : unitInterval × Circle => rotatedDirection v.1 v.2) := by
  unfold rotatedDirection
  fun_prop

private theorem norm_rotatedDirection (s : unitInterval) (ζ : Circle) :
    ‖rotatedDirection s ζ‖ = 1 := by
  simp [rotatedDirection,Complex.norm_exp,Complex.mul_re]

private theorem rotatedDirection_zero (ζ : Circle) : rotatedDirection 0 ζ = -(ζ:ℂ) := by
  simp [rotatedDirection]

private theorem rotatedDirection_one (ζ : Circle) : rotatedDirection 1 ζ = (ζ:ℂ) := by
  simp [rotatedDirection]

/-- Coefficients of the unit direction and its inverse in the intermediate ellipses. -/
private noncomputable def firstCoeff (s : unitInterval) : ℝ :=
  (1-(s:ℝ))*(Real.sqrt 19/2) + (s:ℝ)*(6/5)
private noncomputable def secondCoeff (s : unitInterval) : ℝ :=
  (1-(s:ℝ))*((Real.sqrt 19)⁻¹/2)

private theorem coeff_bounds (s : unitInterval) :
    0 ≤ firstCoeff s ∧ 0 ≤ secondCoeff s ∧
    1 < firstCoeff s - secondCoeff s ∧ firstCoeff s + secondCoeff s < 10 := by
  have hr₀ : 4 < Real.sqrt 19 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hr₁ : Real.sqrt 19 < 5 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hi₀ : 0 < (Real.sqrt 19)⁻¹ := by positivity
  have hi₁ : (Real.sqrt 19)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hs := s.property.1
  have hs' := sub_nonneg.mpr s.property.2
  refine ⟨?_,?_,?_,?_⟩
  · unfold firstCoeff
    positivity
  · unfold secondCoeff
    positivity
  · have h := (convex_Ioi (1:ℝ)) (show (Real.sqrt 19 - (Real.sqrt 19)⁻¹)/2 ∈ Ioi 1 by
        rw [Set.mem_Ioi]; linarith) (show (6/5:ℝ) ∈ Ioi 1 by norm_num) hs' hs (by ring)
    change 1 < (1-(s:ℝ))*((Real.sqrt 19 - (Real.sqrt 19)⁻¹)/2) + (s:ℝ)*(6/5) at h
    unfold firstCoeff secondCoeff
    linarith
  · have h := (convex_Iio (10:ℝ)) (show (Real.sqrt 19 + (Real.sqrt 19)⁻¹)/2 ∈ Iio 10 by
        rw [Set.mem_Iio]; linarith) (show (6/5:ℝ) ∈ Iio 10 by norm_num) hs' hs (by ring)
    change (1-(s:ℝ))*((Real.sqrt 19 + (Real.sqrt 19)⁻¹)/2) + (s:ℝ)*(6/5) < 10 at h
    unfold firstCoeff secondCoeff
    linarith

private noncomputable def ellipseBlend (s : unitInterval) (ζ : Circle) : ℂ :=
  (firstCoeff s:ℂ) * rotatedDirection s ζ + (secondCoeff s:ℂ) * (rotatedDirection s ζ)⁻¹

private theorem ellipseBlend_mem {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    (s : unitInterval) (ζ : Circle) : ellipseBlend s ζ ∈ scaledDisk t := by
  obtain ⟨hc,hd,hdiff,hsum⟩ := coeff_bounds s
  have h₁ : ‖(firstCoeff s:ℂ) * rotatedDirection s ζ‖ = firstCoeff s := by
    simp [norm_rotatedDirection,abs_of_nonneg hc]
  have h₂ : ‖(secondCoeff s:ℂ) * (rotatedDirection s ζ)⁻¹‖ = secondCoeff s := by
    simp [norm_rotatedDirection,abs_of_nonneg hd]
  have hu := norm_add_le ((firstCoeff s:ℂ) * rotatedDirection s ζ)
    ((secondCoeff s:ℂ) * (rotatedDirection s ζ)⁻¹)
  rw [← ellipseBlend,h₁,h₂] at hu
  have hl := norm_sub_le (ellipseBlend s ζ) ((secondCoeff s:ℂ) * (rotatedDirection s ζ)⁻¹)
  rw [show ellipseBlend s ζ - (secondCoeff s:ℂ) * (rotatedDirection s ζ)⁻¹ =
      (firstCoeff s:ℂ) * rotatedDirection s ζ from add_sub_cancel_right _ _,h₁,h₂] at hl
  have hlow : 1 < ‖ellipseBlend s ζ‖ := by linarith
  have hrad : 10 ≤ 1/t := (le_div_iff₀ ht).mpr (by linarith)
  refine ⟨by linarith,?_,?_,?_⟩ <;> intro he <;> rw [he] at hlow <;> norm_num at hlow

private theorem ellipseBlend_continuous :
    Continuous (fun v : unitInterval × Circle => ellipseBlend v.1 v.2) := by
  have hc : Continuous (fun v : unitInterval × Circle => (firstCoeff v.1:ℂ)) := by
    unfold firstCoeff; fun_prop
  have hd : Continuous (fun v : unitInterval × Circle => (secondCoeff v.1:ℂ)) := by
    unfold secondCoeff; fun_prop
  have hne (v : unitInterval × Circle) : rotatedDirection v.1 v.2 ≠ 0 := by
    intro he
    have h := norm_rotatedDirection v.1 v.2
    simp [he] at h
  exact (hc.mul continuous_rotatedDirection).add (hd.mul (continuous_rotatedDirection.inv₀ hne))

private theorem ellipseBlend_zero (ζ : Circle) :
    ellipseBlend 0 ζ = normalizedEmbedding (centerParameter ζ) := by
  simp [ellipseBlend,rotatedDirection_zero,firstCoeff,secondCoeff,normalizedEmbedding,
    FirstAnnulus.joukowski,centerParameter,mul_inv_rev]
  ring

private theorem ellipseBlend_one (ζ : Circle) :
    ellipseBlend 1 ζ = (6/5:ℂ)*(ζ:ℂ) := by
  simp [ellipseBlend,rotatedDirection_one,firstCoeff,secondCoeff]

/-- Rotate away the sign from `s=i z/t`, keeping positive orientation, and deform the center
ellipse to the circle of radius `6/5`. All intermediate loops avoid all three punctures. -/
noncomputable def stripCenterToReference {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    (stripCenterCircle ht ht').Homotopy (referenceCircle ht ht') where
  toFun v := ⟨ellipseBlend v.1 v.2,ellipseBlend_mem ht ht' v.1 v.2⟩
  continuous_toFun := ellipseBlend_continuous.subtype_mk _
  map_zero_left ζ := Subtype.ext (ellipseBlend_zero ζ)
  map_one_left ζ := Subtype.ext (ellipseBlend_one ζ)

/-- Based transport of the true center around the reference circle, with its tail recorded. -/
theorem reference_tailed_stripCenter {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10) :
    let γ := positiveCircleLoop.map (stripCenterCircle ht ht').continuous
    ∃ q : Path (referenceCircle ht ht' 1) (stripCenterCircle ht ht' 1),
      ((q.trans γ).trans q.symm).Homotopic (referenceLoop ht ht') := by
  let H := (stripCenterToReference ht ht').symm
  exact ⟨H.evalAt 1, FirstAnnulusTransport.free_homotopy_tailed_homotopy H positiveCircleLoop⟩

/-- Pull any based word identification for the positive reference circle back to the
actual strip center. The two explicitly oriented tails are composed in traversal order. -/
theorem stripCenter_word_of_reference_word {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/10)
    {b : scaledDisk t} (word : Path b b)
    (hword : ∃ r : Path b (referenceCircle ht ht' 1),
      ((r.trans (referenceLoop ht ht')).trans r.symm).Homotopic word) :
    ∃ q : Path b (stripCenterCircle ht ht' 1),
      ((q.trans (positiveCircleLoop.map (stripCenterCircle ht ht').continuous)).trans q.symm).Homotopic word := by
  obtain ⟨r,hr⟩ := hword
  obtain ⟨q,hq⟩ := reference_tailed_stripCenter ht ht'
  refine ⟨r.trans q, ?_⟩
  apply Path.Homotopic.Quotient.eq.mp
  rw [← Path.Homotopic.Quotient.eq.mpr hr]
  have h := Path.Homotopic.Quotient.eq.mpr hq
  simp only [Path.trans_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc] at h ⊢
  rw [← h]
  simp only [Path.Homotopic.Quotient.trans_assoc]

end BelgianChocolate.SecondAnnulus

