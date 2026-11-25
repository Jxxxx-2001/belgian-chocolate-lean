import FirstAnnulusHomotopySupport
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Subpath
import Mathlib.Tactic

/-! Tailed circles in the scaled slit disk for the first annulus. -/

namespace BelgianChocolate.FirstAnnulusPaths

open Complex Metric Set unitInterval

/-- The scaled source disk, cut along the right real ray and punctured at 0 and -1. -/
def cutDomain (t : ℝ) : Set ℂ :=
  {s | ‖s‖ < 1 / t ∧ ¬(s.im = 0 ∧ 1 ≤ s.re ∧ s.re < 1 / t) ∧ s ≠ 0 ∧ s ≠ -1}

noncomputable def base (t : ℝ) : ℂ := -((1 / (2 * t) : ℝ) : ℂ) * Complex.I

noncomputable def foot (p : ℂ) : ℂ := p - ((1 / 5 : ℝ) : ℂ) * Complex.I

private theorem radius_ge_ten {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    10 ≤ 1 / t := (le_div_iff₀ ht).2 (by linarith)

private theorem base_im {t : ℝ} (ht : 0 < t) : (base t).im < 0 := by
  have hp : 0 < 1 / (2 * t) := one_div_pos.mpr (by positivity)
  simpa [base, Complex.mul_im] using (neg_lt_zero.mpr hp)

private theorem base_norm {t : ℝ} (ht : 0 < t) : ‖base t‖ < 1 / t := by
  have hp : 0 < 2 * t := by positivity
  simp only [base, norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
  rw [div_lt_div_iff₀ hp ht]
  linarith

theorem mem_cutDomain_of_im_ne_zero {t : ℝ} {s : ℂ} (hn : ‖s‖ < 1 / t)
    (hi : s.im ≠ 0) : s ∈ cutDomain t := by
  refine ⟨hn, fun h => hi h.1, ?_, ?_⟩
  · intro h
    exact hi (by rw [h, Complex.zero_im])
  · intro h
    exact hi (by rw [h, Complex.neg_im, Complex.one_im, neg_zero])

private theorem lower_mem {t : ℝ} {s : ℂ} (hn : ‖s‖ < 1 / t) (hi : s.im < 0) :
    s ∈ cutDomain t :=
  mem_cutDomain_of_im_ne_zero hn hi.ne

theorem base_mem {t : ℝ} (ht : 0 < t) : base t ∈ cutDomain t :=
  lower_mem (base_norm ht) (base_im ht)

private theorem center_properties {p : ℂ} (hp : p = 0 ∨ p = -1) :
    ‖p‖ ≤ 1 ∧ p.re ≤ 0 ∧ p.im = 0 := by
  rcases hp with rfl | rfl <;> norm_num

private theorem foot_norm {p : ℂ} (hp : p = 0 ∨ p = -1) : ‖foot p‖ ≤ 6 / 5 := by
  have hn : ‖((1 / 5 : ℝ) : ℂ) * Complex.I‖ = (1 / 5 : ℝ) := by norm_num [norm_mul]
  calc
    ‖foot p‖ ≤ ‖p‖ + ‖((1 / 5 : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ ≤ 6 / 5 := by linarith [(center_properties hp).1]

private theorem foot_im {p : ℂ} (hp : p = 0 ∨ p = -1) : (foot p).im < 0 := by
  norm_num [foot, Complex.mul_im, (center_properties hp).2.2]

theorem foot_mem {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : foot p ∈ cutDomain t :=
  lower_mem (by linarith [foot_norm hp, radius_ge_ten ht ht']) (foot_im hp)

/-- Every point of the affine tail is in the lower half of the scaled disk. -/
theorem tail_mem {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) (u : I) :
    AffineMap.lineMap (base t) (foot p) (u : ℝ) ∈ cutDomain t ∧
      (AffineMap.lineMap (base t) (foot p) (u : ℝ)).im < 0 := by
  have hn : AffineMap.lineMap (base t) (foot p) (u : ℝ) ∈ ball (0 : ℂ) (1 / t) :=
    (convex_ball _ _).lineMap_mem (mem_ball_zero_iff.mpr (base_norm ht))
      (mem_ball_zero_iff.mpr (by linarith [foot_norm hp, radius_ge_ten ht ht'])) u.property
  have hi : (AffineMap.lineMap (base t) (foot p) (u : ℝ)).im < 0 := by
    rw [AffineMap.lineMap_apply_module]
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    have h₀ := mul_nonpos_of_nonneg_of_nonpos u.property.1 (foot_im hp).le
    have h₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr u.property.2) (base_im ht).le
    rcases eq_or_lt_of_le u.property.2 with he | he
    · rw [he]
      simpa using foot_im hp
    · have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr he) (base_im ht)
      linarith
  exact ⟨lower_mem (mem_ball_zero_iff.mp hn) hi, hi⟩

/-- Both full radius-1/5 circles are contained in the scaled slit disk. -/
theorem circle_mem {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p s : ℂ}
    (hp : p = 0 ∨ p = -1) (hs : s ∈ sphere p (1 / 5)) : s ∈ cutDomain t := by
  have hd : ‖s - p‖ = (1 / 5 : ℝ) := by simpa only [mem_sphere, dist_eq_norm] using hs
  have hnorm : ‖s‖ ≤ 6 / 5 := by
    have hb := norm_add_le (s - p) p
    rw [sub_add_cancel, hd] at hb
    linarith [(center_properties hp).1]
  have hre : s.re < 1 := by
    have hb := Complex.re_le_norm (s - p)
    rw [Complex.sub_re, hd] at hb
    linarith [(center_properties hp).2.1]
  refine ⟨by linarith [radius_ge_ten ht ht'], fun h => (not_le_of_gt hre) h.2.1, ?_, ?_⟩
  · intro h
    rw [h] at hd
    rcases hp with rfl | rfl <;> norm_num at hd
  · intro h
    rw [h] at hd
    rcases hp with rfl | rfl <;> norm_num at hd

noncomputable def basepoint {t : ℝ} (ht : 0 < t) : cutDomain t :=
  ⟨base t, base_mem ht⟩

noncomputable def footpoint {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : cutDomain t :=
  ⟨foot p, foot_mem ht ht' hp⟩

noncomputable def tail {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : Path (basepoint ht) (footpoint ht ht' hp) where
  toFun u := ⟨AffineMap.lineMap (base t) (foot p) (u : ℝ), (tail_mem ht ht' hp u).1⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  source' := by apply Subtype.ext; simp [basepoint]
  target' := by apply Subtype.ext; simp [footpoint]

/-- One positively oriented turn, starting at the bottom of the circle. -/
noncomputable def round {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : Path (footpoint ht ht' hp) (footpoint ht ht' hp) where
  toFun u := ⟨circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * (u : ℝ)),
    circle_mem ht ht' hp (circleMap_mem_sphere p (by norm_num) _)⟩
  continuous_toFun := Continuous.subtype_mk (by unfold circleMap; fun_prop) _
  source' := by
    apply Subtype.ext
    change circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * 0) = foot p
    rw [mul_zero, add_zero, ← neg_div, circleMap_neg_pi_div_two]
    rfl
  target' := by
    apply Subtype.ext
    change circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * 1) = foot p
    rw [mul_one, periodic_circleMap, ← neg_div, circleMap_neg_pi_div_two]
    rfl

noncomputable def tailedCircle {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : Path (basepoint ht) (basepoint ht) :=
  ((tail ht ht' hp).trans (round ht ht' hp)).trans (tail ht ht' hp).symm

noncomputable def gammaZero {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (basepoint ht) (basepoint ht) :=
  tailedCircle ht ht' (Or.inl (rfl : (0 : ℂ) = 0))

noncomputable def gammaPlus {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (basepoint ht) (basepoint ht) :=
  tailedCircle ht ht' (Or.inr (rfl : (-1 : ℂ) = -1))

/-- Execute the marked loop about zero, then the marked loop about the upper puncture. -/
noncomputable def pairWord {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (basepoint ht) (basepoint ht) :=
  (gammaZero ht ht').trans (gammaPlus ht ht')

/-- The linear change of variable (s=iz/t) used in the first annulus. -/
noncomputable def scale (t : ℝ) (z : ℂ) : ℂ := Complex.I * z / (t : ℂ)

theorem scale_base (t : ℝ) : scale t (-1 / 2) = base t := by
  simp [scale, base, div_eq_mul_inv, mul_comm, mul_left_comm]

theorem scale_upper {t : ℝ} (ht : 0 < t) :
    scale t ((t : ℂ) * Complex.I) = -1 := by
  have ht₀ : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold scale
  rw [show Complex.I * ((t : ℂ) * Complex.I) = (t : ℂ) * (Complex.I * Complex.I) by ring,
    Complex.I_mul_I, mul_comm, mul_div_assoc, div_self ht₀, mul_one]

theorem scale_foot {t : ℝ} (ht : 0 < t) (p : ℂ) :
    scale t (p - ((t / 5 : ℝ) : ℂ)) = foot (scale t p) := by
  have ht₀ : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [scale, foot, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
  field_simp

theorem scale_lineMap (t : ℝ) (a b : ℂ) (u : ℝ) :
    scale t (AffineMap.lineMap a b u) = AffineMap.lineMap (scale t a) (scale t b) u := by
  simp only [scale, AffineMap.lineMap_apply_module, Complex.real_smul, Complex.ofReal_sub,
    Complex.ofReal_one, div_eq_mul_inv]
  ring

/-- Positive rotation in the source circle remains positive rotation after scaling. -/
theorem scale_circleMap {t : ℝ} (ht : 0 < t) (p : ℂ) (θ : ℝ) :
    scale t (circleMap p (t / 5) (Real.pi + θ)) =
      circleMap (scale t p) (1 / 5) (-(Real.pi / 2) + θ) := by
  have ht₀ : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hpi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have hpi2 : Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I) = -Complex.I := by
    rw [← neg_div]
    exact Complex.exp_neg_pi_div_two_mul_I
  simp only [scale, circleMap, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_one, add_mul, Complex.exp_add, hpi, hpi2]
  field_simp

/-- The open lower half of the disk provides a common convex region for both tails. -/
noncomputable def lowerDomain (t : ℝ) : Set ℂ :=
  ball 0 (1 / t) ∩ {z | z.im < 0}

theorem convex_lowerDomain (t : ℝ) : Convex ℝ (lowerDomain t) :=
  (convex_ball _ _).inter (convex_halfSpace_im_lt 0)

theorem lowerDomain_subset (t : ℝ) : lowerDomain t ⊆ cutDomain t :=
  fun _ hz => lower_mem (mem_ball_zero_iff.mp hz.1) hz.2

private theorem base_mem_lower {t : ℝ} (ht : 0 < t) : base t ∈ lowerDomain t :=
  ⟨mem_ball_zero_iff.mpr (base_norm ht), base_im ht⟩

private theorem foot_mem_lower {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : foot p ∈ lowerDomain t :=
  ⟨mem_ball_zero_iff.mpr (foot_mem ht ht' hp).1, foot_im hp⟩

/-- The shared branching point lies below the middle real gate at `-1/2`. -/
noncomputable def middle : ℂ := foot (-1 / 2)

private theorem middle_mem_lower {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    middle ∈ lowerDomain t := by
  have hn : ‖middle‖ ≤ 7 / 10 := by
    have h := norm_sub_le (-1 / 2 : ℂ) (((1 / 5 : ℝ) : ℂ) * Complex.I)
    norm_num [norm_div, norm_mul] at h
    simpa only [middle, foot, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, neg_div] using h
  refine ⟨mem_ball_zero_iff.mpr (by linarith [radius_ge_ten ht ht']), ?_⟩
  change middle.im < 0
  norm_num [middle, foot, Complex.mul_im, Complex.div_im, Complex.normSq_apply]

noncomputable def midpoint {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) : cutDomain t :=
  ⟨middle, lowerDomain_subset t (middle_mem_lower ht ht')⟩

private noncomputable def lowerSegment {t : ℝ} {a b : cutDomain t}
    (ha : (a : ℂ) ∈ lowerDomain t) (hb : (b : ℂ) ∈ lowerDomain t) : Path a b where
  toFun u := ⟨AffineMap.lineMap (a : ℂ) (b : ℂ) (u : ℝ),
    lowerDomain_subset t ((convex_lowerDomain t).lineMap_mem ha hb u.property)⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

private theorem lowerSegment_mem {t : ℝ} {a b : cutDomain t}
    (ha : (a : ℂ) ∈ lowerDomain t) (hb : (b : ℂ) ∈ lowerDomain t) (u : I) :
    (lowerSegment ha hb u : ℂ) ∈ lowerDomain t :=
  (convex_lowerDomain t).lineMap_mem ha hb u.property

noncomputable def commonTail {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (basepoint ht) (midpoint ht ht') :=
  lowerSegment (base_mem_lower ht) (middle_mem_lower ht ht')

noncomputable def branchTail {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : Path (midpoint ht ht') (footpoint ht ht' hp) :=
  lowerSegment (middle_mem_lower ht ht') (foot_mem_lower ht ht' hp)

/-- Replacing the direct tail by a broken line through the common branching point
preserves its relative homotopy class. -/
theorem tail_homotopic_common_branch {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {p : ℂ} (hp : p = 0 ∨ p = -1) :
    (tail ht ht' hp).Homotopic ((commonTail ht ht').trans (branchTail ht ht' hp)) := by
  apply FirstAnnulusHomotopySupport.homotopic_of_convex_range
    (convex_lowerDomain t) (lowerDomain_subset t)
  · intro u
    exact ⟨mem_ball_zero_iff.mpr (tail_mem ht ht' hp u).1.1, (tail_mem ht ht' hp u).2⟩
  · intro u
    have h : ((commonTail ht ht').trans (branchTail ht ht' hp)) u ∈
        range (commonTail ht ht') ∪ range (branchTail ht ht' hp) := by
      rw [← Path.trans_range]
      exact mem_range_self u
    rcases h with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [← hv]
      exact lowerSegment_mem (a := basepoint ht) (b := midpoint ht ht')
        (base_mem_lower ht) (middle_mem_lower ht ht') v
    · rw [← hv]
      exact lowerSegment_mem (a := midpoint ht ht') (b := footpoint ht ht' hp)
        (middle_mem_lower ht ht') (foot_mem_lower ht ht' hp) v

noncomputable def branchCircle {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : Path (midpoint ht ht') (midpoint ht ht') :=
  ((branchTail ht ht' hp).trans (round ht ht' hp)).trans (branchTail ht ht' hp).symm

noncomputable def branchWord {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (midpoint ht ht') (midpoint ht ht') :=
  (branchCircle ht ht' (Or.inl (rfl : (0 : ℂ) = 0))).trans
    (branchCircle ht ht' (Or.inr (rfl : (-1 : ℂ) = -1)))

open Path.Homotopic.Quotient in
theorem pairWord_homotopic_tailed_branchWord {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (pairWord ht ht').Homotopic (((commonTail ht ht').trans (branchWord ht ht')).trans
      (commonTail ht ht').symm) := by
  let h₀ : (0 : ℂ) = 0 ∨ (0 : ℂ) = -1 := Or.inl rfl
  let h₁ : (-1 : ℂ) = 0 ∨ (-1 : ℂ) = -1 := Or.inr rfl
  have hreplace (p : ℂ) (hp : p = 0 ∨ p = -1) :
      (tailedCircle ht ht' hp).Homotopic
        ((((commonTail ht ht').trans (branchTail ht ht' hp)).trans (round ht ht' hp)).trans
          ((commonTail ht ht').trans (branchTail ht ht' hp)).symm) := by
    have h := tail_homotopic_common_branch ht ht' hp
    exact (h.hcomp (Path.Homotopic.refl _)).hcomp h.symm₂
  apply ((hreplace 0 h₀).hcomp (hreplace (-1) h₁)).trans
  apply eq.mp
  simp only [branchWord, branchCircle, Path.trans_symm, mk_trans, mk_symm]
  simp only [← trans_assoc]
  rw [trans_assoc _ (mk (commonTail ht ht')).symm (mk (commonTail ht ht')), symm_trans, trans_refl]

/-- Coordinates in the small rectangle that joins the three real gates. -/
noncomputable def rectangularPoint (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

private theorem rectangularPoint_re (x y : ℝ) : (rectangularPoint x y).re = x := by
  simp [rectangularPoint, Complex.mul_re]

private theorem rectangularPoint_im (x y : ℝ) : (rectangularPoint x y).im = y := by
  simp [rectangularPoint, Complex.mul_im]

theorem rectangularPoint_mem {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {x y : ℝ}
    (hx : x ∈ Icc (-5 / 4) (1 / 4)) (hy : y ∈ Icc (-1 / 5) (1 / 5))
    (hpunctures : y ≠ 0 ∨ (x ≠ 0 ∧ x ≠ -1)) : rectangularPoint x y ∈ cutDomain t := by
  have hnx : |x| ≤ 5 / 4 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hny : |y| ≤ 1 / 5 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hn : ‖rectangularPoint x y‖ ≤ |x| + |y| := by
    simpa [rectangularPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      norm_add_le (x : ℂ) ((y : ℂ) * Complex.I)
  have hre : (rectangularPoint x y).re < 1 := by
    rw [rectangularPoint_re]
    linarith [hx.2]
  refine ⟨by linarith [radius_ge_ten ht ht'], fun h => (not_le_of_gt hre) h.2.1, ?_, ?_⟩
  · intro h
    have her := congrArg Complex.re h
    have hei := congrArg Complex.im h
    simp only [rectangularPoint_re, Complex.zero_re] at her
    simp only [rectangularPoint_im, Complex.zero_im] at hei
    exact hpunctures.elim (fun hh => hh hei) (fun hh => hh.1 her)
  · intro h
    have her := congrArg Complex.re h
    have hei := congrArg Complex.im h
    simp only [rectangularPoint_re, Complex.neg_re, Complex.one_re] at her
    simp only [rectangularPoint_im, Complex.neg_im, Complex.one_im, neg_zero] at hei
    exact hpunctures.elim (fun hh => hh hei) (fun hh => hh.2 her)

/-- The vertical segments through the right, middle, and left real gates. -/
theorem gate_mem {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {x y : ℝ}
    (hx : x = 1 / 4 ∨ x = -1 / 2 ∨ x = -5 / 4)
    (hy : y ∈ Icc (-1 / 5) (1 / 5)) : rectangularPoint x y ∈ cutDomain t := by
  refine rectangularPoint_mem ht ht' ?_ hy ?_
  · rcases hx with rfl | rfl | rfl <;> norm_num
  · right
    rcases hx with rfl | rfl | rfl <;> norm_num

noncomputable def gateEndpoint {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {x y : ℝ}
    (hx : x = 1 / 4 ∨ x = -1 / 2 ∨ x = -5 / 4)
    (hy : y ∈ Icc (-1 / 5) (1 / 5)) : cutDomain t :=
  ⟨rectangularPoint x y, gate_mem ht ht' hx hy⟩

noncomputable def gatePath {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {x : ℝ}
    (hx : x = 1 / 4 ∨ x = -1 / 2 ∨ x = -5 / 4) :
    Path (gateEndpoint ht ht' hx (y := -1 / 5) (by norm_num))
      (gateEndpoint ht ht' hx (y := 1 / 5) (by norm_num)) where
  toFun u := ⟨rectangularPoint x (-1 / 5 + (2 / 5) * (u : ℝ)),
    gate_mem ht ht' hx ⟨by linarith [u.property.1], by linarith [u.property.2]⟩⟩
  continuous_toFun := Continuous.subtype_mk (by unfold rectangularPoint; fun_prop) _
  source' := by apply Subtype.ext; change rectangularPoint x (-1 / 5 + (2 / 5) * 0) = _; norm_num [gateEndpoint]
  target' := by apply Subtype.ext; change rectangularPoint x (-1 / 5 + (2 / 5) * 1) = _; norm_num [gateEndpoint]

noncomputable def quarter : I := ⟨1 / 4, by norm_num⟩

noncomputable def threeQuarters : I := ⟨3 / 4, by norm_num⟩

theorem round_quarter {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : (round ht ht' hp quarter : ℂ) = p + (1 / 5 : ℂ) := by
  change circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * (1 / 4)) = _
  rw [show -(Real.pi / 2) + 2 * Real.pi * (1 / 4) = 0 by ring]
  simp [circleMap]

theorem round_threeQuarters {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : (round ht ht' hp threeQuarters : ℂ) = p - (1 / 5 : ℂ) := by
  change circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi * (3 / 4)) = _
  rw [show -(Real.pi / 2) + 2 * Real.pi * (3 / 4) = Real.pi by ring]
  simp [circleMap, Complex.exp_pi_mul_I, sub_eq_add_neg]

/-- Split the marked circle at its right and left real intercepts, in traversal order. -/
theorem round_subpaths {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) :
    (((round ht ht' hp).subpath 0 quarter).trans
      ((round ht ht' hp).subpath quarter threeQuarters) |>.trans
      ((round ht ht' hp).subpath threeQuarters 1)).Homotopic ((round ht ht' hp).subpath 0 1) :=
  ((Path.Homotopic.subpath_trans_subpath (round ht ht' hp) 0 quarter threeQuarters).hcomp
    (Path.Homotopic.refl _)).trans
    (Path.Homotopic.subpath_trans_subpath (round ht ht' hp) 0 threeQuarters 1)

private theorem circle_im {p : ℂ} (hp : p = 0 ∨ p = -1) (θ : ℝ) :
    (circleMap p (1 / 5) θ).im = (1 / 5) * Real.sin θ := by
  have h : circleMap p (1 / 5) θ = p + circleMap 0 (1 / 5) θ := by simp [circleMap]
  rw [h, Complex.add_im, (center_properties hp).2.2, zero_add, circleMap_zero_im]

theorem round_upper_subpath_im {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) (u : I) :
    (((round ht ht' hp).subpath quarter threeQuarters u : cutDomain t) : ℂ).im =
      (1 / 5) * Real.sin (Real.pi * (u : ℝ)) := by
  change (circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi *
    (Icc.convexComb quarter threeQuarters u : ℝ))).im = _
  rw [circle_im hp, Icc.coe_convexComb]
  change 1 / 5 * Real.sin (-(Real.pi / 2) + 2 * Real.pi *
    ((1 - (u : ℝ)) * (1 / 4) + (u : ℝ) * (3 / 4))) = _
  congr 2
  ring

theorem round_initial_subpath_im_nonpos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) (u : I) :
    (((round ht ht' hp).subpath 0 quarter u : cutDomain t) : ℂ).im ≤ 0 := by
  change (circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi *
    (Icc.convexComb 0 quarter u : ℝ))).im ≤ 0
  rw [circle_im hp, Icc.coe_convexComb]
  change 1 / 5 * Real.sin (-(Real.pi / 2) + 2 * Real.pi *
    ((1 - (u : ℝ)) * 0 + (u : ℝ) * (1 / 4))) ≤ 0
  apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
  apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
  · nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr u.property.2)]
  · nlinarith [mul_nonneg Real.pi_pos.le u.property.1, Real.pi_pos]

theorem round_final_subpath_im_nonpos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) (u : I) :
    (((round ht ht' hp).subpath threeQuarters 1 u : cutDomain t) : ℂ).im ≤ 0 := by
  change (circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi *
    (Icc.convexComb threeQuarters 1 u : ℝ))).im ≤ 0
  rw [circle_im hp, Icc.coe_convexComb]
  change 1 / 5 * Real.sin (-(Real.pi / 2) + 2 * Real.pi *
    ((1 - (u : ℝ)) * (3 / 4) + (u : ℝ) * 1)) ≤ 0
  apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
  rw [← Real.sin_sub_two_pi]
  apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
  · nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr u.property.2), Real.pi_pos]
  · nlinarith [mul_nonneg Real.pi_pos.le u.property.1]

/-- An affine real-axis link is admissible when its interval avoids both punctures. -/
noncomputable def realLink {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {a b : cutDomain t} (ha : (a : ℂ).im = 0) (hb : (b : ℂ).im = 0)
    (hbox : uIcc (a : ℂ).re (b : ℂ).re ⊆ Icc (-5 / 4) (1 / 4))
    (hpunctures : ∀ x ∈ uIcc (a : ℂ).re (b : ℂ).re, x ≠ 0 ∧ x ≠ -1) :
    Path a b where
  toFun u :=
    let x := AffineMap.lineMap (a : ℂ).re (b : ℂ).re (u : ℝ)
    have hx : x ∈ uIcc (a : ℂ).re (b : ℂ).re :=
      (convex_Icc _ _).lineMap_mem left_mem_uIcc right_mem_uIcc u.property
    ⟨rectangularPoint x 0, rectangularPoint_mem ht ht' (hbox hx) (by norm_num)
      (Or.inr (hpunctures _ hx))⟩
  continuous_toFun := Continuous.subtype_mk (by unfold rectangularPoint; fun_prop) _
  source' := by
    apply Subtype.ext
    change rectangularPoint (AffineMap.lineMap (a : ℂ).re (b : ℂ).re 0) 0 = (a : ℂ)
    rw [AffineMap.lineMap_apply_zero]
    apply Complex.ext
    · exact rectangularPoint_re _ _
    · rw [rectangularPoint_im, ha]
  target' := by
    apply Subtype.ext
    change rectangularPoint (AffineMap.lineMap (a : ℂ).re (b : ℂ).re 1) 0 = (b : ℂ)
    rw [AffineMap.lineMap_apply_one]
    apply Complex.ext
    · exact rectangularPoint_re _ _
    · rw [rectangularPoint_im, hb]

theorem realLink_im {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {a b : cutDomain t} (ha : (a : ℂ).im = 0) (hb : (b : ℂ).im = 0)
    (hbox : uIcc (a : ℂ).re (b : ℂ).re ⊆ Icc (-5 / 4) (1 / 4))
    (hpunctures : ∀ x ∈ uIcc (a : ℂ).re (b : ℂ).re, x ≠ 0 ∧ x ≠ -1) (u : I) :
    (realLink ht ht' ha hb hbox hpunctures u : ℂ).im = 0 :=
  rectangularPoint_im _ _

/-- The direct tail followed by the lower arc up to the right intercept. -/
noncomputable def rightApproach {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : Path (basepoint ht) (round ht ht' hp quarter) :=
  (tail ht ht' hp).trans (((round ht ht' hp).subpath 0 quarter).cast
    (round ht ht' hp).source.symm rfl)

/-- The direct tail followed by the reversed lower arc up to the left intercept. -/
noncomputable def leftApproach {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) : Path (basepoint ht) (round ht ht' hp threeQuarters) :=
  (tail ht ht' hp).trans (((round ht ht' hp).subpath threeQuarters 1).cast
    rfl (round ht ht' hp).target.symm).symm

theorem path_trans_property {X : Type*} [TopologicalSpace X] {a b c : X}
    {p : Path a b} {q : Path b c} {P : X → Prop}
    (hp : ∀ u, P (p u)) (hq : ∀ u, P (q u)) (u : I) : P ((p.trans q) u) := by
  have h : ((p.trans q) u) ∈ range p ∪ range q := by
    rw [← Path.trans_range]
    exact mem_range_self u
  rcases h with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact hv ▸ hp v
  · exact hv ▸ hq v

theorem rightApproach_im_nonpos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) (u : I) : (rightApproach ht ht' hp u : ℂ).im ≤ 0 := by
  apply path_trans_property (P := fun z : cutDomain t => (z : ℂ).im ≤ 0)
  · intro v
    exact (tail_mem ht ht' hp v).2.le
  · exact round_initial_subpath_im_nonpos ht ht' hp

theorem leftApproach_im_nonpos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) (u : I) : (leftApproach ht ht' hp u : ℂ).im ≤ 0 := by
  apply path_trans_property (P := fun z : cutDomain t => (z : ℂ).im ≤ 0)
  · intro v
    exact (tail_mem ht ht' hp v).2.le
  · intro v
    exact round_final_subpath_im_nonpos ht ht' hp (unitInterval.symm v)

open Path.Homotopic.Quotient in
/-- The marked loop is the right approach, the upper semicircle, and the reversed left approach. -/
theorem tailedCircle_homotopic_approaches {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) :
    (tailedCircle ht ht' hp).Homotopic
      (((rightApproach ht ht' hp).trans ((round ht ht' hp).subpath quarter threeQuarters)).trans
        (leftApproach ht ht' hp).symm) := by
  let rou := round ht ht' hp
  let ini := (rou.subpath 0 quarter).cast rou.source.symm rfl
  let top := rou.subpath quarter threeQuarters
  let fin := (rou.subpath threeQuarters 1).cast rfl rou.target.symm
  have h : ((ini.trans top).trans fin).Homotopic rou := by
    have hsub := (round_subpaths ht ht' hp).pathCast rou.source.symm rou.target.symm
    rw [Path.subpath_zero_one] at hsub
    convert hsub using 1 <;> exact Path.ext (by rfl)
  have h' := ((Path.Homotopic.refl (tail ht ht' hp)).hcomp h.symm).hcomp
    (Path.Homotopic.refl (tail ht ht' hp).symm)
  apply h'.trans
  apply eq.mp
  simp only [rightApproach, leftApproach, Path.trans_symm, Path.symm_symm, mk_trans,
    ← trans_assoc, ini, top, fin, rou]

private theorem middleLink_range {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    uIcc ((round ht ht' (p := 0) (Or.inl rfl) threeQuarters : cutDomain t) : ℂ).re
      ((round ht ht' (p := -1) (Or.inr rfl) quarter : cutDomain t) : ℂ).re =
    Icc (-4 / 5 : ℝ) (-1 / 5) := by
  rw [round_threeQuarters, round_quarter]
  have h₀ : ((0 : ℂ) - 1 / 5).re = (-1 / 5 : ℝ) := by
    norm_num [Complex.div_re, Complex.normSq_apply]
  have h₁ : ((-1 : ℂ) + 1 / 5).re = (-4 / 5 : ℝ) := by
    norm_num [Complex.div_re, Complex.normSq_apply]
  rw [h₀, h₁, uIcc_of_ge (by norm_num)]

/-- The real link between the left intercept of the zero circle and the right
intercept of the minus-one circle stays between the two punctures. -/
noncomputable def middleLink {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (round ht ht' (p := 0) (Or.inl rfl) threeQuarters)
      (round ht ht' (p := -1) (Or.inr rfl) quarter) :=
  realLink ht ht'
    (by rw [round_threeQuarters]; norm_num [Complex.div_im, Complex.normSq_apply])
    (by rw [round_quarter]; norm_num [Complex.div_im, Complex.normSq_apply])
    (by rw [middleLink_range ht ht']; exact Icc_subset_Icc (by norm_num) (by norm_num))
    (by
      intro x hx
      rw [middleLink_range ht ht'] at hx
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)

noncomputable def upperBridge {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    Path (round ht ht' (p := 0) (Or.inl rfl) quarter)
      (round ht ht' (p := -1) (Or.inr rfl) threeQuarters) :=
  (((round ht ht' (p := 0) (Or.inl rfl)).subpath quarter threeQuarters).trans
    (middleLink ht ht')).trans
    ((round ht ht' (p := -1) (Or.inr rfl)).subpath quarter threeQuarters)

theorem upperBridge_im_nonneg {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) (u : I) :
    0 ≤ (upperBridge ht ht' u : ℂ).im := by
  have hround {p : ℂ} (hp : p = 0 ∨ p = -1) (v : I) :
      0 ≤ (((round ht ht' hp).subpath quarter threeQuarters v : cutDomain t) : ℂ).im := by
    rw [round_upper_subpath_im]
    exact mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi
      (mul_nonneg Real.pi_pos.le v.property.1)
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left v.property.2 Real.pi_pos.le))
  apply path_trans_property (P := fun z : cutDomain t => 0 ≤ (z : ℂ).im)
  · intro v
    apply path_trans_property (P := fun z : cutDomain t => 0 ≤ (z : ℂ).im) (hround (Or.inl (rfl : (0 : ℂ) = 0))) ?_ v
    intro w
    have hzero : (middleLink ht ht' w : ℂ).im = 0 := by
      unfold middleLink
      exact realLink_im ht ht' _ _ _ _ w
    rw [hzero]
  · exact hround (Or.inr rfl)

theorem middleApproach_im_nonpos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) (u : I) :
    ((((leftApproach ht ht' (p := 0) (Or.inl rfl)).symm.trans
      (rightApproach ht ht' (p := -1) (Or.inr rfl))) u : cutDomain t) : ℂ).im ≤ 0 := by
  exact path_trans_property (P := fun z : cutDomain t => (z : ℂ).im ≤ 0)
    (fun v => leftApproach_im_nonpos ht ht' (Or.inl (rfl : (0 : ℂ) = 0)) (unitInterval.symm v))
    (fun v => rightApproach_im_nonpos ht ht' (Or.inr (rfl : (-1 : ℂ) = -1)) v) u

open Path.Homotopic.Quotient in
/-- Replacing the middle lower connection by the real link leaves the two upper
semicircles in execution order, with only the outer approaches remaining. -/
theorem pairWord_homotopic_upperBridge_of_middle {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    (hmiddle : ((leftApproach ht ht' (p := 0) (Or.inl rfl)).symm.trans
      (rightApproach ht ht' (p := -1) (Or.inr rfl))).Homotopic (middleLink ht ht')) :
    (pairWord ht ht').Homotopic
      (((rightApproach ht ht' (p := 0) (Or.inl rfl)).trans (upperBridge ht ht')).trans
        (leftApproach ht ht' (p := -1) (Or.inr rfl)).symm) := by
  have h₀ := tailedCircle_homotopic_approaches ht ht' (Or.inl (rfl : (0 : ℂ) = 0))
  have h₁ := tailedCircle_homotopic_approaches ht ht' (Or.inr (rfl : (-1 : ℂ) = -1))
  apply (h₀.hcomp h₁).trans
  apply eq.mp
  have hm := eq.mpr hmiddle
  simp only [mk_trans, mk_symm] at hm
  simp only [upperBridge, mk_trans, mk_symm, ← trans_assoc]
  rw [trans_assoc _ (mk (leftApproach ht ht' (p := 0) (Or.inl rfl))).symm
    (mk (rightApproach ht ht' (p := -1) (Or.inr rfl))), hm]

private theorem initial_strict {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) {u : I} (hu : u ≠ 1) :
    (((round ht ht' hp).subpath 0 quarter u : cutDomain t) : ℂ).im < 0 := by
  have hlt : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (fun h => hu (Subtype.ext h))
  change (circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi *
    (Icc.convexComb 0 quarter u : ℝ))).im < 0
  rw [circle_im hp, Icc.coe_convexComb]
  change 1 / 5 * Real.sin (-(Real.pi / 2) + 2 * Real.pi *
    ((1 - (u : ℝ)) * 0 + (u : ℝ) * (1 / 4))) < 0
  apply mul_neg_of_pos_of_neg (by norm_num)
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hlt)]
  · nlinarith [mul_nonneg Real.pi_pos.le u.property.1, Real.pi_pos]

private theorem final_strict {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) {u : I} (hu : u ≠ 0) :
    (((round ht ht' hp).subpath threeQuarters 1 u : cutDomain t) : ℂ).im < 0 := by
  have hlt : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (fun h => hu (Subtype.ext h.symm))
  change (circleMap p (1 / 5) (-(Real.pi / 2) + 2 * Real.pi *
    (Icc.convexComb threeQuarters 1 u : ℝ))).im < 0
  rw [circle_im hp, Icc.coe_convexComb]
  change 1 / 5 * Real.sin (-(Real.pi / 2) + 2 * Real.pi *
    ((1 - (u : ℝ)) * (3 / 4) + (u : ℝ) * 1)) < 0
  apply mul_neg_of_pos_of_neg (by norm_num)
  rw [← Real.sin_sub_two_pi]
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr u.property.2), Real.pi_pos]
  · nlinarith [mul_pos Real.pi_pos hlt]

private theorem right_strict {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) {u : I} (hu : u ≠ 1) :
    (rightApproach ht ht' hp u : ℂ).im < 0 := by
  unfold rightApproach
  rw [Path.trans_apply]
  split
  · exact (tail_mem ht ht' hp _).2
  · apply initial_strict ht ht' hp
    intro he
    apply hu
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    change 2 * (u : ℝ) - 1 = 1 at hv
    change (u : ℝ) = 1
    linarith

private theorem left_strict {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) {p : ℂ}
    (hp : p = 0 ∨ p = -1) {u : I} (hu : u ≠ 1) :
    (leftApproach ht ht' hp u : ℂ).im < 0 := by
  unfold leftApproach
  rw [Path.trans_apply]
  split
  · exact (tail_mem ht ht' hp _).2
  next h =>
    let v : I := ⟨2 * (u : ℝ) - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, u.property.2⟩⟩
    refine final_strict ht ht' hp (u := unitInterval.symm v) ?_
    intro he
    apply hu
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    change 1 - (2 * (u : ℝ) - 1) = 0 at hv
    change (u : ℝ) = 1
    linarith

private theorem middle_strict {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    {u : I} (h₀ : u ≠ 0) (h₁ : u ≠ 1) :
    ((((leftApproach ht ht' (p := 0) (Or.inl rfl)).symm.trans
      (rightApproach ht ht' (p := -1) (Or.inr rfl))) u : cutDomain t) : ℂ).im < 0 := by
  rw [Path.trans_apply]
  split
  · apply left_strict ht ht' (Or.inl rfl)
    intro he
    apply h₀
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    change 1 - 2 * (u : ℝ) = 1 at hv
    change (u : ℝ) = 0
    linarith
  · apply right_strict ht ht' (Or.inr rfl)
    intro he
    apply h₁
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    change 2 * (u : ℝ) - 1 = 1 at hv
    change (u : ℝ) = 1
    linarith

theorem middleApproach_homotopic_middleLink {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    ((leftApproach ht ht' (p := 0) (Or.inl rfl)).symm.trans
      (rightApproach ht ht' (p := -1) (Or.inr rfl))).Homotopic (middleLink ht ht') := by
  apply Path.Homotopic.symm
  apply FirstAnnulusHomotopySupport.homotopic_of_weak_strict_linear_side (Ω := cutDomain t)
    (convex_ball (0 : ℂ) (1 / t)) (fun _ hz => mem_ball_zero_iff.mpr hz.1)
    (-Complex.imCLM.toLinearMap)
  · intro z hz hz'
    have him : z.im < 0 := by simpa using hz'
    exact lower_mem (mem_ball_zero_iff.mp hz) him
  · intro u _ _
    have hzero : (middleLink ht ht' u : ℂ).im = 0 := by
      unfold middleLink
      exact realLink_im ht ht' _ _ _ _ u
    simpa using (show 0 ≤ -(middleLink ht ht' u : ℂ).im by rw [hzero, neg_zero])
  · intro u hu₀ hu₁
    simpa using neg_pos.mpr (middle_strict ht ht' hu₀ hu₁)

theorem pairWord_homotopic_upperBridge {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10) :
    (pairWord ht ht').Homotopic
      (((rightApproach ht ht' (p := 0) (Or.inl rfl)).trans (upperBridge ht ht')).trans
        (leftApproach ht ht' (p := -1) (Or.inr rfl)).symm) :=
  pairWord_homotopic_upperBridge_of_middle ht ht' (middleApproach_homotopic_middleLink ht ht')

end BelgianChocolate.FirstAnnulusPaths
