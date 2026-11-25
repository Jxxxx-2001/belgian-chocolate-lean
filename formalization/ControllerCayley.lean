import ControllerSchur

namespace BelgianChocolate.ControlWitness

open Complex

theorem evalRat_cast (a : List ℤ) (z : ℚ) :
    ((evalRat a z:ℚ):ℂ) = evalCoeffs a (z:ℂ) := by
  induction a with
  | nil => simp [evalRat,evalCoeffs]
  | cons c as ih => simp [evalRat,evalCoeffs,ih]

/-- Algebraic meaning of the cleared homogeneous transform. -/
theorem eval_homogeneous (f₀ f₁ g₀ g₁ : ℤ) (a : List ℤ) (z : ℂ)
    (hG : (g₀:ℂ)+(g₁:ℂ)*z ≠ 0) :
    let F := (f₀:ℂ)+(f₁:ℂ)*z
    let G := (g₀:ℂ)+(g₁:ℂ)*z
    let r := homogeneous f₀ f₁ g₀ g₁ a
    evalCoeffs r.2 z = G^a.length ∧
      evalCoeffs r.1 z * G = G^a.length * evalCoeffs a (F/G) := by
  dsimp only
  let F := (f₀:ℂ)+(f₁:ℂ)*z
  let G := (g₀:ℂ)+(g₁:ℂ)*z
  induction a with
  | nil => simp [homogeneous,evalCoeffs]
  | cons c cs ih =>
    obtain ⟨hg,hp⟩ := ih
    simp only [homogeneous,eval_linMul,eval_addCoeffs,eval_scaleCoeffs,List.length_cons,evalCoeffs]
    rw [hg, pow_succ]
    constructor
    · ring
    · change ((c:ℂ) * G^cs.length + F * evalCoeffs (homogeneous f₀ f₁ g₀ g₁ cs).1 z) * G =
        G^cs.length * G * ((c:ℂ) + F/G * evalCoeffs cs (F/G))
      change evalCoeffs (homogeneous f₀ f₁ g₀ g₁ cs).1 z * G =
        G^cs.length * evalCoeffs cs (F/G) at hp
      calc
        _ = (c:ℂ)*G^cs.length*G + F*(evalCoeffs (homogeneous f₀ f₁ g₀ g₁ cs).1 z*G) := by ring
        _ = _ := by rw [hp]; field_simp [show G ≠ 0 from hG]

private theorem cayley_norm_ge_one {q : ℂ} (hq : 0 ≤ q.re) (hd : 1-q ≠ 0) :
    1 ≤ ‖(1+q)/(1-q)‖ := by
  have hs : ‖(1:ℂ)-q‖^2 ≤ ‖(1:ℂ)+q‖^2 := by
    rw [Complex.sq_norm,Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.sub_im,Complex.add_im,
      Complex.one_re, Complex.one_im,zero_add,zero_sub]
    nlinarith
  rw [norm_div,le_div_iff₀ (norm_pos_iff.mpr hd),one_mul]
  nlinarith [norm_nonneg ((1:ℂ)-q), norm_nonneg ((1:ℂ)+q)]

/-- The certified shifted polynomial has no root in the closed half-plane
`Re s ≥ -10⁻⁹`. The prospective point mapping to infinity is checked separately. -/
theorem closed_halfPlane_nonzero (a : List ℤ) (ds : List ℤ)
    (hc : verifiedSchur ds (shiftedCayley a) = true)
    (hexception : evalRat a (((billion:ℚ)-1)/billion) ≠ 0)
    {s : ℂ} (hs : -(1/1000000000:ℝ) ≤ s.re) : evalCoeffs a s ≠ 0 := by
  let q : ℂ := s + 1/1000000000
  have hq : 0 ≤ q.re := by
    dsimp [q]
    norm_num
    linarith
  by_cases hsing : q = 1
  · have he : s = ((((billion:ℚ)-1)/billion:ℚ):ℂ) := by
      dsimp [q] at hsing
      norm_num [billion]
      linear_combination hsing
    rw [he, ← evalRat_cast]
    exact_mod_cast hexception
  have hd : 1-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hsing)
  let w := (1+q)/(1-q)
  have hw : 1 ≤ ‖w‖ := cayley_norm_ge_one hq hd
  let G : ℂ := (billion:ℂ)+(billion:ℂ)*w
  let F : ℂ := ((-(billion+1):ℤ):ℂ)+((billion-1:ℤ):ℂ)*w
  have hGval : G = (2*(billion:ℂ))/(1-q) := by
    dsimp [G,w]
    field_simp [hd]
    ring
  have hG : G ≠ 0 := hGval ▸ div_ne_zero (by norm_num [billion]) hd
  have hF : F/G = s := by
    apply (div_eq_iff hG).mpr
    dsimp [F,G,w]
    push_cast
    field_simp [hd]
    dsimp [q,billion]
    ring
  have he := (eval_homogeneous (-(billion+1)) (billion-1) billion billion a w hG).2
  change evalCoeffs (shiftedCayley a) w * G = G^a.length * evalCoeffs a (F/G) at he
  rw [hF] at he
  intro hroot
  rw [hroot,mul_zero] at he
  exact (verifiedSchur_sound _ _ hc _ hw).1 ((mul_eq_zero.mp he).resolve_right hG)

end BelgianChocolate.ControlWitness

