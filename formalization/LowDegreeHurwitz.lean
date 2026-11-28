import Conjecture3

open Polynomial
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)

/-- The cubic Hurwitz sufficient condition, proved by evaluating at a putative root. -/
theorem stable_cubic (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hab : c < a*b) :
    StrictlyStable (X^3+C a*X^2+C b*X+C c) := by
  rw [strictStable_iff_no_roots]
  intro z hz hr
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C] at hr
  change z^3+(a:ℂ)*z^2+(b:ℂ)*z+(c:ℂ)=0 at hr
  let r := z.re
  let t := z.im
  have hr0 : 0 ≤ r := hz
  have hreal := congrArg Complex.re hr
  have himag := congrArg Complex.im hr
  simp [pow_succ, Complex.mul_re, Complex.mul_im] at hreal himag
  have hre : t^2*(a+3*r) = c+b*r+a*r^2+r^3 := by
    dsimp [r,t]
    linear_combination -hreal
  have him : t*(b+2*a*r+3*r^2-t^2) = 0 := by
    dsimp [r,t]
    linear_combination himag
  rcases mul_eq_zero.mp him with h | h
  · simp only [h,zero_pow (by decide : 2 ≠ 0),zero_mul] at hre
    exact (show 0 < c+b*r+a*r^2+r^3 by positivity).ne' hre.symm
  have hid : (a+3*r)*(b+2*a*r+3*r^2)-(c+b*r+a*r^2+r^3) =
      (a*b-c)+2*r*(a^2+b)+8*a*r^2+8*r^3 := by ring
  have h0 := sub_pos.mpr hab
  have hpos : 0 < (a*b-c)+2*r*(a^2+b)+8*a*r^2+8*r^3 := by positivity
  have hbr := sub_eq_zero.mp h
  rw [hbr,mul_comm (a+3*r),hre,sub_self] at hid
  linarith

/-- The quartic Hurwitz sufficient condition, using nonnegative real translates. -/
theorem stable_quartic (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hdet : 0 < a*b*c-c^2-a^2*d) :
    StrictlyStable (X^4+C a*X^3+C b*X^2+C c*X+C d) := by
  rw [strictStable_iff_no_roots]
  intro z hz hr
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C] at hr
  change z^4+(a:ℂ)*z^3+(b:ℂ)*z^2+(c:ℂ)*z+(d:ℂ)=0 at hr
  let r := z.re
  let t := z.im
  have hr0 : 0 ≤ r := hz
  let A := a+4*r
  let B := b+3*a*r+6*r^2
  let C₁ := c+2*b*r+3*a*r^2+4*r^3
  let D := d+c*r+b*r^2+a*r^3+r^4
  have hreal := congrArg Complex.re hr
  have himag := congrArg Complex.im hr
  simp [pow_succ, Complex.mul_re, Complex.mul_im] at hreal himag
  have hre : t^4-B*t^2+D = 0 := by
    dsimp [r,t,B,D]
    linear_combination hreal
  have him : t*(C₁-A*t^2) = 0 := by
    dsimp [r,t,C₁,A]
    linear_combination himag
  have hD : 0 < D := by dsimp [D]; positivity
  have hs : 0 < b^2-4*d := by
    have h := sq_nonneg (a*b-2*c)
    have hy : 0 < a^2*(b^2-4*d) := by nlinarith only [h,hdet]
    exact pos_of_mul_pos_right hy (sq_nonneg a)
  have hid : A*B*C₁-C₁^2-A^2*D =
      (a*b*c-c^2-a^2*d)+r*(2*a*(b^2-4*d)+2*a^2*c)+
      r^2*(8*a^2*b+4*(b^2-4*d)+4*a*c)+r^3*(8*a^3+32*a*b)+
      r^4*(48*a^2+32*b)+96*a*r^5+64*r^6 := by dsimp [A,B,C₁,D]; ring
  have hpos : 0 < A*B*C₁-C₁^2-A^2*D := by
    rw [hid]
    positivity
  rcases mul_eq_zero.mp him with h | h
  · simp [h,hD.ne'] at hre
  have hrel := sub_eq_zero.mp h
  rw [hrel] at hpos
  nlinarith only [hpos, show A*B*(A*t^2)-(A*t^2)^2-A^2*D = 0 by
    linear_combination -A^2*hre]

#print axioms stable_cubic
#print axioms stable_quartic
end BelgianChocolate.Conjectures

