import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Exact integer arithmetic for the finite-order Belgian Chocolate witness.
Coefficient lists are in increasing powers. -/

namespace BelgianChocolate.ControlWitness

/-- Dense addition, with the shorter coefficient list extended by zeros. -/
def addCoeffs : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a::as, b::bs => (a+b)::addCoeffs as bs

def scaleCoeffs (c : ℤ) (a : List ℤ) : List ℤ := a.map (c * ·)

def linMul (c d : ℤ) (a : List ℤ) : List ℤ :=
  addCoeffs (scaleCoeffs c a) (0 :: scaleCoeffs d a)

/-- Homogeneous evaluation at the linear forms `F=f₀+f₁z`, `G=g₀+g₁z`.
The components store `G^(length-1) p(F/G)` and `G^length`. -/
def homogeneous (f₀ f₁ g₀ g₁ : ℤ) : List ℤ → List ℤ × List ℤ
  | [] => ([],[1])
  | x::xs =>
    let r := homogeneous f₀ f₁ g₀ g₁ xs
    (addCoeffs (scaleCoeffs x r.2) (linMul f₀ f₁ r.1), linMul g₀ g₁ r.2)

def billion : ℤ := 1000000000

/-- Clears the positive denominator in the Cayley transform after the exact `10⁻⁹` shift. -/
def shiftedCayley (a : List ℤ) : List ℤ :=
  (homogeneous (-(billion+1)) (billion-1) billion billion a).1

def deltaNum : ℤ := 98236947
def deltaDen : ℤ := 100000000

/-- Integer numerator of `(s²-2δs+1)x+(s²-1)y` at the joint scale `deltaDen * denominator`. -/
def closedLoopNums (x y : List ℤ) : List ℤ :=
  addCoeffs (scaleCoeffs deltaDen (addCoeffs x (scaleCoeffs (-1) y)))
    (0 :: addCoeffs (scaleCoeffs (-(2*deltaNum)) x) (0 :: scaleCoeffs deltaDen (addCoeffs x y)))

/-- The primitive Schur row `(L a[j] - h a[n-j])/g`, after its zero constant is removed. -/
def schurNumerator (a : List ℤ) : List ℤ :=
  let L := a.getLastD 0
  let h := a.headD 0
  (List.zipWith (fun u v => L*u - h*v) a a.reverse).tail

/-- Calculate proposed integer normalizations. Their validity is independently checked by `verifiedSchur`. -/
def schurScales : Nat → List ℤ → List ℤ
  | 0, _ => []
  | n+1, a =>
    let r := schurNumerator a
    let d : ℤ := (r.foldl (fun (k : ℕ) v => Nat.gcd k v.natAbs) 0 : ℕ)
    d :: schurScales n (r.map (fun v => v/d))

/-- A certificate supplies positive integer scalings for the primitive reductions. Each
step checks both the forward and reversed coefficient identity exactly. -/
def verifiedSchur : List ℤ → List ℤ → Bool
  | [], a => decide (a.length = 1 ∧ a.headD 0 ≠ 0)
  | d::ds, a =>
      let L := a.getLastD 0
      let h := a.headD 0
      let b := (schurNumerator a).map (fun v => v/d)
      decide (a.length = ds.length+2 ∧ h^2 < L^2 ∧ d ≠ 0 ∧
        addCoeffs (scaleCoeffs L a) (scaleCoeffs (-h) a.reverse) = 0 :: scaleCoeffs d b ∧
        addCoeffs (scaleCoeffs L a.reverse) (scaleCoeffs (-h) a) = scaleCoeffs d b.reverse ++ [0]) &&
        verifiedSchur ds b


def evalRat : List ℤ → ℚ → ℚ
  | [], _ => 0
  | a::as, z => (a:ℚ) + z * evalRat as z

end BelgianChocolate.ControlWitness

