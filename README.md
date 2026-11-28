# The Exact Stabilizability Threshold for the Belgian Chocolate Problem

**Xiang Ji**, **Long Wang**, and **Wensheng Yu**

Xiang Ji and Wensheng Yu · School of Electronic Engineering, Beijing University of Posts and Telecommunications  
Long Wang · Center for Systems and Control, College of Engineering, Peking University

English · [中文](README.zh-CN.md)

Project affiliation: Intelligent Information Processing Laboratory, Beijing University of Posts and Telecommunications (北京邮电大学 智能信息处理实验室).

**Initial Lean formalization commit: 2026-11-25 · [4006bec](https://github.com/Jxxxx-2001/belgian-chocolate-lean/commit/4006bec3e7f41c605a9bcd07d28d90fc4261b292).**

**Content updated: 2026-11-28.**

This repository accompanies the manuscript and contains Lean 4 proofs of the exact threshold and the two fixed-degree results, together with a rational controller certificate.

[Lean main theorem](formalization/BelgianChocolateThreshold.lean#L89) · [Axiom audit](formalization/BelgianChocolateThresholdAudit.lean) · [Reproduction instructions](formalization/REPRODUCE.md)

## The problem

In the polynomial formulation of Blondel's simultaneous stabilization problem, fix 0 &lt; δ &lt; 1. Seek nonzero real polynomials x, y with deg y ≤ deg x such that x, y, and

<p align="center">Z(s) = (s² − 2δs + 1)x(s) + (s² − 1)y(s)</p>

are strictly Hurwitz stable, meaning that each zero has strictly negative real part. The finite-order controller is y/x. [Lean definition](formalization/ControllerFeasible.lean#L11)

## Main results

| Result | Statement | Lean |
| --- | --- | --- |
| Finite-order stabilization | The feasible parameters are exactly (0, δ<sub>∗</sub>). The supremum δ<sub>∗</sub> is unattained. | [Interval and endpoint](formalization/BelgianChocolateThreshold.lean#L38) |
| Disk interpolation | The feasible parameters are exactly [t<sub>∗</sub>, 1). At t = t<sub>∗</sub> there are exactly two interpolants, f<sub>∗</sub>(z) and f<sub>∗</sub>(−z), with f<sub>∗</sub>′(0) &gt; 0. | [Interval and endpoint classification](formalization/MarkedCompetitorComparison.lean#L236) |
| Exact threshold formula | Let d<sub>∗</sub> be the harmonic measure at 0 of the lower unit semicircle in the unique balanced slit domain. Then t<sub>∗</sub> = tan(πd<sub>∗</sub>/4) and δ<sub>∗</sub> = cos(πd<sub>∗</sub>/2) = (1 − t<sub>∗</sub>²)/(1 + t<sub>∗</sub>²). | [Balanced slit](formalization/BalancedSlitRoot.lean#L101) · [Exact formulas](formalization/BelgianChocolateThreshold.lean#L32) |
| Example 6.1 — Sixth-order counterexample | With a degree-six denominator and a constant numerator, every feasible parameter is below √(11/12). With a degree-six numerator and denominator, some parameter above 0.96295 is feasible. | [Refutation](formalization/Conjecture2.lean#L377) · [Strict gap](formalization/Conjecture2.lean#L363) |
| Theorem 6.2 — Sharpness of the continued-fraction bound | For a constant numerator and denominator degree n ≥ 1, let δ<sub>n</sub><sup>∗</sup> be the feasible supremum. Every feasible parameter is strictly below δ<sub>n</sub> = cos(π/[2(n + 1)]). The supremum equals this bound for n = 1, 2, 3, 4 and is strictly smaller for n ≥ 5. | [Continued-fraction bound](formalization/ContinuedFractionBound.lean#L73) · [Equality classification](formalization/Conjecture3Equality.lean#L8) |

For δ in [0, 1], the manuscript also includes δ = 0, giving the feasible set [0, δ<sub>∗</sub>). A controller at zero is given by x(s) = s + 1 and y(s) = 1/2. The linked Lean threshold theorem uses positive parameters.

The numerical approximation δ<sub>∗</sub> ≈ 0.987237027 comes from Muhan Liu's evaluation of the harmonic measure and balance equation (preprint, Section 6). [Liu's preprint](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf)

## Research background

- **1994.** Vincent Blondel posed the problem in the study of simultaneous stabilization. The polynomial formulation asks when a stable, minimum-phase rational controller can stabilize a particular second-order plant. [Blondel’s monograph, pp. 149–150](https://link.springer.com/book/10.1007/3-540-19862-8)
- **2008.** Guannan He, Long Wang, and Wensheng Yu used automated inequality proving to obtain explicit parameter bounds for fixed-order stabilizing controllers and formulated two conjectures for the Belgian Chocolate Problem. [IFAC paper](https://doi.org/10.3182/20080706-5-KR-1001.00191)
- **2011.** Qiang Guan, Guannan He, Long Wang, and Wensheng Yu reviewed the Belgian Chocolate Problem from the perspectives of theoretical bounds and controller design. Section 5 describes how a single threshold separates feasible and infeasible parameters. [*Control Theory & Applications* 28(1), 1–12](https://www.oalib.com/journal/3455/11)
- **2013.** Walter Bergweiler and Alexandre Eremenko formulated the associated holomorphic interpolation problem on the unit disk and proved the upper bound δ<sub>∗</sub> &lt; 0.999579. [*Gol’dberg’s Constants*, §11](https://www.math.purdue.edu/~eremenko/dvi/goldbergconst.pdf)
- **2014.** Wang Li and Wensheng Yu used elliptic modular functions and lengths of hyperbolic closed geodesics to refine a parameter estimate based on the Hempel–Smith bound. [CCDC paper](https://doi.org/10.1109/CCDC.2014.6852192)
- **2016.** Wang Li, Long Wang, and Wensheng Yu surveyed analytical and numerical bounds for the Belgian Chocolate Problem, including bounds for fixed controller orders. [*Journal of Systems Science & Complexity* 29(2), 289–299](https://doi.org/10.1007/s11424-015-4182-1)
- **2018.** Zachary Charles and Nigel Boston proved that δ = 0.9808348 is feasible using the algebraic structure of the stabilization equations. [Charles and Boston, Theorem 5.1](https://arxiv.org/abs/1708.08114)
- **2026.** Xuandi Cheng gave an exact polynomial certificate for feasibility at δ = 0.9846316110433085. Muhan Liu derived the same exact threshold as the accompanying manuscript using a modular covering and a Cauchy integral argument. [Cheng’s certificate](https://github.com/chengxuandi/belgian-chocolate-certified-lower-bound/tree/362cf25a04ebd0468b05153008ba72dca7f09ef6) · [Liu’s preprint](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf)

## Proof outline

### Theorem 1.1 — Stabilizability threshold

For a slit tip α, let a(α), b₀(α), and d(α) be the harmonic measures at 0 of the curved arc C, the two slit banks combined, and the lower semicircle L, respectively. The theorem gives a unique balanced tip α<sub>∗</sub> ∈ (−1, 0) and the formula

<p align="center">a(α<sub>∗</sub>) = b₀(α<sub>∗</sub>), &emsp; d<sub>∗</sub> = d(α<sub>∗</sub>), &emsp; δ<sub>∗</sub> = cos(πd<sub>∗</sub>/2).</p>

The feasible positive parameters are exactly (0, δ<sub>∗</sub>). For parameters in [0, 1], the feasible set is [0, δ<sub>∗</sub>). Thus δ<sub>∗</sub> is the supremum over all finite controller orders and cannot be attained by any finite-order controller.

The two harmonic measures a and b₀ vary continuously and strictly in opposite directions as the slit grows. Their difference changes sign, giving the unique balance. The Cayley transform relates controller feasibility to the disk problem in Theorem 2.1. Polynomial approximation gives controllers below the threshold, and the boundary behavior of the extremal interpolant rules out finite-order attainment. [Lean threshold theorem for positive parameters](formalization/BelgianChocolateThreshold.lean#L89)

### Theorem 2.1 — Disk threshold and uniqueness

For 0 &lt; t &lt; 1, a disk interpolant at t is holomorphic on the unit disk and commutes with complex conjugation. Its preimages of 0 and 1 are prescribed by

<p align="center">f⁻¹({0}) = {0}, &emsp; f⁻¹({1}) = {it, −it},</p>

and all three preimages are simple. With the same d<sub>∗</sub> as in Theorem 1.1, the change of parameters is

<p align="center">t<sub>∗</sub> = tan(πd<sub>∗</sub>/4), &emsp; δ = (1 − t²)/(1 + t²).</p>

The feasible disk parameters are exactly [t<sub>∗</sub>, 1). At t = t<sub>∗</sub> there are exactly two interpolants, f<sub>∗</sub>(z) and f<sub>∗</sub>(−z), with f<sub>∗</sub>′(0) &gt; 0.

The balanced slit gives the candidate f<sub>∗</sub>. Two explicit annuli determine the boundary markings of competing lifts. Comparing harmonic primitives excludes smaller t and proves uniqueness with the positive-derivative normalization. A certified degree-28 controller at δ<sub>w</sub> = 98236947/10⁸ gives t<sub>∗</sub> ≤ t<sub>w</sub> &lt; 1/10, so the comparison covers every positive parameter up to t<sub>∗</sub>. [Lean disk comparison](formalization/MarkedCompetitorComparison.lean#L236) · [Schur verification of the witness](verification/README.md)

<p align="center"><img src="assets/balanced-slit.png" width="660" alt="The upper half-disk maps to a domain bounded by the curved arc C and the lower semicircle L, with a slit from −1 to α∗. The marked point it∗ maps to 0."></p>

**Figure 1.** The two halves of the diameter and the upper semicircle map to C, the two slit banks, and L, respectively. The map sends it<sub>∗</sub> to 0.

### Example 6.1 — A sixth-order counterexample

For the fixed-degree results, H<sup>i</sup> is the set of real strictly Hurwitz polynomials of degree i, and MH<sup>n</sup> is the subset of H<sup>n</sup> consisting of monic polynomials. Let S<sub>n,i</sub> be the positive parameters feasible with x ∈ MH<sup>n</sup>, y ∈ H<sup>i</sup>, and strictly Hurwitz closed-loop polynomial Z from the problem statement. Write δ<sub>n</sub><sup>∗</sup> = sup S<sub>n,0</sub>.

Put δ<sub>b</sub><sup>∗</sup> = √(11/12). Every δ ∈ S<sub>6,0</sub> is strictly below δ<sub>b</sub><sup>∗</sup>, while some δ ∈ S<sub>6,6</sub> exceeds 0.96295. In particular,

<p align="center">δ<sub>6</sub><sup>∗</sup> ≤ δ<sub>b</sub><sup>∗</sup> &lt; 0.96295 &lt; sup S<sub>6,6</sub>.</p>

So a bound valid for constant numerators can fail when the numerator degree is raised to six with the denominator degree fixed. The proof uses a sign condition on the odd coefficients of a Hurwitz sextic to rule out constant numerators at and above the bound. An algebraic identity and a Möbius transformation give the strictly stable witness. [Lean refutation](formalization/Conjecture2.lean#L377) · [Threshold gap](formalization/Conjecture2.lean#L363)

### Theorem 6.2 — Sharpness of the continued-fraction bound

For n ≥ 1, let δ<sub>n</sub> be the largest positive real zero of the rational function f<sub>n</sub> defined by

<p align="center">f₀(δ) = −δ, &emsp; f<sub>n</sub>(δ) = −1/f<sub>n−1</sub>(δ) − 2δ.</p>

The theorem gives

<p align="center">δ<sub>n</sub> = sin((n + 2)π/[2(n + 1)]) = cos(π/[2(n + 1)]), &emsp; δ<sub>n</sub><sup>∗</sup> ≤ δ<sub>n</sub>,</p>

<p align="center">δ<sub>n</sub><sup>∗</sup> = δ<sub>n</sub> for 1 ≤ n ≤ 4, &emsp; δ<sub>n</sub><sup>∗</sup> &lt; δ<sub>n</sub> for n ≥ 5.</p>

Every δ ∈ S<sub>n,0</sub> is strictly below δ<sub>n</sub>. With a constant numerator, the bound can be approached arbitrarily closely at denominator degrees one through four. At each fixed degree five or higher, the feasible supremum stays strictly below the bound.

Chebyshev polynomials give f<sub>n</sub>(δ) = −T<sub>n+1</sub>(δ)/T<sub>n</sub>(δ). At low degrees, the closed-loop family Z(s) = (s + ε)<sup>n+2</sup> gives strictly feasible parameters approaching the bound. At higher degrees, approaching the bound would force an extra right-half-plane root in the limiting polynomial, contradicting strict Hurwitz stability along the approximating sequence. [Lean continued-fraction bound](formalization/ContinuedFractionBound.lean#L73) · [Equality classification](formalization/Conjecture3Equality.lean#L8)

## Lean 4 formalization

The project uses Mathlib and Tau Ceti and contains 160 Lean files with 21,726 source lines, excluding dependencies. The threshold theorem and the final declarations for Example 6.1 and Theorem 6.2 depend only on `propext`, `Classical.choice`, and `Quot.sound`. [Reproduction and axiom checks](formalization/REPRODUCE.md)

## Citation

Xiang Ji, Long Wang, and Wensheng Yu, *The Exact Stabilizability Threshold for the Belgian Chocolate Problem*, manuscript, 2026. When citing the Lean formalization, include the repository commit you used.
