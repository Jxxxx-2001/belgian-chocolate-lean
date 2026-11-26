# The Exact Stabilizability Threshold for the Belgian Chocolate Problem

**Xiang Ji and Wensheng Yu** · School of Electronic Engineering, Beijing University of Posts and Telecommunications

English · [中文](README.zh-CN.md)

Project affiliation: Intelligent Information Processing Laboratory, Beijing University of Posts and Telecommunications (北京邮电大学 智能信息处理实验室).

**Initial Lean formalization commit: 2026-11-25 · [4006bec](https://github.com/Jxxxx-2001/belgian-chocolate-lean/commit/4006bec3e7f41c605a9bcd07d28d90fc4261b292).**

**Content updated: 2026-11-26.**

This repository accompanies the manuscript and contains the Lean 4 formalization and the rational controller certificate.

[Lean main theorem](formalization/BelgianChocolateThreshold.lean#L89) · [Axiom audit](formalization/BelgianChocolateThresholdAudit.lean) · [Reproduction instructions](formalization/REPRODUCE.md)

## The problem

In the polynomial formulation of Blondel's simultaneous stabilization problem, fix 0 &lt; δ &lt; 1. Seek nonzero real polynomials x, y with deg y ≤ deg x such that x, y, and

Z(s) = (s² − 2δs + 1)x(s) + (s² − 1)y(s)

are strictly Hurwitz stable, meaning that each zero has strictly negative real part. The finite-order controller is y/x. [Lean definition](formalization/ControllerFeasible.lean#L11)

## Main results

| Result | Statement | Lean |
| --- | --- | --- |
| Finite-order stabilization | The feasible parameters are exactly (0, δ<sub>∗</sub>). The supremum δ<sub>∗</sub> is unattained. | [Interval and endpoint](formalization/BelgianChocolateThreshold.lean#L38) |
| Disk interpolation | The feasible parameters are exactly [t<sub>∗</sub>, 1). At t = t<sub>∗</sub> there are exactly two interpolants, f<sub>∗</sub>(z) and f<sub>∗</sub>(−z), with f<sub>∗</sub>′(0) &gt; 0. | [Interval and endpoint classification](formalization/MarkedCompetitorComparison.lean#L236) |
| Exact threshold formula | Let d<sub>∗</sub> be the harmonic measure at 0 of the lower unit semicircle in the unique balanced slit domain. Then t<sub>∗</sub> = tan(πd<sub>∗</sub>/4) and δ<sub>∗</sub> = cos(πd<sub>∗</sub>/2) = (1 − t<sub>∗</sub>²)/(1 + t<sub>∗</sub>²). | [Balanced slit](formalization/BalancedSlitRoot.lean#L101) · [Exact formulas](formalization/BelgianChocolateThreshold.lean#L32) |

The numerical approximation δ<sub>∗</sub> ≈ 0.987237027 comes from Muhan Liu's evaluation of the harmonic measure and balance equation (preprint, Section 6). [Liu's preprint](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf)

## Research background

- **1994.** Vincent Blondel posed the problem in the study of simultaneous stabilization. The polynomial formulation asks when a stable, minimum-phase rational controller can stabilize a particular second-order plant. [Blondel’s monograph, pp. 149–150](https://link.springer.com/book/10.1007/3-540-19862-8)
- **2013.** Walter Bergweiler and Alexandre Eremenko formulated the associated holomorphic interpolation problem on the unit disk and proved the upper bound δ<sub>∗</sub> &lt; 0.999579. [*Gol’dberg’s Constants*, §11](https://www.math.purdue.edu/~eremenko/dvi/goldbergconst.pdf)
- **2018.** Zachary Charles and Nigel Boston proved that δ = 0.9808348 is feasible using the algebraic structure of the stabilization equations. [Charles and Boston, Theorem 5.1](https://arxiv.org/abs/1708.08114)
- **2026.** Xuandi Cheng gave an exact polynomial certificate for feasibility at δ = 0.9846316110433085. Muhan Liu derived the same exact threshold as the accompanying manuscript using a modular covering and a Cauchy integral argument. [Cheng’s certificate](https://github.com/chengxuandi/belgian-chocolate-certified-lower-bound/tree/362cf25a04ebd0468b05153008ba72dca7f09ef6) · [Liu’s preprint](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf)

## Proof outline

The proof constructs the extremal interpolant from the balanced slit. Two explicit annuli determine the boundary markings of the covering lifts of competing interpolants. Comparing harmonic primitives then gives the disk threshold and the endpoint classification. Below the finite-order threshold, polynomial approximation produces stabilizing controllers. At the threshold, the extremal interpolant's boundary behavior rules out a finite-order realization.

A certified degree-28 rational controller gives feasibility at δ<sub>w</sub> = 98236947/10⁸. Its associated disk parameter satisfies t<sub>w</sub> &lt; 1/10. The comparison argument gives t<sub>∗</sub> ≤ t<sub>w</sub>, so the comparison applies to every positive parameter up to t<sub>∗</sub>. [Lean witness](formalization/ControllerFeasible.lean#L34) · [Independent Schur verification](verification/README.md)

## Lean 4 formalization

The formalization uses Mathlib and Tau Ceti. The audited source snapshot ([`4006bec`](https://github.com/Jxxxx-2001/belgian-chocolate-lean/commit/4006bec3e7f41c605a9bcd07d28d90fc4261b292)) contains 147 Lean files and 19,330 source lines, excluding external dependencies.

The main theorem, `BelgianChocolate.belgian_chocolate_threshold`, depends only on `propext`, `Classical.choice`, and `Quot.sound`. The axiom audit reports the same three dependencies for all 31 checked declarations. [Main theorem](formalization/BelgianChocolateThreshold.lean#L89) · [Axiom audit](formalization/BelgianChocolateThresholdAudit.lean)

## Citation

Xiang Ji and Wensheng Yu, *The Exact Stabilizability Threshold for the Belgian Chocolate Problem*, manuscript, 2026. When citing the Lean formalization, include the repository commit you used.
