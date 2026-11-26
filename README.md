# The Exact Stabilizability Threshold for the Belgian Chocolate Problem

**Xiang Ji and Wensheng Yu** · School of Electronic Engineering, Beijing University of Posts and Telecommunications

English · [中文](README.zh-CN.md)

This repository accompanies the manuscript and contains the Lean 4 formalization and the rational controller certificate.

[Lean main theorem](formalization/BelgianChocolateThreshold.lean#L89) · [Axiom audit](formalization/BelgianChocolateThresholdAudit.lean) · [Reproduction instructions](formalization/REPRODUCE.md)

## The problem

In the polynomial formulation of Blondel's simultaneous stabilization problem, fix $0<\delta<1$. Seek nonzero real polynomials $x,y$ with $\deg y\le\deg x$ such that $x$, $y$, and

```math
Z(s)=(s^2-2\delta s+1)x(s)+(s^2-1)y(s)
```

are strictly Hurwitz stable, meaning that each zero has strictly negative real part. The finite-order controller is $y/x$. [Lean definition](formalization/ControllerFeasible.lean#L11)

## Main results

| Result | Statement | Lean |
| --- | --- | --- |
| Finite-order stabilization | The feasible parameters are exactly $(0,\delta_*)$. The supremum $\delta_*$ is unattained. | [Interval and endpoint](formalization/BelgianChocolateThreshold.lean#L38) |
| Disk interpolation | The feasible parameters are exactly $[t_*,1)$. At $t=t_*$ there are exactly two interpolants, $f_*(z)$ and $f_*(-z)$, with $f_*'(0)>0$. | [Interval and endpoint classification](formalization/MarkedCompetitorComparison.lean#L236) |
| Exact threshold formula | Let $d_*$ be the harmonic measure at $0$ of the lower unit semicircle in the unique balanced slit domain. Then $t_*=\tan(\pi d_*/4)$ and $\delta_*=\cos(\pi d_*/2)=(1-t_*^2)/(1+t_*^2)$. | [Balanced slit](formalization/BalancedSlitRoot.lean#L101) · [Exact formulas](formalization/BelgianChocolateThreshold.lean#L32) |

The numerical approximation $\delta_*\approx 0.987237027$ comes from Muhan Liu's evaluation of the harmonic measure and balance equation (preprint, Section 6). [Liu's preprint](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf)

## Proof outline

The proof constructs the extremal interpolant from the balanced slit. Two explicit annuli determine the boundary markings of the covering lifts of competing interpolants. Comparing harmonic primitives then gives the disk threshold and the endpoint classification. Below the finite-order threshold, polynomial approximation produces stabilizing controllers. At the threshold, the extremal interpolant's boundary behavior rules out a finite-order realization.

A certified degree-28 rational controller gives feasibility at $\delta_w=98236947/10^8$. Its associated disk parameter satisfies $t_w<1/10$. The comparison argument gives $t_*\le t_w$, so the comparison applies to every positive parameter up to $t_*$. [Lean witness](formalization/ControllerFeasible.lean#L34) · [Independent Schur verification](verification/README.md)

## Lean 4 formalization

The formalization uses Mathlib and Tau Ceti. The audited source snapshot ([`4006bec`](https://github.com/Jxxxx-2001/belgian-chocolate-lean/commit/4006bec3e7f41c605a9bcd07d28d90fc4261b292)) contains 147 Lean files and 19,330 source lines, excluding external dependencies.

The main theorem, `BelgianChocolate.belgian_chocolate_threshold`, depends only on `propext`, `Classical.choice`, and `Quot.sound`. The axiom audit reports the same three dependencies for all 31 checked declarations. [Main theorem](formalization/BelgianChocolateThreshold.lean#L89) · [Axiom audit](formalization/BelgianChocolateThresholdAudit.lean)

## Citation and related work

Xiang Ji and Wensheng Yu, *The Exact Stabilizability Threshold for the Belgian Chocolate Problem*, manuscript, 2026. When citing the Lean formalization, include the repository commit you used.

For background, see Vincent Blondel's [*Simultaneous Stabilization of Linear Systems*](https://link.springer.com/book/10.1007/3-540-19862-8) and Section 11 of Walter Bergweiler and Alexandre Eremenko's [*Goldberg's Constants*](https://www.math.purdue.edu/~eremenko/dvi/goldbergconst.pdf). Muhan Liu obtained the same threshold using a modular covering and a Cauchy integral argument. [Liu's preprint](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf)
