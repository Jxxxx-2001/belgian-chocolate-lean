# The Exact Stabilizability Threshold for the Belgian Chocolate Problem

English · [中文](README.zh-CN.md)

## The problem

In the polynomial formulation of Blondel's simultaneous stabilization problem, fix $0<\delta<1$. Seek nonzero real polynomials $x,y$ with $\deg y\le\deg x$ such that $x$, $y$, and

```math
Z(s)=(s^2-2\delta s+1)x(s)+(s^2-1)y(s)
```

are all strictly Hurwitz stable. Each zero must have strictly negative real part. The finite-order controller is $y/x$. [Lean definition](formalization/ControllerFeasible.lean#L8)

## Main results

[Lean main theorem · `BelgianChocolate.belgian_chocolate_threshold`](formalization/BelgianChocolateThreshold.lean#L89)

| Result | Statement | Lean |
| --- | --- | --- |
| Exact stabilizability threshold | The feasible parameters are exactly $(0,\delta_*)$. The supremum $\delta_*$ is unattained. | [Feasible interval, endpoint, and supremum](formalization/BelgianChocolateThreshold.lean#L38) |
| Harmonic-measure formula | Let $d$ be the harmonic measure at $0$ of the lower unit semicircle in the domain with the unique balanced slit. Then $t_*=\tan(\pi d/4)$ and $\delta_*=\cos(\pi d/2)=(1-t_*^2)/(1+t_*^2)$. Numerically, $\delta_*\approx0.987237027$. | [Unique balanced slit](formalization/BalancedSlitRoot.lean#L101) · [Exact formulas](formalization/BelgianChocolateThreshold.lean#L33) |
| Disk interpolation threshold | The disk problem is feasible exactly for $t\in[t_*,1)$. At $t=t_*$, the solution with $f'(0)>0$ is unique on the open unit disk. | [Feasibility and uniqueness](formalization/BelgianChocolateThreshold.lean#L35) |

The proof constructs the balanced slit, uses two explicit annuli to normalize covering lifts, and compares harmonic primitives to rule out smaller disk parameters. The final step constructs finite-order controllers for $0<\delta<\delta_*$ and excludes the finite-order endpoint.

## Quick verification

[Build and audit the Lean theorem](formalization/REPRODUCE.md) · [Recompute the rational controller witness](verification/README.md)

## Related work and citation

For background, see Vincent Blondel's [*Simultaneous Stabilization of Linear Systems*](https://link.springer.com/book/10.1007/3-540-19862-8) and Section 11 of Walter Bergweiler and Alexandre Eremenko's [*Goldberg's Constants*](https://www.math.purdue.edu/~eremenko/dvi/goldbergconst.pdf). For another analytic proof of the threshold, see Muhan Liu's [*An Analytic Solution to the Generalized Belgian Chocolate Problem*](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf).

For the Lean formalization, cite the repository release or commit you used.
