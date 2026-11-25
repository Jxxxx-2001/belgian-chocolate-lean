# 比利时巧克力问题的精确镇定阈值

[English](README.md) · 中文

## 问题

在 Blondel 同时镇定问题的多项式表述中，给定 $0<\delta<1$，寻找非零实多项式 $x,y$，使 $\deg y\le\deg x$，且 $x$、$y$ 和

```math
Z(s)=(s^2-2\delta s+1)x(s)+(s^2-1)y(s)
```

的每个零点都具有严格负的实部。有限阶控制器为 $y/x$。[Lean 定义](formalization/ControllerFeasible.lean#L8)

## 主要结论

[Lean 主定理 · `BelgianChocolate.belgian_chocolate_threshold`](formalization/BelgianChocolateThreshold.lean#L89)

| 结论 | 表述 | Lean |
| --- | --- | --- |
| 精确镇定阈值 | 原始问题的可行参数恰为 $(0,\delta_*)$，上确界 $\delta_*$ 不可达。 | [可行区间、端点和上确界](formalization/BelgianChocolateThreshold.lean#L38) |
| 调和测度公式 | 令 $d$ 为唯一平衡裂缝域中从 $0$ 看单位下半圆得到的调和测度。则 $t_*=\tan(\pi d/4)$，$\delta_*=\cos(\pi d/2)=(1-t_*^2)/(1+t_*^2)$。数值近似为 $\delta_*\approx0.987237027$。 | [唯一平衡裂缝](formalization/BalancedSlitRoot.lean#L101) · [精确公式](formalization/BelgianChocolateThreshold.lean#L33) |
| 圆盘插值阈值 | 圆盘可行参数恰为 $[t_*,1)$。在 $t=t_*$ 处，满足 $f'(0)>0$ 的解在整个开单位圆盘上唯一。 | [可行性与唯一性](formalization/BelgianChocolateThreshold.lean#L35) |

证明先构造平衡裂缝，再用两个显式环域归一化覆盖提升，通过调和原函数比较排除更小的圆盘参数。最后构造 $0<\delta<\delta_*$ 时的有限阶控制器，并排除临界点处的有限阶实现。

## 复现与引用

[构建和审计 Lean 主定理](formalization/REPRODUCE.md) · [复算有理控制器见证](verification/README.md)

背景可参阅 Blondel 的 [*Simultaneous Stabilization of Linear Systems*](https://link.springer.com/book/10.1007/3-540-19862-8) 以及 Bergweiler 与 Eremenko 的 [*Goldberg's Constants*](https://www.math.purdue.edu/~eremenko/dvi/goldbergconst.pdf) 第 11 节。Liu 的另一份阈值解析证明见 [*An Analytic Solution to the Generalized Belgian Chocolate Problem*](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf)。

引用 Lean 形式化时，请注明实际使用的仓库发布版本或提交。
