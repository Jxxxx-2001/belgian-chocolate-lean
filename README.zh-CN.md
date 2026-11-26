# 比利时巧克力问题的精确可镇定性阈值

**Xiang Ji、Wensheng Yu** · 北京邮电大学电子工程学院

[English](README.md) · 中文

本仓库配套论文，包含 Lean 4 形式化证明和有理控制器证书。

[Lean 主定理](formalization/BelgianChocolateThreshold.lean#L89) · [公理审计](formalization/BelgianChocolateThresholdAudit.lean) · [复现说明](formalization/REPRODUCE.md)

## 问题

在 Blondel 同时镇定问题的多项式表述中，给定 $0<\delta<1$，寻找非零实多项式 $x,y$，使 $\deg y\le\deg x$，且 $x$、$y$ 和

```math
Z(s)=(s^2-2\delta s+1)x(s)+(s^2-1)y(s)
```

均严格 Hurwitz 稳定，即各自的所有零点都具有严格负的实部。有限阶控制器为 $y/x$。 [Lean 定义](formalization/ControllerFeasible.lean#L11)

## 主要结论

| 结论 | 表述 | Lean |
| --- | --- | --- |
| 有限阶控制器镇定 | 可行参数恰为 $(0,\delta_*)$，上确界 $\delta_*$ 不可达。 | [区间与端点](formalization/BelgianChocolateThreshold.lean#L38) |
| 圆盘插值 | 可行参数恰为 $[t_*,1)$。在 $t=t_*$ 处恰有两个插值函数 $f_*(z)$ 和 $f_*(-z)$，其中 $f_*'(0)>0$。 | [区间与端点分类](formalization/MarkedCompetitorComparison.lean#L236) |
| 精确阈值公式 | 令 $d_*$ 为唯一平衡裂缝域中单位下半圆在原点处的调和测度。则 $t_*=\tan(\pi d_*/4)$，且 $\delta_*=\cos(\pi d_*/2)=(1-t_*^2)/(1+t_*^2)$。 | [平衡裂缝](formalization/BalancedSlitRoot.lean#L101) · [精确公式](formalization/BelgianChocolateThreshold.lean#L32) |

数值近似 $\delta_*\approx 0.987237027$ 取自 Muhan Liu 的预印本第 6 节对调和测度和平衡方程的数值计算。 [Liu 的预印本](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf)

## 证明路线

先由平衡裂缝构造极值插值函数，再利用两个显式环域确定竞争插值函数的覆盖提升的边界标记。比较调和原函数得到圆盘阈值和端点分类。有限阶阈值以下，通过多项式逼近构造镇定控制器。临界点处，极值插值函数的边界行为排除了有限阶实现。

经验证的 28 阶有理控制器给出可行参数 $\delta_w=98236947/10^8$，对应的圆盘参数满足 $t_w<1/10$。由比较论证得到 $t_*\le t_w$，因此该论证覆盖所有不超过 $t_*$ 的正参数。 [Lean 见证](formalization/ControllerFeasible.lean#L34) · [独立 Schur 验证](verification/README.md)

## Lean 4 形式化

形式化工程使用 Mathlib 和 Tau Ceti。验收提交 [`4006bec`](https://github.com/Jxxxx-2001/belgian-chocolate-lean/commit/4006bec3e7f41c605a9bcd07d28d90fc4261b292) 收录 147 个 Lean 文件、19,330 行源码，统计范围为仓库内源码。

主定理 `BelgianChocolate.belgian_chocolate_threshold` 只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。审计覆盖的 31 个声明均依赖同样的三条公理。 [主定理](formalization/BelgianChocolateThreshold.lean#L89) · [公理审计](formalization/BelgianChocolateThresholdAudit.lean)

## 引用与相关工作

Xiang Ji、Wensheng Yu，《比利时巧克力问题的精确可镇定性阈值》，2026 年稿。引用 Lean 形式化时，请注明所使用的仓库提交。

背景可参阅 Blondel 的 [*Simultaneous Stabilization of Linear Systems*](https://link.springer.com/book/10.1007/3-540-19862-8) 和 Bergweiler 与 Eremenko 的 [*Goldberg's Constants*](https://www.math.purdue.edu/~eremenko/dvi/goldbergconst.pdf) 第 11 节。Muhan Liu 使用模覆盖和 Cauchy 积分论证得到了同一阈值。 [Liu 的预印本](https://www.alphaxiv.org/abs/2611.generalized-belgian-chocolate-stabilization.pdf)
