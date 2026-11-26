# P1.5 原历史物理系数的有限两长 P2 预算

状态：**source-only，未运行 Lean elaboration、内核回放或完整 owned 声明检查**。本目录推进原历史 `trueD` 物理通道的有限 expanded-core 预算。它位于 1106 稿两长误差 `M y² D^(3/2)` 的有限装配阶段。

## 原对象和实际结论

[P1OriginalHistoricalTwoLongP2.lean](P1OriginalHistoricalTwoLongP2.lean) 保持以下原对象：

- 模数集合是 `remainingModuli B N (trueDDeltaSupport old fresh N cap w z)`。
- 系数是原 `trueDDeltaRho old fresh N cap w z L` 的复数嵌入，策略差的顺序不变。
- 每个核仍用原目标 `N`、同一个物理模数 `q` 和已有 `mellinBrunCore` 的精确互素均值。
- 短系数仍是 `shortSequence` 的原有序 HB 元组推前，保留位置重数、碰撞符号、Möbius 截断、分子对数与 Mellin 相位。
- Brun 支撑仍是两份 `brunSupport Z (2*j+1)` 的笛卡尔积，系数仍是原 `brunPairCoefficient`。

记 `M = shortScale bs`、`y = Z^(2*j+1)`，并定义原模数矩预算

\[
T(D)=(D\sqrt D+1)\{4(1+\log\max(1,D))\}^{16}.
\]

`historical_rowCore_bound` 的源码给出

\[
\left\|\sum_{m\in I}\sum_{q\in Q}\rho(q)
 \sum_{(d_1,d_2)\in\mathcal D^2} b(d_1,d_2)
 \operatorname{mellinBrunCore}(\ldots,\alpha_m,m,d_1,d_2,N,q)\right\|
\le \operatorname{pairCost}(\delta,U,V,H)\,M y^2 T(D)
 (1+\log X)^{|\iota|}.
\]

条件只涉及原尺度、频率与有限支撑：`1 ≤ X`、每个短块 `2*lower ≤ X`、`1 ≤ Z`、`0 < delta ≤ 1/4`、`U,V > 0`、`H ≥ 0`、`|t₁|,|t₂| ≤ H`，以及原集合上 `q ≤ D`。

最后的 `historical_rowCore_bound_at_physical_level` 取

\[
D=\lfloor N^{599/1000}\rfloor,
\]

由 `remainingModuli` 自身的严格上截断推出全部模数的此上界，因此最终版本没有额外的 level 前提。任意辅助局部尺度版本仍可使用前一条定理，前提须由真实活项几何供应。

## 复用的证明

`historical_modulus_class` 直接调用已验收的 TrueD 支撑平方自由性、目标互素性和真实策略差单位幅度界。没有用旧的粗界 2，也没有将 free product carrier 认作平方自由。

`historical_modulus_moment` 沿用已有 `actual_lower_p2_modulus_moment` 的逐模数标量支配，换入上述真实历史系数，再调用 canonical `sum_divisor_fourth_moment_le_log`。没有假定整个模数矩，也没有依赖缺源的 `Part3TwoLongJointP2ModulusMoment`。

`historical_Brun_P2` 逐个原 Brun 对调用 `P4BOriginalSquarefreeP2.mellinBrunCore_internalP2`。这条已有点态证明不要求短积与模数互素，已保留非互素短积的原零分支；调用没有 `CompositeWeilInput`、`hP2` 或目标误差假设。

Brun 对质量来自已有 `brunPair_mass`，短系数质量来自已有 `shortSequence_mass`。六条通用 Brun 支撑/系数声明在 [support](support/) 中原字节提取为共享 owner；原 namespace 和证明体保留，旧 provider 的互补版本记录后续导入路由。这项采用不新增该六条证明的编译信用。

## 稿内范围和剩余连接

固定手稿是 `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en/coefficient-appendix.tex`，SHA256 `267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440`。对应原点态 P2/有限展开、`coef:core-summed` 及 779–820 行的 `coef:two-rough-error`。

本源码尚未把原 rough 对等同于 Brun 多项式；E1/E3 的精确均值及其两倍因子、各 sharp 端点的积分误差、原 singleton 图/HB/Fourier 恢复都仍需原供应接口接入。它也没有在实际 `x` 上完成最终任意对数精度支付。

原 singleton `actual_fourier_l1_budget` 在固定阶数 6 时给出 `log(N+2)^72`；外层图/HB 计数还会产生额外损失。后续应按该真实预算选择局部精度，不能直接采用 P4 为自身 `log^38` 总量安排的 `A+40`。相关既有供应应继续复用。

编译和来源状态见本目录 `SOURCE_REVIEW.json`。完整 P1.5 仍未闭合。
