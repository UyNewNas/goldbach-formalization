# 原 singleton remaining Type I：实际两长几何

**Source-only，未 elaboration，没有新增 Lean／kernel 接受。** 本目录记录新 owner [P1OriginalSingletonRemainingTypeIGeometry.lean](../../../../ImbalancedChen/P1OriginalSingletonRemainingTypeIGeometry.lean) 的源码与手稿合同；完整指纹、声明区间和原 supplier 绑定见 [SOURCE_REVIEW.json](SOURCE_REVIEW.json)。没有修改现有 Lean owner、runner 或验收清单。

## 实际完成的连接

固定 `kap0 < 1` 和 `0 < zeta ≤ 1/20000`，先取得一个充分大的物理 `N` 阈值，再量化所有 profile `kap`、collar order `B`、rough-cutoff order `K`、chart `cj`、HB order、原整数和有序 block word。

原 `originalChart (actualLicence kap B N) N kap0 [cj] [n] ≠ 0` 的额外 `eta` 给出 `N^(1-kap0) < n`，已有 `profile_nonzero_support` 给出 `R/2 ≤ n ≤ 2R`。因此所有活 chart 的 `R` 统一趋于无穷。正指数增长进一步给出 `8192 < R^(1-18*zeta)` 和 `4 < R^(3*zeta/4)`。

随后直接复用旧 `original_chart_numeric_reserves`，代入 `X=R`、`a=1`、`C=2` 和原 `hbCutoff=(2R)^(1/3)`。它支付旧 `original_noMedium_actual_alternative` 所需的全部五个数值门槛；新定理没有把这些门槛重新列成假设。原 Type I 的两个判断再排除一长，得到恰两长，且每条 long occurrence 的角色是 `.one` 或 `.logarithm`。重复 block 仍按有序 occurrence 计数，原整数不被限制为素数。

## 原 remaining predicate 保持不变

历史 `P1OriginalSingletonOneLongRectangle.remainingTypeIValue` 的正文为：

```lean
if (longBlocks hi (rows.flatMap Row.blocks)).length = 1 then 0
else typeIValue lo hi F rows
```

新 `singleton_remaining_predicate_iff` 只把 `rows := [row]` 后的这个正文展开，证明其非零条件恰为“long count 非一、`firstMedium=none`、原 `F [row]≠0`”。没有新增另一个 remaining carrier。最后的 row terminal 保留 `row.factors.prod`、`row.blocks` 和原 `F`；可将 `F` 直接实例化为原 `sourceTest`，保留同一 `Q/rho`。

该几何终点仍明确使用原 **非零 `blockCoefficient`**，即有限 assigned-weight 和之后的 block。它没有把单个非零 `assignedWeight` 等同于非零 block 和，也未支付整个 remaining Atlas 的误差。

## 来源与发布边界

手稿是固定 `a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 1106 `coefficient-appendix.tex`，对应 526–548、621–630 的原 HB／Type I 段落。旧 numeric、role、profile-support 与 cutoff 证明保持原 owner 和字节。

一个直接 supplier 的 canonical 路径仍待随 root 的 **rough4** 原样采用发布：`P5OriginalPrimeAtlasReserveBranches.lean`。共享树的预存副本与已发布档案 `docs/source-only/20261028-resume-30f/pp_fourier/P5OriginalPrimeAtlasReserveBranches.lean` 完全相同：8183 字节，SHA-256 `8b8987b5208aa0ed201adeb84a03076119519ff2880fb442175de2385b3ad049`，Git blob `3b9dcf2b9a75ad6f9667b641dde32562e43d5e7e`。本工作没有写入或更改该副本，也没有复制其 `originalMediumLow/High` 定义。因此当前交付不宣称 clean-checkout import-ready；root 将在合并 rough 与 geometry 源后另建完整源图。

本次完成作者静态源码／手稿合同检查及精确来源绑定。两个 peer 正处理优先编译事务，本交付未附独立审查回执；没有执行 Lean、kernel 或云任务。后续仍需独立静态复核、选定后的原验收门槛，以及两长 rough／strip／P2／Fourier／外层预算装配。完整 medium signed M 继续复用 P3.4/P3.5 的实际族接入工作。
