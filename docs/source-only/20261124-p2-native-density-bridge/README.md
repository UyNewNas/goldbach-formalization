# Native Ω3：接入已有 Fine selection 的真实 K 密度

2026-11-24。状态：**SOURCE ONLY / UNCOMPILED / NO NEW KERNEL CREDIT**。

候选：`ImbalancedChen/P2NativeOmega3FineDensityBridge.lean`。两个公开定理、零新定义、零公理。没有执行 Lean 或云编译，没有修改原接收器、原 Fine supplier 或 P3。

## 复用检查与新增范围

先读取了已有 [UPSTREAM_REUSE_REVIEW.json](../20261124-p2-wu-uniform/UPSTREAM_REUSE_REVIEW.json)，继而只检查精确源声明及已有调用。

`P4BOriginalFineAttachedUpper.Selection.attached_K` 已被 P5 的 U7/U8/U9 和 P6 outer-row 接收器使用；这些现成接口不应重写。当前本地 active/source-only Lean 搜索中，没有另一个调用 `P2NativeOmega3SameRhoNormalization.uniform_actual_rho_normalized_comparison` 的桥。

此候选只接上该 native Ω3 接收器的 `hdensity`。它没有重复证明实际密度、native Ω3 mass、奇异级数归一化、prime-window 计数或 Θ 下界。

## 对象逐项一致

| native 接收器参数 | 本候选实际选择 | 原有依据 |
|---|---|---|
| `K` | `currentK` | `Selection.attached_K` 的同一常数；正性直接计算 |
| `nu` | `1` | 原 `exists_counting_selection` 的输出 |
| `r` | `19/96` | 同上；不是 Fine 网格参数 `r : ℕ` |
| `e` | `selection.beta` | 不是 Fine selection 的有理精度 `e : ℚ` |
| `retain` | `retention m r n e q a (1 * selection.beta^2)` | 与 `attachedDensity` 定义逐项相同 |
| `cap` | `id` | 原 selection 采用的枚举上界 |
| `D` | `attachedUpperModuli 1 (19/96) selection.beta retain id N` | 原 `attachedDensity` 的真实模数集 |
| `rho` | `attachedUpperCoefficient 1 (19/96) selection.beta retain id N` | 原 `attachedDensity` 的同一真实系数 |
| `0 < beta ≤ 1` | 由 `selection.pos`、`selection.lt_eighth` 得到 | 没有新增输入 |
| `beta² ≤ 19/96` | `selection.square_lt.le` | 没有新增输入 |
| `N^(1*(19/96)) ≤ cap N` | `N ≥ 4` 后指数单调性 | 没有新增输入 |

`Selection.attached_K` 是 eventual 命题，Ω3 receiver 返回具体阈值。本候选取两者阈值的最大值；对同一 N 使用 selection 的密度。没有换一套 coefficient，也没有为每个 source box 重新选 policy。

## 两个声明

### `selected_omega3_comparison`

输入已有 `Selection ... 1 (19/96) ...`、native depth k、`0<δ≤1/10`、`τ>0`、`ε>0`，直接调用两个原定理，得到：

```text
∃ T≥4, ∀ N≥T even, ∀ native legal boxes, ∀ 2≤s≤t≤10,
  wuOmega3Sum
  ≤ (((1+τ)·currentK/4)·omega3XIntegralEnvelope(s,t)+ε)·boxTheta
      + actual coprime correction
      + actual signed distribution error
      + actual small-prime mass.
```

结论中的三个误差逐字保留原 native receiver 的 `labels`、`sourceProduct`、`weight`、模数集和 coefficient。

### `exists_selected_omega3_comparison`

先用原 `exists_counting_selection` 从有限策略参数构造 selection。调用者只提供原参数范围、正 fine-tolerance 和 mesh/denominator 请求，**不提供 `Selection`、`hdensity`、PP、hRows 或计数下界假设**。结论给出同一个 selection，然后才量化 k、δ、τ、ε、N、source boxes 和 s,t。

这使第一条不只是把 density 前提装进一个结构后改名：所用结构的存在性在第二条中由原有源码定理实际构造。

## 手稿与量词边界

对应固定1106稿 `chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`，`argument.tex` 的 `eq:current-PP` 与 `prop:current-positive-product` 中，同一 ρ 同时用于 density 与 signed discrepancy 的要求。

该候选保持现成 native receiver 已有的 box 量词，只去掉其可由已有 source supplier 供给的密度前提；没有建立一个新的 all-moving PP 命题。它也没有把 native Wu 盒与手稿增强 marked family 识别。有限族与 native H/h 的区别继续以 [P2 最终依赖审计](../../verification/20261124-p2-private/P2_FINAL_DEPENDENCY_AUDIT.md) 为准。

## 剩余与验收要求

三个实际误差仍需各自供应，尤其 `p5z_labelledDistributionError` 仍须实际同一 ρ、许可几何权重的 P3 分布结论。没有假定 `full_uniform`、`hRows` 或 `UniformPrimeProductTarget` 已成立；这一步不供给 `testedFibreBalance` 的全部 Γ5/Γ9–21、不证明 H247、采用 seed 或完整 P2。

Y07 `P4BOriginalFineAttachedUpper` 已在原复用审计中核对远端 exact source，却尚无已找到的完整 strict/kernel receipt。此新桥必须连同 manifest 选定的两个直接源与各自真实依赖闭包一起验证。仅本文件的源码可读性、两个对象的定义一致、或后续某个局部 import 成功，都不能给完整证明信用。不得通过引入 density/count-shaped 公理或用不一致的旧对象满足导入。

下一数学阻塞在 actual signed PP 与另外两项真实误差的支付，不在当前密度参数接线。本小分支到这里停止，等待原候选闭包验收及对应真正分析供应。

## 独立源码复核

`/root/p2_numerical` 对候选及两个精确直接源做了只读独审，确认 D/rho/retention/ceil cutoff 定义一致、所有参数侧条件来自已有字段、selection 与阈值量词顺序正确、三个原误差保留。未要求改动 Lean 文件。复核版本 SHA 与具体范围已写入 `SOURCE_MANIFEST.json`；该结果仅为源码逻辑审查，不是 Lean 编译或内核验收。
