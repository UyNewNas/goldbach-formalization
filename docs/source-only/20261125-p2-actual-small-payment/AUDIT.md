# P2 1106 稿内闭合边界与本轮小乘积付款

审计基线：`UyNewNas/goldbach-formalization` 的 P2 HEAD `e008ae002d4cec5f01b127a11dbb13016be38c97`；1106 手稿基线 `a988cba584d803ae2856a0de50efb582f4f3dd6a`。本记录只读原项目，候选写在独立目录；未调用云编译，未 commit/push。状态必须区分**已有证明源码**、**仍缺真实证明**和**待来源/编译/内核资格化**。

## 这次实际推进

新增 `ImbalancedChen/Part5OriginalH430ActualSwitchedSmallPayment.lean`，四个 theorem、一个定义。既有 `Part5OriginalH430ClassicalSwitchedSmallPayment.small_both_atoms` 本身只要求 `d>0`、`Q≤N`、`N^frozenResidualFloor≤Q/d`，没有 classicalBand 或 α>3 条件。既有 `SeedHistoryMass.scale_and_alpha` 和 `OriginalRootQBound.original_root_Q_le_target` 对实际 U3/U4 history 已供应这些条件。因此，本次只推广此前限制为 classical U3 的 marked consumer，没有重证整数计数、对数吸收、PP/VM 或 all22。

令 `X=N^(1-κ)`，`A_B` 为实际 Γ9–21 小完整乘积的带素数测试正计数，`B_B` 为同一整数载体的原 `(K/4)*thetaConversion` 计价。新源码对两种原始 root、每个实际 `LevelIndex` 子族，在同一个充分大阈值下得到

\[
0\le A_B\le\varepsilon\Theta_B,\qquad
0\le B_B\le\varepsilon\Theta_B,\qquad
|A_B-B_B|\le\varepsilon\Theta_B.
\]

`marked_split` 逐项识别该差为 `switchedPPBalance B - remainingSwitchedBalance κ B`。后者显式保留 Γ5 与 Γ9–21 的大完整乘积、原素数测试、全部标签/重复字/单位尾、同一 `Q,d` 和原计价。`actual_seed_and_four_rounds_after_small_payment` 以 ε/2 分配将付款接回原实际 seed 与四轮 endpoint；阈值不依赖子族个数，没有除以可能为零的质量，也没有假设待证 PP/debt 结论。

这里允许任意实际子族 B，是因为所用界逐个 d 统一成立，再乘正 mark 求和；并未把稿内的固定有限 PP 分布结论扩张为未经证明的任意移动族版本。

1106 对应：`prop:current-positive-product`、`coef:prime-product-insertion` 的固定幂次小完整乘积付款，及 `sv:feedback-error` 的固定正残余尺度。候选使用精确 sharp split `Dm≤N^(1-κ)`；并未宣称完成 `2N^(1-κ)` 平滑过渡区或 PP 分布证明。它不把 classical U3 的 α>3/cubic margin 推广到增强 U3/U4。

**验收边界：SOURCE_ONLY_UNCOMPILED；formal credit = 0。** 本机 `lean`/`lake` 不在 PATH，未提交任何云运行。原 `small_both_atoms` 所在包的 `REGISTRY.json` 也标为 `SOURCE_ONLY_UNCOMPILED`。因此这是可复核的新证明源码，不能写成 P2 已验收或小债务已获内核验收。

## 可复用供应与真正的开放前提

| 项 | 现有具体入口 | 结论及状态 | 1106 对应 |
|---|---|---|---|
| 原 all22 的实际同系数密度 | `P4AOriginalFiniteAll22FineDensity.exists_fine_same_rho_hdensity` | 已有完整源码，直接接 Nineteen、actual early defect、同一 β/k/ρ 与一次 compiler reserve；无需重写。历史独审为源码完成；依赖选源及编译/内核仍待资格化。 | `sv:literal-density`、`sv:finite-realization`、`eq:current-upper-density` |
| all22 缺失本地文件 | `P4AOriginalFiniteAll22PaidSixth`、`Nineteen`、`EarlyDefectCounting` | 已在固定远端 `eea9486f7b101d484e2938e97499c1d77cc1a67a` 定位原源码，见既有 `all22-reuse-supply.json`。属于原源码复用/资格化，不是新数学缺口。 | 同上 |
| Winner9 同 owner seed | `P4AOriginalFull87SeedRefinements.original_seed_refined_floor` | 11 月 24 日原声明替换已存在，使用 actual Full87 `.nine11` 及 21/22 increment 各一次。数值验收由 root 另行处理；本任务未重复。 | 原有限证书与密度账本 |
| proper-power 删除 | `Part3.ProperPowerChartSum.eventually_primeProductSignedError_sub_vonMangoldt_logAccuracy`；`Part3.ProperPowerActualPairFamily.eventually_smoothPair_uniformWidth_prime_sub_vonMangoldt_logAccuracy` 及 varying-width 版本 | P3 固定 head `ef1479c272bdd6b24800fa10409d793f0a2fe95c` 已验收供应；保持同一带符号 ρ、精确互素均值、product=N 项。可复用；不是完整 PP 定理。 | `coef:prime-product-insertion` |
| 同 ρ 的真正 PP/VM 分布 | `P4BOriginalFineAttachedRetained.uniformPP_of_remainingRows` 的 `hRows` | **仍欠证明**：对原 `remainingRows` 的每个整数精度 p，证明 `∃ D≥0, ∀ᶠ N, Even N → ‖remainingRows …‖≤D*N/(log N)^p`。该源保留此假设；proper-power 删除仅比较 prime 与 VM，不能自行提供 VM 本体的 cancellation。`RestrictedMediumObligation` / `UniformPrimeProductTarget` 的整体原始供应仍开放。 | `prop:current-medium`、`eq:current-PP`、`coef:prime-product-insertion` |
| 实际 Γ5 Family 实例 | `scale_and_alpha` 等几何供应；rank 另由 agent 实作 | 除 rank 外，实际源到 smooth/profile 的一致性、有效整数支撑、collar、实际 width 预算与 PP 仍需逐项接线/证明。classical `Family200`/`1/90` 不自动覆盖原 U3/U4 全 history。 | `sv:full-switched-mass`、`sv:switch-mass-bounds` |
| seed / W1 / W2 实际 count 接线 | `SeedSameCarrierPP.actual_seed_and_four_rounds_at_common_prime_restriction`；`AllBankSignedCounts`；`W2SignedOrdinaryBase.rowDebt` | 已有实际载体和有向代数源码，**不是仅待编译即可全闭合**。`ordinaryAP`、大乘积/Γ5 discrepancy、W1/W2 的 fixed/lower/switched/child debts 仍出现在结论。本候选仅移除明确的小乘积部分。 | `sv:two-step-base`、`sv:two-step-feedback`、`sv:finite-seed`、`sv:seed-feedback-integral` |
| Wu/H247 实函数语义 | `P2HistoricalLowTargetEdges.original_bank_from_edges`；`P2HistoricalSavedFloorFullBinder.checked_full_saved_total_actual_lower` | 原 29 条边界不等式 `readGain 247 i ≤ H δ (tableGrid (i+1))` 仍是前提，不能用已计算数组代替原 Wu 实函数。原 Binder 仍需 `BankEndpointLicences` 及实际积分供应。本次检查范围未找到这 29 条的完整付款。 | `sv:finite-feedback`、`sv:feedback-error` 与原有限迭代 |

## 难点分类与最小下一步

- **表达/接线困难**：same ρ、实际 labelled source、统一参数顺序、有限正族与 zero-mass 的一致性；本次 all-root 小乘积推广属于这一类，已有 scalar proof 真实支持结论。
- **稿内省略推导**：同一原子中保留 `1/d` 后将整数小乘积界吸收到真 `thetaAtom`，以及有限 marks 的和；旧 scalar source 已实现，本次只补缺失的实际全 root 消费。
- **实质尚未形式化的证明义务**：`hRows` 原始 signed rows 的任意 log saving、实际 PP/VM/medium 本体、W1/W2 有向差额和 Wu 原函数 licence。这些不能用类型包装或把目标重新作为假设消除。发现这些开放前提不等于发现 1106 数学反例；本审计没有证明稿件存在实质矛盾。
- **来源/验收资格化**：all22、H430 历史供应、11 月 12 日 small-payment 包等已有源码应先复用并核对 ABI/对象/公理闭包。大型历史 manifest 本身不授予内核信用，也不能作为重写现有证明的理由。

下一步最小实作是让当前候选连同既有 scalar supplier 和实际 history geometry 一起完成限定依赖选源与编译验收。若继续推进整个分布债务，应直接证明上述 `hRows` 或实际族所需的对应原始 signed VM 估计，而不是添加一个仍输入同名 target 的 wrapper。

机器可读的来源、哈希、状态与未付款清单见 `AUDIT.json`。文件中的 `source_present` 与 `kernel_accepted` 字段独立；本轮没有新 formal credit。
