# P2.9：实际有限标记族与 native Wu 的语义边界

日期：2026-11-25。本文记录此前完成的只读源码与冻结稿核对；保存本文未重跑检索、编译、原 producer、数值 guard 或 kernel replay。

项目源码核对基线为 `a929011ec95843553fc2e10b7291c8077e0952c0`；冻结稿为 `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`。后者相对发布提交 `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` 仅修改 README，本文所引 release-20261106 稿件未变。

## 结论与后续方向

1. **29 条 H247 比较是现行 native-Wu bank/Binder 路线的未证充分条件，不等价于冻结稿唯一或必要的剩余目标。** 现有代码没有证明该路线与实际 admitted marked-family 语义等价。
2. native 目标在移动盒统一性方面附加了要求，其物理层级却固定在 `Q=N^(1/2-δ)`；冻结稿还使用增强的 `Q=N^λ`。**两族不能直接作全盘“更强／更弱”的排序，也不能直接认同。**
3. 现有 `P2AdoptedSeedSourceBoundary` 是明确标记为 SOURCE_ONLY 的边界证据，本文未确认其内核验收；对象不相同、简单转移不足，均不证明 29 条比较为假，**也不证明手稿错误**。
4. **后续应在原 Q、原标签、selected gates、stable ceiling 与原 Θ 上，为实际有限 marked family 补 count licences，并接回有限数组与实际积分。** 不应仅为消除旧 Binder 的接口前提，把本轮任务扩展成稿外通用 Wu 量词下的新证明工程。已有 native 结果保留其原范围，不能用它们替换实际族尚欠的许可。

## 1. 当前 bank 使用的确实是 native 极限函数

项目相对路径 `ImbalancedChen/P2TableActionSoundness.lean` 的命名空间仍为 `ImbalancedChen.P2TableActionSourceOnly`，其中定义：

```lean
def H (δ s : ℝ) : ℝ := wuImprovementLimit true δ s
def h (δ s : ℝ) : ℝ := wuImprovementLimit false δ s
```

这不是本次实际有限族上由 248/430 代递推定义的 count defect。该文件头注释明确保留 enhanced W1/W2 baseline、switched-cost licences、增强 stable-prefix uniformity，以及与 `wuSourceBox` 的族识别责任。

[固定项目源码：P2TableActionSoundness](https://github.com/UyNewNas/goldbach-formalization/blob/a929011ec95843553fc2e10b7291c8077e0952c0/ImbalancedChen/P2TableActionSoundness.lean)

`ImbalancedChen/P2HistoricSavedOrdinaryDefectAssembly.lean` 的 `BankEndpointLicences δ` 要求 200 个实际 lower-bank 端点与上述 native `h δ` 比较；低于 2 的端点不需 lower-h licence。

`docs/source-only/20261112-resume/t08/bank-next/successor-low-frontier/P2HistoricalLowTargetEdges.lean` 的 `original_bank_from_edges` 将其缩减为显式前提：

```lean
∀ i : Fin 200, i.val ∈ edges →
  readGain 247 i ≤ H δ (tableGrid (i.val + 1))
```

29 是现有实现给出的充分测试集，不是冻结稿直接声明的 29 个定理。`edges` 为：

```text
50,51,52,53,54,55,56,57,59,61,63,64,65,67,69,
71,73,74,75,77,79,81,83,84,85,87,89,94,99
```

[固定项目源码：BankEndpointLicences](https://github.com/UyNewNas/goldbach-formalization/blob/a929011ec95843553fc2e10b7291c8077e0952c0/ImbalancedChen/P2HistoricSavedOrdinaryDefectAssembly.lean)；[固定项目源码：29 项缩减](https://github.com/UyNewNas/goldbach-formalization/blob/a929011ec95843553fc2e10b7291c8077e0952c0/docs/source-only/20261112-resume/t08/bank-next/successor-low-frontier/P2HistoricalLowTargetEdges.lean)

## 2. native Wu 的对象与量词

原依赖为 `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`。

`research/wu2008/src/MathlibNt/Wu2008DoubleSieve/ImprovementFamilies.lean` 定义 `wuSourceBox k δ N i Δ V`，要求 `i≤k`、`Δ-1` 在 `log(N)^(-4)` 与其两倍之间、V 反单调、每槽 `V j≥N^(δ^(k+1))`，以及 `boxSquaredPrefixes (N^(1/2-δ)) V`。

`wuAdmissibleImprovements` 的顺序是固定 k、δ、s 后，选择阈值 N0，再对全部充分大偶数 N 和全部合法移动 `i,Δ,V` 给出 `wuImprovementComparison`。计数为 `wuBoxPhi`，归一化为 `boxTheta N (N^(1/2-δ))`。

`research/wu2008/src/MathlibNt/Wu2008DoubleSieve/ImprovementLimits.lean` 定义：先对 eventual improvements 取 supremum，再对深度取 infimum。`wuImprovementLimit_sub_mem` 只把极限值减去正 ε 后用于每个固定深度的全部 native boxes；它没有断言对增长深度有一个共同阈值。

因此，`g≤H δ s` 可供应每个固定深度下、阈值先于所有 moving boxes 的统一 count estimate；仅有若干固定实际族的估计，不能直接推出此命题。

[固定 native 定义：ImprovementFamilies 21–50](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/research/wu2008/src/MathlibNt/Wu2008DoubleSieve/ImprovementFamilies.lean#L21-L50)；[ImprovementLimits 17–24](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/research/wu2008/src/MathlibNt/Wu2008DoubleSieve/ImprovementLimits.lean#L17-L24)；[极限消费端 233–245](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/research/wu2008/src/MathlibNt/Wu2008DoubleSieve/ImprovementLimits.lean#L233-L245)

## 3. 冻结稿要求保留的对象

| 维度 | native Wu | 冻结稿实际有限族 |
|---|---|---|
| 总层级 | `Q=N^(1/2-δ)` | 实际共同 `Q=N^λ`，包括 `1/2<λ<153/256` |
| 族与阈值 | 每个深度下所有合法 moving boxes，阈值先于盒参数 | 先固定有限 admitted queries 与逼近，再令 N 增大 |
| 几何与历史 | native `boxSquaredPrefixes` | full/selected-complement squares、factorization branch、stable ceiling、原 labels |
| 归一化 | native `Q/d` | 实际 `Q/d`、原 marks 与重复 multiplicity |
| 所需缺陷语义 | native 全族的极限函数 | 数组逐代对实际 count 的合法上下缺陷 |

稿件在 `sv:finite-feedback` 中给出实际 finite positive marked family，在 `sv:finite-seed` 中要求相应准入与 comparison cutoff；`sv:feedback-error` 后先固定共同有限查询集再令 N 增大，并分别处理 positive-mass 与 zero-mass pieces。

[冻结稿：sieve-appendix 494–530](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L494-L530)；[seed 893–902](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L893-L902)；[共同查询集 1090–1101](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L1090-L1101)

## 4. 已有桥的实际范围与未付比较

`docs/source-only/20261112-resume/t08/bank-next/functional-license-next/review-r1/P2HistoricalFunctionalCommonSource.lean` 的 `common_native_source` 确实对所有 native boxes 给共同阈值，结论仍使用 native `firstGain` 及 `SecondFunctionalCoupledFeedback.cost/gain`；没有输出 enhanced-family 转换。

同目录父级的 `P2HistoricalW1NativeClipping.lean` 对 4 个不满足 native ratio gate 的参数使用 `s'=max(s,S/(S-2))`，保留 `firstFunctionalGainPsi δ s' S`。它没有自动支付原存储 base 到此 clipped base 的比较。

`P2HistoricalW2NativeFunctional.lean` 使用的 native W2 cost 含 `2/(1-2δ)*(omega3XIntegralEnvelope+jointSup)`。存储 action 的 K、Γ5 修复成本和分代重价尚需真实带符号比较；参数相同不等于费用相同。

同目录 `REPORT.md` 的“整行进入原吴极限仍缺的项目”明确保留：一般 W1 base、4 个 clipped 例的成本、W2 总成本与 singleton/pair 接线，以及 adopted `2327/100000` seed 在 native sourcebox 下的许可。

[固定项目源码：common_native_source](https://github.com/UyNewNas/goldbach-formalization/blob/a929011ec95843553fc2e10b7291c8077e0952c0/docs/source-only/20261112-resume/t08/bank-next/functional-license-next/review-r1/P2HistoricalFunctionalCommonSource.lean)；[固定 native W2 cost/gain](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/research/wu2008/src/MathlibNt/Wu2008DoubleSieve/SecondFunctionalCoupledFeedback.lean#L43-L78)

另有后续独立 classical 路线：`docs/source-only/20261123-yellow-node-owners/y09_w1w2_exceptions/ImbalancedChen/P2OriginalWuSeedAfterGoodPairs.lean` 的 `classical_seed_after_good_pairs` 在全部 native boxes 上给出

`5*(wuBoxPhi-(1-1/50)*Θ) ≤ testedFibreBalance+ε*Θ`。

这是实际推进，但右侧 signed debt 仍在；它没有输出 adopted seed、29 个 H247 licence 或 enhanced→native 转换。

## 5. 明确的不认同证据及 Binder 的终点

`docs/source-only/20261102-resume-30m/adopted_positive_seed/P2AdoptedSeedSourceBoundary.lean` 已有 `enhanced_level_gt_Wu/ne`、`enhanced_residual_gt_Wu`、`enhanced_cutoff_gt_Wu`、`true_alpha_changes_with_level` 等源码，记录同一 N、prefix、argument 下改变 Q 会严格改变层级、cutoff 和真实 α。

其 `Wu_coefficient_exceeds_adopted` 说明：较弱 Wu `1/5000` 上界经简单 cutoff 比较，留下的 reciprocal-log 系数仍大于 adopted `2327/100000` 所需系数。**这仅排除该简单转移，不排除独立证明 adopted seed。该文件为 SOURCE_ONLY，本文未确认其内核验收。**

[固定项目源码：P2AdoptedSeedSourceBoundary](https://github.com/UyNewNas/goldbach-formalization/blob/a929011ec95843553fc2e10b7291c8077e0952c0/docs/source-only/20261102-resume-30m/adopted_positive_seed/P2AdoptedSeedSourceBoundary.lean)

`ImbalancedChen/P2HistoricalSavedFloorFullBinder.lean` 的 `rowCompleteActualIntegral` 是 ordinary integral 加 guarded native-Wu-h integral；`checked_full_saved_total_actual_lower` 仍输入 `hbank`。文件头明确把实际 Wu 源族与 manuscript enhanced family 的识别留作独立责任。

因此，即使 29 条完成，直接解除的也只是该 native-Wu 积分 Binder 的对应条件，尚不能据此宣称增强实际母族或完整 P2.9 已闭合。

[固定项目源码：P2HistoricalSavedFloorFullBinder](https://github.com/UyNewNas/goldbach-formalization/blob/a929011ec95843553fc2e10b7291c8077e0952c0/ImbalancedChen/P2HistoricalSavedFloorFullBinder.lean)

本记录不改变既有定理、原 bank 数值、看板状态或证明目标。当前实际 Γ5 整数支撑／几何 Family 工作应继续服务于冻结稿原有限族的 count licences；native 普遍量词及其独立成本比较保持另列，不授予额外完成信用。
