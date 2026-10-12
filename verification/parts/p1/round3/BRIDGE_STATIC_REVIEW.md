# Part 1：第五层 saving bridge 静态独立审阅

## 范围与源码身份

审阅者：`/root/bridge_review`。本记录对应以下两份源码；审阅开始、结束及写入记录前复核的 SHA-256 相同。

| 源码 | SHA-256 |
| --- | --- |
| `ImbalancedChen/ActualHistoricalFifthSavingIntegral.lean` | `8788d1706f24136a6279e9d0336866e68355134d5a2109c3900c32d62382b31c` |
| `ImbalancedChen/HistoricalFifthCutoffInvariance.lean` | `abe06826e099ec0beb73329c1c887fc5aeca0583efe1ff46c3b92ec91d9cdb3d` |

审阅只读取这两个模块及相关现有定义、供应定理和证明。未运行 Lean、frontend、检查器或运行时队列，未修改任何 Lean 源码。本文件是静态审阅记录，不是编译回执、kernel 检查结果或公理 census。

**静态结论：未发现必须修复的系数、方向、历史归属或截断语义错误。** 下述判断仍须由与相同源码绑定的真实验证接续。

## 实际权重、归一化与差值方向

`FirstExitHistoricalLevels.lean` 中 `actualHistoricalFifthSaving` 的原定义使用完整候选历史的实际权重：

```lean
(candidate.selectedPrefix.map
  (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod
```

权重乘以新第五层 gated lower residual 减去旧第四祖先 gated lower residual。新 bridge 原样使用该权重，经 `actualPrimeFrontier_candidates_weighted_sum_eq_tuple_sum` 重排为 tuple 的 `∏ i, 1 / ((p i : ℝ) - 1)`；第五个素数因子保留。

`ActualOwnCubeTupleDictionary.lean` 的字典分别归一化旧、新 residual。`ActualHistoricalFifthCellIntegral.lean` 中 `fifthTupleOwnCubeDifference` 和 `fifthPrimeCorrection` 已含 residual 的 `Real.log (N : ℝ) / singularSeries N`，因此 bridge 外侧恰好归一化一次。`List.sum_map_mul_right` 与 `ring` 的用法和当前引理类型相符，不需要约去归一化因子。

原有限恒等式的方向是 fourth policy retained polynomial 减去 fifth policy retained polynomial，等于正的前缀乘积权重乘以“新 lower residual 减旧 lower residual”。新模块维持此方向，没有从 saving 的名称推断有限差值非负。

## 有效祖先与分别保留的 own cube

`HistoricalPrefixCertificate.lean` 的历史反向存储；`rosserAncestor 4 history` 经 `primeHistoryLogCoordinates_eq_historicalPrefixProject` 对应处理顺序 tuple 的前四个坐标。新 bridge 的旧 residual 使用

```lean
D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)
```

新 residual 使用 `D.exponent5 t`。旧第四层未选中时继续继承有效第三祖先；第五层未选中时继承这一完整第四历史。

`upperFourthToFifthSaving_eq` 从实际 rank-four frontier 的长度与 `levelCheck` 推出第三至第四的比较；对真实候选 `q :: frontier.selectedPrefix`，再恢复其第四祖先并推出第四至第五的比较。候选来自原第三层 capped rank-four parent。第四 level 及旧第五 own cube 未被加入候选枚举过滤。

`ActualFrozenOwnCubeDensity.lean` 与 `ActualPrimeBoxOwnCubeResidual.lean` 的两个严格条件分别保留：`P * p₄^2 < N^lambdaNew` 和 `P * p₄^2 < N^lambdaOld`。两侧使用同一实际自然数乘积、最后选中素数及各自的 quotient level。旧门拒绝而新门接受的候选仍被计入。

## Arbitrary cutoff、同一 cap 与极限

任意 `z` 的 saving-to-tuple 恒等式仅进行有限字典与枚举重排，因此没有增加 `N > 1`、cap 覆盖或解析假设。

owned-cell cutoff 定理在 `1 < N`、`a < b`、`N^b ≤ z` 下，把 cell 内的严格 `tᵢ < b` 转回 `pᵢ < N^b`。`FirstExitFrontierTupleReindex.lean` 的实际 membership 保留严格 `pᵢ < cap`、素性、`pᵢ ∤ N`、排序及完整 proper-parent validity。只改变 outer cutoff，目标、cap、parent 和 residual 均保持相同。

该有限恒等式不要求 `N^b ≤ cap`：不足 cap 时两侧仍是相同截断。cap 覆盖用于后续积分极限；移动 outer cutoff 版本另有独立的 eventual `N^b ≤ z N`。所有极限固定 `D`，并沿正偶数 `N → ∞` 使用 `0 < D.a`、`D.a < D.b`、`0 < D.old`、`D.levelCheck = true`。ceil 版本由 `Nat.le_ceil` 提供覆盖。

## 实际离散边界支付

有限 cell 分解和 cutoff 恒等式使用原 Ico 唯一归属，包含内部网格面上的实际素数，不使用零测删除离散原子。

积分 transport 复用 `ActualPrimeIcoCellTestFunctions.lean` 中对每个点成立的 `affineSandwich_test_error`。该误差乘以实际非负素数权重后控制实际有限和，包括墙上的原子。连续 null-wall 结论仅作用于连续积分；`ActualPrimeOwnCubeIcoIntegral.lean` 随后把此 Ico/affine-gate 极限与实际 gated residual 的 uniform error 组合。基础实际倒素数质量误差还由 `ActualPrimeReciprocalMass.lean` 的有限 window 比较支付目标整除排除、权重变更与端点误差。

这条依赖链没有断言有限 `N` 的实际边界质量为零，也未提供全构造的显式数值边界预算。

## 三个接收与使用限制

1. **有限历史比较不是完整许可。** `levelCheck` 只检查所选有限 cell 的 level 比较。实际 adopted table、有效祖先绑定、平方/包络许可、支持、因子分解及最终 K/c 仍是独立输入；不能由这个 Bool 推出。
2. **完整 cutoff 恒等式目前在归一化层。** `fifthOwnCubeDifference_outside` 已给出未归一化的点态 fallback 零差，但本模块未声明未归一化完整 saving 的 cutoff 恒等式。不得无条件约去 `log N / singularSeries N` 强化结论。
3. **同一 cap 和固定数据是实质条件。** outer-cutoff invariance 不允许更换 residual cap；它也不处理不足 cap 的积分极限、floor、随 `N` 改变的 mesh/table，或两个完整 policy 各自的密度极限。

上述核对未产生必须修改的源码建议。实际 frontend、原检查器及 defining-module census 的状态应从各自真实回执单独接收。
