# 原 U4 Gamma5 源到构造 Family 的接线

**状态：SOURCE_ONLY_UNCOMPILED；formal_credit = 0；kernel declaration credit = 0；endpoint credit = 0。**

本增量只有 `P2FiniteMarkedGamma5ActualFamily.lean`。它直接复用此前的实际 source rank 和 physical plateau，再把原整数元组放入本轮已构造的原 `P5Z.AdmissibleAllRankIntegerGeometricFamily.Family`。没有恢复、编译或重新核验旧 arithmetic-history 闭包；那一闭包的 1,526 个 native 候选仍未获得本轮资格化。本文件也不计入本轮轻量几何模块的内核声明数。

## 新增结论

`sourceIntegerPoint` 按已有 `slotEquiv` 保留原 old list、两个 fresh 槽和完整 `canonicalTail` 的每个出现次数。`sourceIntegerPoint_cast` 证明它的实数 cast 恰好是旧 `physicalToFin (sourcePhysicalPoint ...)`。重复素因子不合并，`m = 1` 的空 rough tail 不增加占位因子。

`originalSplitFamily k r n p t width` 使用已有 `geometricFamily`，取：

- `K = frozenSourceRankBound`；
- `a = frozenLeafCutoffFloor`；
- 全尺度函数 `logQ T = log (rootQ T n .U4 t p)`；
- 原固定宽度 `0 < width ≤ 1`；
- 原 cutoff `(T : ℝ) ^ frozenLeafCutoffFloor`。

这个构造器的数值拆分界 `k + 2 + r ≤ K` 只用于选择有限秩；真正的源定理 `enhanced_position_family_source_one` 不把该界交给调用者。它直接调用旧 `enhanced_position_source_rank` 得到此界，然后用 `geometricFamily_at_rank` 和旧 `enhanced_position_finPhysical_source_one` 得到构造 Family 的实际整数权重等于一。

主定理保留原 `LevelIndex`、`p`、`wordProduct`、`badLabels`、`roughNumbers` 和同一 root `Q`。所需原源条件是 `N ≥ 2`、`0 ≤ t ≤ 1/12`、`1/(n+1) ≤ 11/384`、`p ∈ originalBand N .U4` 及原 pair/rough membership。新几何 Family 只在 `scaleThreshold frozenLeafCutoffFloor ≤ N` 的共同大尺度分支上等于原 profile，因此主定理明确保留这个尺度条件。它独立于 marks、`n,p,t`、旧/尾秩和源元组。

## 量词顺序与使用范围

每个 Family 代表一个固定 old/tail 拆分，不代表整个带 marks 的算术聚合。正 marks 与 additive-prime、congruence 或 coprimality test 都留在几何权重外；本文件没有改写任何这些外部因子。

`originalSplitFamily_mixedEuler_uniform` 直接使用已有 `ambient_mixedEuler_budget`，保持以下量词顺序：

```text
固定 width > 0、width ≤ 1、导数阶 order
∃ C : ℕ, C > 0,
∀ n p k r t, ∀ hkr : k + 2 + r ≤ frozenSourceRankBound,
∀ T d Euler-word physical-point, ... ≤ C.
```

因此同一个 C 可用于在 T 确定后选择的 p；这里没有从逐 Family 的 `∃ C` 非法推出全族的 `∃ C`。这只是空间几何和 Euler 预算的统一性。它不允许直接把固定 finite queries 的 PP 分布结论扩张到任意移动的算术家族，也没有宣称构造了整个 U4 聚合的单一已获 PP 许可的 Family。

## 复用和验收边界

三个旧候选原样复用，未重写其证明：

| 模块 | 固定来源 |
|---|---|
| `P2FiniteMarkedGamma5ActualRank` | `docs/source-only/20261125-p2-actual-source-rank/ImbalancedChen/P2FiniteMarkedGamma5ActualRank.lean` |
| `P2FiniteMarkedGamma5SeedPlateau` | 同目录的 `P2FiniteMarkedGamma5SeedPlateau.lean` |
| `P2FiniteMarkedGamma5ActualPhysicalPlateau` | 同目录的 `P2FiniteMarkedGamma5ActualPhysicalPlateau.lean` |

新文件直接 import `P2FiniteMarkedGamma5GeometricFamily` 与 `P2FiniteMarkedGamma5ActualPhysicalPlateau`。后一项的旧 import 闭包尚未资格化。若以后完整加载该闭包，原 `P5AdmissibleAllRankIntegerGeometricFamily` owner 必须使用 `20261125-p2-9-geometric-family` 中与 `P2Gamma5AdmissibleFamilyCore` 配套的提取后版本，避免重复声明原同名 `Family`。本文件不引入另一份结构或同名 target。

本次新增只是实际源消费已构造 Family 的接线，属于稿内表达/接线问题。它没有证明 collar 普通质量趋零、原 Γ5 的积分成本上界、同 rho 的 PP/VM 分布、W1/W2 有向差额，因此不宣称 P2.9 已闭合。

现有 native Binder 所保留的 29 条 H247/native-Wu 实函数边界属于仍开放的充分条件/兼容性分支。当前尚未证明这 29 项是 1106 手稿实际增强 finite-family 结论的必要义务；二者的语义识别仍未完成。本记录将该分支与上述稿内主线的剩余义务分开。

1106 手稿定位沿用本轮独立核稿结果：固定 commit `a988cba584d803ae2856a0de50efb582f4f3dd6a` 下，`argument.tex` 的 `prop:current-positive-product`，`coefficient-appendix.tex` 的原 smooth labelled Family 条件，以及 `sieve-appendix.tex` 的 `sv:complete-fifth-region`、`sv:feedback-error`。本文件不把稿中正外包的省略描述当作已形式化的 collar 或分布供应。
