# P1.5 两个原始历史计数的修正项归约

`exists_original_count_distributions` 将两个中心化计数分别归约到各自的原符号和 `Σ (mediumAtlas + remainingTypeIAtlas)`，每个差的范数上界为 `u * singularNormalization N`。比较项的策略顺序为 `(S false, R false)`，节省项为 `(eight false, six false)`。两项共用历史选择及充分大偶数阈值，保留各自的接收器、`primeMass N` 乘原密度均值、原移动剩余类及 `remainingModuli` 上的真实 Δρ。[Lean 源码](../../../source-only/20261126/p1-historical-atlas-correction-reduction/P1OriginalHistoricalAtlasCorrectionReduction.lean)

| 预算 | 已有证明及实例化 |
| --- | --- |
| `u/2` | 归档的 `exists_original_count_remainders` 在两个原计数上提供同一组历史选择。它先用 `noMedium_exact_partition` 拆出单长和，用实际 `eventually_actual_sourceChannel` 估计该和，粗素数项由原逐图零和消去。该步骤保留 `1 ≤ K` 以及 `0 < zeta ≤ 1/20000`。 |
| `u/4` | 原 trim 定理对原模数族和真实 Δρ 取 `kap0 = kap`、许可阶数 6。平方自由给出模数正性，严格上截断 `d < N^(599/1000)` 和 `N ≥ 2` 给出 `Q ⊆ Icc 1 N`。 |
| `u/4` | 原 proper-power 定理在同一模数族、同一系数、同一许可和图表顺序上估计整项和。两个支付均使用 `trueDDeltaRho_abs_le_one`。 |

带符号恒等式为 `retainedAtlas − distributionAtlas = trimReserve − Σ properPowerReserve`。新证明相交上述阈值，保持 `∃ B ≥ 0` 在固定 `kap,zeta,K` 之前，保留三个遗漏预算及选择次序。两项存留的原符号分布估计与 P1.5 最终闭合仍待证明。

**核验状态为 source-only。** 候选保存在 source-only 目录。待历史 OneLong 依赖正式采用且递归导入核验通过后，再将其安装为标准模块。新文件的第一个 import 可追溯到已发布的归档源码。在本次绑定基线中，该文件缺少标准模块路径，递归安装边界沿用旧的来源登记。本轮只核对字节、声明文本与调用，无 Lean elaboration、内核回放或证书。[机器可读绑定](SOURCE_REVIEW.json) · [原单长归约及其输入](../../../source-only/20261125-p15-historical-onelong/SOURCE_BINDINGS.json) · [已有来源核对](../../20261125/p15-actual-means/history-source-recovery/SOURCE_INDEX.json)
