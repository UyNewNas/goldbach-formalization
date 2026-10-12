# Part 3 Prime AP distribution：独立源码审查

状态：**SOURCE_REVIEW_ONLY_NOT_COMPILED**。

本记录仅来自生产源码、共同源码中使用的定义以及 pinned 上游源码的只读核对。本审查没有运行 Lean，没有执行严格编译、生产对象内核重放或传递公理审计，也没有修改生产源码。以下“匹配”表示源码和数学对象匹配，不构成任何编译器确认或内核验收。依赖恢复及编译诊断仍以本批实际回执为准。

## 固定来源

- 被审查模块：`ImbalancedChen.Part3PrimeAPDistribution`。
- 被审查文件：`ImbalancedChen/Part3PrimeAPDistribution.lean`。
- 实际读取快照：`/workspace/scratch/535d89efd063/goldbach-formalization/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/Part3PrimeAPDistribution.lean`。
- 实际计算源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`。
- 已知交接提交：`f37f341412eb239f7e7e8937921ee8d01c9c2922`；该源的证明成果来自 `7d70a2545fd819706e473eb41e4d430ad19119d8`。
- 共同证明基线：`1a80c1bcce67886f699d097fc37fd245cd3620bf`。
- pinned goldbach-lean：`09b97db5764ade1246bfb77206baa1b124760958`。
- 工具链、数学定义、依赖版本和生产验证门均未由本审查修改。

## 十三条 theorem 的逐项匹配

源码共有十三条 `theorem` 和两个 `def`。这只是源码计数；未来所属声明公理审计应从实际环境枚举全部声明，包含 private/generated 声明，而不应把十三或十五硬编码成审计上限。

| 定理 | 源码位置 | 数学对象及证明检查 |
| --- | --- | --- |
| `part3_chenPrimeAPCount_eq_primesInAP` | 第30–32行 | 两侧都是包括上端点的真实素数 AP 计数。局部两次 filter 与上游素数条件和同余条件的合取 filter 一致，没有插入额外互素筛选。 |
| `part3PrimeAPError_eq_standard` | 第39–42行 | 只将余数规范化为 `a % d`；`Nat.ModEq` 与 `Nat.mod_mod` 支持该变换。陈述对任意自然数 `a,d` 成立，不偷偷增加 primitive 条件。 |
| `part3PrimeAPError_target_eq_chenQuotientPrimeAPError` | 第44–47行 | 取目标余数 `a=N` 后与实际 quotient 错误定义一致；两侧比较质量均为 `trueLogarithmicIntegral N`，`rfl` 合理。 |
| `part3_standardPrimeAPMaxError_le_prefix` | 第50–56行 | `Y≤N` 给出 `Y∈range(N+1)`；上游 prefix max 正好覆盖所有这些端点，包括零。 |
| `part3_abs_primeAPError_le_prefix` | 第60–68行 | 正模数和字面 primitive 余数经规范化进入上游 canonical unit-residue 最大值。 |
| `part3_abs_chenQuotientPrimeAPError_le_prefix` | 第72–77行 | 上一条的 `Y=a=N` 实例，实际需要的 `Coprime N d` 方向正确。 |
| `part3_sum_abs_primeAPError_le_prefix` | 第81–94行 | `S⊆Icc 1 D` 保证每个实际模数为正；扩大求和支撑时只添加非负 prefix-max 误差。 |
| `part3_abs_sum_mul_primeAPError_le_sum_abs` | 第98–108行 | 对实系数 `|w d|≤1` 使用有限三角不等式和逐项比较，没有额外支撑基数损失。 |
| `part3_sum_abs_primeAPError_log_saving` | 第113–132行 | 与 pinned 无条件 Standard BV 的参数及类型匹配。BV 的单一阈值先于所有支撑、端点、模数 cap 和移动余数选择器。 |
| `part3_abs_sum_mul_primeAPError_log_saving` | 第136–150行 | 在同一 BV 阈值之后再量化任意允许的实 signed 系数，系数不参与阈值选择。 |
| `part3PrimeAPIntervalError_eq_sub` | 第158–162行 | 区间误差精确等于上、下两个前缀误差之差；比较中心同样作差。 |
| `part3_abs_sum_mul_primeAPIntervalError_log_saving` | 第166–184行 | `L≤U≤N` 保证两个端点均由同一阈值控制。第181行的 `abs_sub _ _` 是正确的两项三角不等式，得到显式因子2。 |
| `part3_chenQuotientPrimeAPError_pool_log_saving` | 第188–203行 | 在 `(Icc 1 Q).filter (fun k => Nat.Coprime k N)` 上实例化普通 BV。`.symm` 正确把实际筛选转成 `Coprime N k`。 |

以上逐项源码审查未发现数学缺口，也未发现应当在取得真实编译诊断之前修改的确定 Lean API 错误。此结论不承诺严格编译、内核重放或传递公理审计将通过。

## pinned Standard BV 供应者及完整类型

本审查通过 GitHub 只读取得并核对以下固定版本源码：

1. [Bombieri1965Richert418Unconditional.lean](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/AnalyticNumberTheory/BombieriVinogradov/Bombieri1965Richert418Unconditional.lean)，Git blob `02a3e18aabdb7b64489b49adf32974c093703946`。
2. [Distribution/BombieriVinogradov.lean](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/Distribution/BombieriVinogradov.lean)，Git blob `6faba1a5e3b7807ed2948454666449398debfd02`。
3. [Bombieri1965Richert418.lean](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/AnalyticNumberTheory/BombieriVinogradov/Bombieri1965Richert418.lean)，Git blob `f8c80fd47fb992cf86f0d8861d41daf9450f2833`。

上游正常 theorem 的源码为：

```lean
namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem standardBombieriVinogradov :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  standardBombieriVinogradov_of_nonprincipalPrimitivePsi
    nonprincipalPrimitivePsiSiegelWalfiszSource

end AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
```

其返回 Prop 的完整展开定义如下。此处为 **pinned 源码提取类型，不是本次编译器确认类型**：

```lean
namespace MathlibNt.SieveTheory.BombieriVinogradov

open Real Finset Filter
open scoped Classical BigOperators

def StandardBombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, 2 ≤ N →
        ∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N B),
          standardPrimeAPPrefixMaxError N q ≤
            C * (N : ℝ) / Real.log N ^ A

end MathlibNt.SieveTheory.BombieriVinogradov
```

局部第121–132行对这个接口的消费顺序准确。上游所取用的 `standardBombieriVinogradov` 陈述没有待供 SW 参数；本记录没有据此声称已完成其依赖的对象绑定或传递公理检查。

## 实际中心与算术对象

上游 `primesInAP` 是：

```lean
def primesInAP (x q l : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card
```

其中心准确为

\[
\operatorname{trueLi}(x)
=\frac{2}{\log 2}+\int_2^x\frac{dt}{\log t}.
\]

这是 `LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) x`，不同于 Richert 无加法常数的 `integral_2^x`。单前缀误差不能描述为采用无常数的 Richert 积分；共同区间的两个中心相减时，该固定常数准确消去。

局部 `chenPrimeAPCount` 没有删去整除中心 `N` 的素数。其与 `chenQuotientPrimeAPError` 的连接是准确的，但实际 quotient 源的中心素数修正仍须在后续误差组装中保留。

## 统一阈值、模数范围与系数边界

局部共同区间估计的量词顺序为：

\[
\forall A>0\;\exists B\ge0\;\exists C>0\;
\forall^{\infty}N\;\forall Q,S,L,U,a,w\;(\cdots).
\]

这里 `B,C` 及 eventual 阈值不依赖阈值之后的区间、移动余数、支撑和系数。不是对每个固定参数分别取得阈值后声称同时一致。

准确适用范围如下：

- 完整物理模数 cap 为 `Q ≤ panModulusCutoff N B`，即 `floor(N^(1/2) / (log N)^B)`；它不是辅助因子分解范围。
- 算术序列为真实素数前缀或真实共同整数区间 `L < p ≤ U`。
- 端点为自然数，满足 `L≤U≤N`；本模块没有另外证明真实端点的 floor/ceil 转移。
- 余数选择器为 `a : ℕ → ℕ`，对实际模数逐一要求 `Nat.Coprime (a d) d`。
- 模数系数为 `w : ℕ → ℝ`，在实际支撑上满足 `|w d|≤1`。
- 素数变量中的加性相位为零。模数外部系数 `w d` 不能替代素数变量中的 `e(αp)`。
- 模数1由原定义正确覆盖；模数0不进入 BV 求和。

该模块不覆盖 `theta_* = 599/1000` 的高物理模数，不提供 prime-product source、packet 内部系数、rough 槽、任意加性相位、任意除数增长系数或其 Brun/Mellin 转移。普通 BV 中先逐项取绝对值的证明不能作为高模数 signed cancellation 的替身。

## 可疑 API 点的具体核对

- 第65行从上游 `unitResidues` 到局部 `finiteReducedResidues` 的 `change`：共同源码 `PanProductLiuBridge.finiteReducedResidues_eq_unitResidues` 由 `rfl` 证明，支持这里的定义一致性。
- 第55行 `Finset.le_max'`：pinned `Bombieri1965Richert418.lean` 的同类 prefix-max 证明具有相同调用形状。
- `Finset.abs_sum_le_sum_abs`、`Finset.sum_le_sum_of_subset_of_nonneg` 和 `abs_sub`：共同源码已有多处同形使用。
- 第181行现已使用 `abs_sub _ _`。它是本处需要的两项界，不应改回三点形式的 `abs_sub_le`。
- 以上是源码层面的 API 核对。具体 elaborator、严格 warning、导入对象兼容性问题只能由正常工具链实际诊断确认。

## 最小独立验收内容与接收范围

本批适合独立验收整个 `Part3PrimeAPDistribution` 定义模块，尤其是以下两个实际消费者入口：

1. `part3_abs_sum_mul_primeAPIntervalError_log_saving`：共同整数区间、移动 primitive 余数、允许的实 signed 模数系数。
2. `part3_chenQuotientPrimeAPError_pool_log_saving`：实际 quotient 误差池使用的普通 BV 供应者。

该验收不要求先编译 rough、medium 或 current-lower 候选模块。若目标所需的真实导入对象无法恢复，应记录缺少的最小依赖及实际诊断，不能把源码审查记成编译通过。

本模块可提供 Part 3、Part 4-B 和 Part 5 在上述普通 BV 范围内的输入；论文当前 `.599` 高模数主线以及实际策略的完整分布连接仍是独立未闭合工作，本记录没有将其描述成仅剩形式化翻译。
