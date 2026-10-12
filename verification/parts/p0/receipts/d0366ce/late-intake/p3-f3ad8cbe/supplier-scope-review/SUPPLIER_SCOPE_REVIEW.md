# P3 素数 AP 供应接口独立源码审查

## 接收结论与证据身份

固定交接 `f3ad8cbe43c61c903857c7411626ee8c56f4f2f9` 中，`ImbalancedChen/Part3PrimeAPDistribution.lean` 的源码范围确为 **13 个 theorem 与 2 个 def**。这 15 项是源码声明数，不能替代编译后包含私有／生成声明的环境清单。

该文件提供的候选范围是：**真实素数 AP 计数、归一化真实对数积分中心、普通 BV 的完整物理模数截断、同一 eventual 阈值后的公共端点／区间、随模数变化的 primitive 余数，以及绝对值至多 1 的实权重。** 没有从这些接口推出手稿所需的高模数素数乘积分布、加法相位估计或同一实际 `rho` 的完整上下界。

目标源码 9873 字节，SHA-256：

```text
55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc
```

Git blob 为 `2d761133b313302ab3a89ae906eb6944037a093d`。锁定上游 goldbach 提交为 `09b97db5764ade1246bfb77206baa1b124760958`。

本审查只读本地固定源码、来源清单与已有交接状态；未运行 Lean、CI、内核重放、公理检查或网络访问。额外的三个项目定义源通过本地 `git show f3ad8cbe…:路径` 读取，副本只写入本审查目录，没有变更 Git refs 或仓库。

**下列代码块和 `SOURCE_DECLARATIONS_ONLY.json` 均为源码提取陈述，不是编译器确认类型。** 已有 P3 回执仍是 `BLOCKED_MISSING_IMPORT_OBJECTS`，目标声明 elaboration 未开始、目标对象未产生；本审查没有升级其验证状态。

## 上游 theorem 与 Prop 的精确关系

固定 `Bombieri1965Richert418Unconditional.lean` 中的生产者是一个 theorem：

```lean
theorem standardBombieriVinogradov :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  standardBombieriVinogradov_of_nonprincipalPrimitivePsi
    nonprincipalPrimitivePsiSiegelWalfiszSource
```

它的类型是由另一个固定源定义的命题：

```lean
def StandardBombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, 2 ≤ N →
        ∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N B),
          standardPrimeAPPrefixMaxError N q ≤
            C * (N : ℝ) / Real.log N ^ A
```

因此 P3 中 `standardBombieriVinogradov A hA` 在源码接口层是展开这个命题类型后应用 theorem 的证明项，并非将一个 `def … : Prop` 当成已证结论。P3 没有新增 `hBV : StandardBombieriVinogradov` 参数。上游源中可见的生产证明链也不是以一个额外分布命题作为此 theorem 的参数。

这一源码观察不能替代完整上游导入闭包的严格编译、内核重放与传递公理审计；本次没有执行这些验证。

## 截断与真实 li：已读实际定义

原先提供的四个上游文件没有包含 `panModulusCutoff` 的定义。补读固定提交的两份实际定义源后，定义已确定，无须依据注释推断。

### 完整物理模数截断

在 `MathlibNt/SieveTheory/Liu/LogarithmicIntegral/LiuTrueLiPan.lean` 第 91–92 行：

```lean
noncomputable def panModulusCutoff (N : ℕ) (B : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B)
```

该定义位于 `MathlibNt.SieveTheory.LiuWeight` namespace。P3 第 26 行的 `open … (panModulusCutoff)` 只是引入此名称，不创建另一种定义或改变截断。BV 命题中的 `LiuWeight.panModulusCutoff` 和 P3 的短名指向同一个定义。

所以 `Q ≤ panModulusCutoff N B` 约束的是求和中完整的物理模数，公式为

\[
Q\le \left\lfloor\frac{N^{1/2}}{(\log N)^B}\right\rfloor.
\]

不能用某个辅助因子 `b` 或 `d` 分别满足的界，代替实际模数 `b*d` 满足这个界。

### 主项的精确归一化

固定 `MathlibNt/SieveTheory/Arithmetic/LiuLogarithmicIntegral.lean` 第 22–23 行：

```lean
noncomputable def liuLogarithmicIntegral (κ x : ℝ) : ℝ :=
  κ + ∫ t in (2 : ℝ)..x, 1 / Real.log t
```

固定 BV 定义源中：

```lean
noncomputable def trueLogarithmicIntegral (x : ℝ) : ℝ :=
  LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) x
```

实际中心因而是

\[
\operatorname{li}_{\mathrm{norm}}(x)
=\frac{2}{\log 2}+\int_2^x\frac{dt}{\log t}.
\]

它不是 `x / log x` 代理，也没有把加法常数省略。单前缀误差使用这个完整中心；区间误差使用两个完整中心的差，故该固定加法常数在相减时消去。若后续要改变单前缀的 li 归一化，仍需显式保留或估计相应误差。

## 真实计数、余数和权重

同一固定项目提交的 `ChenInitialPrimeSource.lean` 定义：

```lean
def chenPrimePrefix (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

def chenPrimeAPCount (N a d : ℕ) : ℝ :=
  (((chenPrimePrefix N).filter (fun P => Nat.ModEq d P a)).card : ℝ)
```

这是真实的 `p ≤ N` 素数计数，没有在计数定义内添加与 `N` 或 `d` 的互素掩码。上游 `primesInAP` 同样是 `range (x+1)` 上的素数与同余条件合取；局部参数顺序为 `(Y,a,d)`，上游为 `(Y,d,a)`，P3 的等式正确调整了顺序。

`part3PrimeAPError_eq_standard` 只将余数化为 `a % d`。进入 BV 最大误差时才显式要求 `0 < d` 与 `Nat.Coprime a d`。本地 `finiteReducedResidues d` 的实际定义为 `(Finset.range d).filter (fun a => Nat.Coprime a d)`；同一固定项目源的 `finiteReducedResidues_eq_unitResidues` 使用 `rfl` 给出与供应者表示一致的源码桥。模数 1 的代表为 0；模数 0 不在最终 `Icc 1 Q` 求和中。

有符号权重是 `w : ℕ → ℝ`，只要求 `∀ d ∈ S, |w d| ≤ 1`，无需正性，也无需在 `S` 外有界。它乘在每个模数的完整 AP 误差外。三角不等式加逐项绝对值界不会产生 `S.card` 因子。它没有证明随素数变量变化的权重或相位，也不能直接用于 `3^ω(d)` 等可能超过 1 的模数权重。

## 全部源码声明范围

下表仅列短名；namespace 均为 `ImbalancedChen`。完整源码头保存在 `SOURCE_DECLARATIONS_ONLY.json`，每条都标记 `compiler_confirmed=false`。

| 种类 | 源码声明 | 精确范围与主要输入 |
| --- | --- | --- |
| theorem | `part3_chenPrimeAPCount_eq_primesInAP` | 全部自然数 `Y,a,d` 的真实 inclusive 计数恒等式 |
| def | `part3PrimeAPError` | `chenPrimeAPCount Y a d - trueLogarithmicIntegral Y / φ(d)` |
| theorem | `part3PrimeAPError_eq_standard` | 全部自然数参数；规范化 `a % d`，无额外 primitive 假设 |
| theorem | `part3PrimeAPError_target_eq_chenQuotientPrimeAPError` | `Y=a=N` 与比较质量精确取真实 li 的 quotient 错误相同 |
| theorem | `part3_standardPrimeAPMaxError_le_prefix` | `Y ≤ N`，将该端点 residue max 放入同一 `N` 的 prefix max |
| theorem | `part3_abs_primeAPError_le_prefix` | `Y ≤ N`、`0 < d`、`Coprime a d`；余数可独立于端点 |
| theorem | `part3_abs_chenQuotientPrimeAPError_le_prefix` | `0 < d`、`Coprime N d`，目标余数为 `N` |
| theorem | `part3_sum_abs_primeAPError_le_prefix` | `S ⊆ Icc 1 D`、公共 `Y ≤ N`、逐模数 primitive 余数 `a d` |
| theorem | `part3_abs_sum_mul_primeAPError_le_sum_abs` | 有限 `S` 上 `|w d|≤1` 的模数权重三角界 |
| theorem | `part3_sum_abs_primeAPError_log_saving` | 同一 ordinary-BV 阈值后的所有 `Q,S,Y,a`；真实物理 cap |
| theorem | `part3_abs_sum_mul_primeAPError_log_saving` | 同上，继续统一于所有有界实权重 `w` |
| def | `part3PrimeAPIntervalError` | 上、下 inclusive 计数与真实 li 中心分别相减 |
| theorem | `part3PrimeAPIntervalError_eq_sub` | 全部 `L,U,a,d` 的代数恒等式，不需要排序假设 |
| theorem | `part3_abs_sum_mul_primeAPIntervalError_log_saving` | 公共区间 `L < p ≤ U`，`L≤U≤N`；显式系数 2 |
| theorem | `part3_chenQuotientPrimeAPError_pool_log_saving` | `k ∈ Icc 1 Q` 且 `Coprime k N` 的实际目标-`N` 误差池 |

## 统一阈值与区间系数 2

单前缀有权界的量词顺序是：

```lean
theorem part3_abs_sum_mul_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A
```

`B,C` 与 eventual 阈值在 `Q,S,Y,a,w` 之前选择。因而同一个足够大的 `N` 可以容纳这些后续选择，包括依赖 `N` 的余数选择与权重。P3 用 `filter_upwards [hBV, eventually_ge_atTop 2]` 把上游显式的 `2≤N` 条件并入这一个 eventual 阈值。

这里的 `Y` 对同一次模数求和是公共端点；源码没有给出 `Y(d)` 的直接接口。区间版本同样使用公共 `L,U`，只把余数与权重作为模数函数。

区间误差的实际定义为：

```lean
def part3PrimeAPIntervalError (L U a d : ℕ) : ℝ :=
  (chenPrimeAPCount U a d - chenPrimeAPCount L a d) -
    (trueLogarithmicIntegral U - trueLogarithmicIntegral L) / (Nat.totient d : ℝ)
```

有序端点条件 `L≤U≤N` 下，计数差对应 `L<p≤U`。源码先将此误差精确改写为两个前缀误差之差，再对相同 `B,C,N` 使用上、下两个端点界，得到

```lean
|∑ d ∈ S, w d * part3PrimeAPIntervalError L U (a d) d| ≤
  2 * (C * (N : ℝ) / Real.log (N : ℝ) ^ A)
```

系数 2 因此有明确来源；不能在交接中省去。

## 尚未闭合的输入与接收 Part

| 接收方 | 本候选可提供的接口 | 后续仍须真实供应的输入 |
| --- | --- | --- |
| Part 0／Part 3 | 15 项源码候选、固定真实 li／cap、普通 BV 适配范围 | 目标严格编译、目标原装内核重放、完整 defining-module 传递公理审计；当前缺对象状态不因源码审查而改变 |
| Part 1 | 实际选择后可尝试实例化的有限 `S`、移动余数与权重接口 | 同一实际构造的物理模数 cap、primitive 余数、`|w|≤1`、公共端点／区间与实际计数恒等式；不得用辅助因子范围替换完整模数范围 |
| Part 4-A／Part 4-B | 普通 BV 范围内可复用的素数 AP 误差候选 | 高物理模数及素数乘积源分布、加法相位估计、选盒实际 `rho` 的误差组装、真实解析 `K` 与完整 `hUpper` |
| Part 5 | 原始 quotient 错误池的普通 BV 候选 | 完整 Chen 均值所需的实际源／权／质量与归一化桥、所有余项、真实解析 `c` 与 `hLower`；对同一实际 `rho` 的密度供应仍来自 Part 4-A，无须等待 Part 4-B |

特别是，已有 `ChenQuotientSieveRemainders.lean` 的真实余项恒等式仍含：

```lean
chenQuotientPrimeAPError N M (b * d) -
  chenQuotientPrimeAPError N M b / (Nat.totient d : ℝ) +
  chenQuotientCentreCorrection N b d
```

本候选实例化的是 `M = trueLogarithmicIntegral N` 的普通 AP 误差池。它没有取消中心素数修正，没有为真实筛余项自动证明所有系数界，也没有自动保证每个完整模数 `b*d` 都处于 BV 截断内。高模数、乘积源和相位方面的缺口不能包装成新结构或类型类后称为已闭合。

## 附件

- `SOURCE_DECLARATIONS_ONLY.json`：13 theorem／2 def 的全部源码头，显式标记未经编译器确认。
- `SCOPE_INPUTS.json`：目标、固定上游实际定义源与三个补读项目源的字节、SHA-256 和 Git blob 身份；这只是源码身份核对。
- `project-fixed-source/`：从完整固定项目 SHA 只读取得的实际计数、余数与局部 supplier bridge 源文件。

所有本次新增内容均在 `supplier-scope-review/` 内；没有增加 production 源码、根导入或接收声明数。
