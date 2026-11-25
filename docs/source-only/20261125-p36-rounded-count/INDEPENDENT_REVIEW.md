# Independent review: actual rounded-output U5 count insertion

**结论：本次限定的源码与接口审查未发现阻断。** 这是一条有实际作用的有限计数连接：把已有 compiler 的 rounded 输出直接放回原 U5 算术源，并保留同一系数的精确互素均值、signed discrepancy 和 signed centre 修正。它没有得到数值密度下界或 PP 估计，也没有给旧 literal `selectedPolicy` 记入任何结果。

**状态仍为 SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE。** 本审查没有执行 Lean、kernel replay 或远程任务；源码推理与依赖预检不替代这些验收步骤。

## 绑定与范围

- 审查对象：`ImbalancedChen/P3OriginalU5RoundedCountInsertion.lean`，145 行，7,606 bytes，SHA-256 `6f1339f4a96390703b1d0b9f88d1abee46e764a287bb03ef7ea6b26ea6cd2935`。
- 主数学快照：`072863fe9c8cbef6c4dc1f5ce42cc5b7c18c6c8c`；只读 donor：`d6a9d76c56621992a8445c9628d4a2058db72eb6`。
- 稿件：`chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`；sieve appendix blob `bf8bae30ff18f21d716138af0cc6d9fbb4a80747`，coefficient appendix blob `10f3e2efb2074a9b97148a5151956e1d450be13f`。
- 同时审阅 `README.md`、`FREEZE.json`、`SOURCE_INDEX.json`、`PUBLIC_DECLARATIONS.json` 和 `DEPENDENCY_PREFLIGHT.json`。冻结列表及来源索引的 bytes、SHA-256、Git blob 均已从实际文件或固定 Git 对象独立重算匹配。

## 四个连接定理

| 定理 | 独立核对结果 |
| --- | --- |
| `rowEstimator_le_sifted` | 先用任意系数的 `quotient_sum_physicalDivisorSum` 将 estimator 还原为真实 quotient source 上的 divisor sum，再逐点应用已有 rounded `rho_minorant`。求和的权重为 1，故不需要错误的 `rho ≥ 0` 或 beta-minus 非负假设。 |
| `rowEstimator_eq_exact_mean_and_signed` | 直接使用 `finitePrimitiveDiscrepancy = finiteCongruenceMass − finiteCoprimeMass / φ`。单位权 congruence mass 恰为 `chenPrimeAPCount`；分配律后为 `E = M + D − C`，centre 的负号正确。 |
| `original_U5_rounded_count_lower` | 对原 `pairSupport N` 逐行求和，再用 `currentChenUpsilon5_eq_siftedQuotientPrimeSource`。没有把外部标签映成不带 multiplicity 的物理模数集合。 |
| `original_U5_rounded_exact_mean_lower` | 仅把上一行的不等式按精确 row identity 展开、分配有限和；没有增加最终 count、density、admission 或 PP 前提。 |

### 系数与方向

`roundedSupport` 和 `roundedRho` 分别是现有 `P2LowerFiniteCellBetaCompiler.support`、`.rho` 的原参数实例。小 cutoff、总 cutoff、small level 正是旧 U5 选择；`tau` 只传给既有 rounding。`attachment_gates` 从 `2 ≤ N`、`0 < epsilon < 1/8` 得到 minorant 所需三个 gate，`Nat.le_ceil` 给出实 cutoff 到自然 cap 的边界。没有把 rounded 输出识别为某个 raw policy 的 rho，也没有调用 raw-policy 的 `∀ P` count 来代替这个连接。

上游 compiler 的实际符号规则仍为：rough coefficient 非负时接 beta-minus，负时接 beta-plus；它的 `rho_minorant` 由 signed attachment 和 rough minorant 推出。本候选直接复用该结果，没有对 signed 系数乘不等式，因而没有改变 lower 方向。`tau` 任取实数对于这条有限代数结论无碍；正 mesh 的几何用途不由此得到。

### 原算术源、标记与 multiplicity

`markedProduct t = t.1 * t.2`，`fullModulus t k = (t.1 * t.2) * k`；原 ordered pair 始终保留在外层。小/rough 分解的唯一性属于已有 compiler，本候选没有另建分解或除以 multiplicity。

旧 `chenQuotientPrimeCarrier` 仍从 `chenAdditivePrimeCarrier N` 出发并筛选 `b ∣ N − P`。其 quotient image 的注入性已有证明；`chenQuotientPrimeSource_data` 保留正性与对 N 的互素性。`chenSiftedQuotientPrimeSource_eq_coprime_filter` 使用的正是这些事实，故新稿用 sieve product 的 coprime filter 时没有漏掉 target-coprimality mask。旧 Fubini 中的 `AP − Centre` 保留排除 centre divisors 的修正。

minorant 输入为 `(q : ℤ)`，输出上的 `Int.natAbs_natCast` 精确回到自然数 q；没有把有符号 receiver 直接当自然数或遗漏负值分支。行定理可以对任意 t 成立；最终 U5 定理仍只求和真实 selector，不从这个较强的有限行入口推出全 family 几何结论。

### 精确均值与 centre

`rowExactMean` 的分子是完整的 `finiteCoprimeMass (chenPrimePrefix N) (fun _ => 1) (fullModulus t k)`，分母是同一 full modulus 的 totient。它没有换成总 prime mass、`li(N)`，也没有未经证明将 totient 拆成两个因子。模数素因子造成的质量差异已经保留在这个分子中，没有静默丢弃 modulus-prime correction。

`rowSignedPrimitive` 用同一 prime prefix、residue N、full modulus 和 rounded rho；`rowSignedCentre` 同样保留 signed rho，且计数的是原 `P ∣ N` 的 AP 子集。centre 修正只在 `E = M + D − C` 中减去一次。本稿没有把它改成无符号成本或宣称其小。`finitePrimitiveDiscrepancy` 的原定义允许一般 residue 与 totalized division；这个纯有限恒等式本身不等于获得 primitive-residue distribution 的适用条件。

## 去重、预检与公开范围

在指定 main/donor 的 U5、quotient、finite-cell compiler 与 primitive-discrepancy 接口中，未发现已有直接的 rounded-output U5 count 入口。现成的通用 Fubini、真实 rho minorant 与原 count dictionary 均被直接调用；原 raw causal count 的 displayed coefficient 不同，不能只改名称套用。新稿没有重写树算法、beta attachment 或 quotient 注入性。

从每个选定源码的实际 import 独立递归核对得到 **146 个项目模块 = 143 个 main 源码 + 2 个 donor 源码 + 1 个新候选**，无缺失、无 import cycle、无多余来源记录；**98 个显式外部 import** 与预检清单完全一致，均已在固定主 manifest 的 external inventory 内。主 selected manifest 外恰为新候选、两个 donor finite-cell 模块，以及已经存在的 `UpperCoefficientPerturbation`。所有 146 条选源记录的字节与哈希均匹配。这是 source selection 核对，不是缓存对象复用许可。

源码公开列表确为 **2 abbrev、4 def、4 theorem**。对候选和两个 donor 新引入文件去除注释后，未见 `sorry`、`admit`、`axiom`、`unsafe`、`implemented_by`、`extern` 或 `run_tac`。此文本检查不代替完整的 elaborated defining-module/type/transitive-axiom 审计。

README 的范围说明与声明相符：这里只接通 sieve appendix `sv:physical-lower` 中 pointwise lower polynomial 到原有限 count 的算术步骤，并遵守 coefficient appendix 的同系数 exact coprime mean 要求。所需增强 U5 density 识别、rounding/beta loss 支付、signed centre 支付、整 external-pair/residual word 的 atom/tensor、physical cap、common Q、admission 和 PP 均仍待供应。

## 后续验收边界

本静态审查无需作者改动候选。若集成，应重新绑定当时的完整 source selection，并完成 fresh strict owned compile、bundled official leanchecker replay、完整 defining-module 声明及类型 inventory，以及 transitive axioms 仅限 `propext`、`Classical.choice`、`Quot.sound` 的检查。候选、两个 source-only donor 接口及其实际依赖的编译兼容性尚未由本报告验收。

本次唯一写入为此独立报告；未修改候选、freeze、canonical source、主 manifest 或 targets，未 stage、commit 或更新看板。
