# P3.1 下一步起点：复用硬频率尾供应者，接入同一 J 的实际源尾项

记录日期：2026-11-27。本文是只读源码与稿件定位报告，不新增 Lean 声明，也不代替编译、strict、kernel replay 或公理审计。

## 1. 固定基线与本轮边界

形式化仓库：`UyNewNas/goldbach-formalization`。本报告所依据的本轮固定源码提交是：

```text
6bad5965aad974d6187d36477948c8d6273e6281
```

其中已加入 `Part3ActualPositiveLatticeSmoothCore.lean`、`Part3ActualSmoothMassCompletion.lean`、`Part3ActualSmoothMassCommonLanes.lean`。root 已报告这三个模块的 strict 与 38 条环境声明预检通过；写作本报告时，固定提交的正式验收仍在 P1 队列。本文不把预检改写为固定提交正式验收。

这三个模块已经把原 `smoothMass`、`sixSmoothMass` 接到实际有限源的 common-J 分解。下轮无需重做 20 条恢复声明，也无需重做 actual completedPiece、zero-y/primary、共同正负 m 区间之间的有限恒等式。

冻结稿件：

- 仓库：`UyNewNas/chen-imbalanced-semiprimes`。
- 提交：`a988cba584d803ae2856a0de50efb582f4f3dd6a`。
- 路径：`paper/release-20261106/en/analytic-appendix.tex`。
- Git blob：`7cf3bbb16cd8924565eb439e474e0674f04631da`。
- SHA256：`e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`。
- 本地已核对副本：`/workspace/scratch/e5f883a2215a/reference/paper/release-20261106/en/analytic-appendix.tex`。

稿件定位：689–694 行为实际 b-Poisson 恒等式；695–699 行为 Poisson m=0 估计；700–703 行为共同截断及普通光滑 Fourier 衰减尾；705–727 行为归一化、共同 m 泛函及 cusp/packet；1040–1067 行给出谱 J/A 使用时的共同区间、共同相位、与谱高无关的 n 系数等限制。

## 2. 建议的下一项最小工作

**优先恢复已有硬频率尾证明，并将其接到当前 `poissonTail`、`tailKernel` 和 primary 源分解。** 对应稿件 700–703 行。这一步可以在不恢复完整 `OriginalData/FixedBlock` 的情况下推进。

现成源码已经证明参数统一的光滑频率衰减、硬窗口尾、有限 c 核尾及带权有限源尾。下轮的新增部分主要是当前窗口表示与旧窗口表示的识别，以及已有有限源恒等式的组合。不要重新从 Schwartz 衰减重写这套分析证明。

### 2.1 五份原源码的精确身份

下列路径均相对于 `UyNewNas/goldbach-formalization`。五个 blob 已逐个通过 GitHub connector 取回；本地完整副本均位于 `/workspace/scratch/e5f883a2215a/reference/ImbalancedChen/`。

| 原来源文件 | Git blob | 原文件 bytes |
|---|---|---:|
| `ImbalancedChen/Part3SmoothProgressionError.lean` | `292a7bddc202d6c4c3795de288b053df0b55ca5c` | 6591 |
| `ImbalancedChen/Part3PhysicalCompletedFrequencyDecay.lean` | `626e6417fbf7505307e958201f933b15eb672d82` | 3539 |
| `ImbalancedChen/Part3PhysicalHardSchwartzTail.lean` | `a32af63a6fc6d2ca67c35256b0c533214aef04a0` | 4670 |
| `ImbalancedChen/Part3PhysicalCommonHardFrequencyWindow.lean` | `a5d68cef6f7b9fded140b687e8de75f29b3239c4` | 4222 |
| `ImbalancedChen/Part3ActualCompletedHardTailMass.lean` | `b23e2e000301008244372e076411750ad4daa2bb` | 9910 |

原文件 SHA256，按上表顺序：

```text
e85a63019bab532bd2f34996e9e1e59e71def841bde54c8404a637ebb1b17b52
4d046d6513a6000cc49ba9e41d41a7b6a4c8c33f548449a862838b017d298bfb
3517d2bf683629a6c78463ec72730752fb558c847f39d684289105c056649f21
d47f2d762733d48c4c7702d970bb048782efe35a7a75e424c71ce4e796e39cfa
2c84a397d5620e43c3e845046e75c5d506ae3ba0e27e1baddd3fd71a0ce2e188
```

### 2.2 编译证据等级

`Part3SmoothProgressionError` 已被独立核实位于 P3.2 源码 `34201be0` 的 130-module provider 闭包。所核对正式报告的定位为：

```text
repository: UyNewNas/goldbach-formalization
ref: 30e2a96b601458d59116517ca478c496a68a39c9
path: docs/part3-distribution/node32-20261125/ci-34201be0/report.json
source_sha256: e85a63019bab532bd2f34996e9e1e59e71def841bde54c8404a637ebb1b17b52
olean_sha256: dc19446481153c5e394c9a32f0147ca2fdf3e6b982a4bc8b8e8d31c554032fab
```

因此它的等级是**已编译、源码与对象被冻结的 imported provider**，不是该次六个 strict/replay terminal 之一。

其余四份尾模块的原源码身份已验证，但它们未出现在本轮已经缓存的 P3.2 报告、P3.4 common-phase（源码 `97d5de82`）与 packet（源码 `145be87`）报告的选定 targets/source/object 绑定中。本轮没有 P3.5 的完整报告缓存，故只记录为**编译、strict、replay 状态未确认**；不声称从未编译。旧文件的 `SOURCE ONLY / UNCOMPILED` 头注释也不能单独作为当前验收状态证据。

### 2.3 最小恢复闭包与现有 owner

第一层只需 `Part3SmoothProgressionError` 中的以下六条原声明：

1. `poisson_decay_step`。
2. `poisson_decay_sum_range_le`。
3. `poisson_decay_summable_nat`。
4. `poisson_decay_tsum_nat_le`。
5. `poissonNonzeroDecay`。
6. `poissonNonzeroDecay_summable_tsum_le`。

随后复用以下三个物理模块的原证明：

- `Part3PhysicalCompletedFrequencyDecay`：`frequency_norm_rapidDecay`、`frequency_summable_norm`、`frequency_summable`。
- `Part3PhysicalHardSchwartzTail`：`hardOmitted`、`frequency_hard_window_tail`。
- `Part3PhysicalCommonHardFrequencyWindow`：`commonHardWindow`、其含零与窗外物理频率性质、`frequency_common_hard_window_tail`、`frequency_common_hard_window_tail_cap`。

如本轮推进至带权源，则再恢复 `Part3ActualCompletedHardTailMass` 的 `hardCompletedKernel`、`hardSourcePiece`、`sourceAbsMass`、`completedKernel_common_hard_tail`、`source_common_hard_tail`。这些是该原文件的前三个定义及前两个定理。最后两条只依赖通用完成核、有限源与频率尾，不需要其后 `actual_completedModePiece_common_hard_tail` 所使用的整套 actualMode 系数实现。

当前 owner 已有 `frequency`、`kloosterman_norm_le`、实际 Schwartz cutoff、`schwartz_norm_le_rapidDecay`、`completedKernel`、`Source`、`weight`、`output`、`carrier` 和 `weighted_pushforward`。应复用当前 owner；不要因原文件 import 列表较大而重新声明它们，或整体拉入旧 `ActualBetaNativeSource` / `ActualModeJointBetaPositiveCount` 闭包。

原 `sourceAbsMass_le_rawLabelBudget` 与 `actual_completedModePiece_common_hard_tail` 可作为后续供应者。当前最小尾接线不必提前恢复它们，更不能假定当前任意 `lambda`、`omega` 已满足那些 actualMode 范数结论。

## 3. 旧硬窗口与当前同一 J 的精确匹配

旧定义为：

```text
commonHardWindow C M R
  = Icc (-(ceil (10*C*R/M) : ℤ)) (ceil (10*C*R/M) : ℤ).
```

当前 `Part3OriginalCommonPoissonLanesCore.lean` 的 `mem_mWindow_iff` 给出 `m ∈ mWindow J ↔ m.natAbs ≤ J`，所以它与 `Icc (-J) J` 是同一个有限集。当前 c 外层载体为 `Ioc 0 (Nat.floor (10*C))`；这里的 10 必须保留。

对本轮六个 smooth scale pairs，假设 `B > 0`、`C > 0`、`R > 0`，统一选取：

\[
J=\left\lceil\frac{10CR}{B}\right\rceil.
\]

| 本轮 b-scale | 旧尾定理的 `(M, R)` 参数 | 窗口与界 |
|---|---|---|
| `B` | `(B, R)` | 窗口就是同一 `mWindow J` |
| `2*B` | `(2*B, 2*R)` | 窗口仍为同一 `mWindow J`；分母增大，尾界不超过第一行的界 |

`completedKernel_common_hard_tail` 对 c-smooth scale `N` 任意。因此分别令 `N = C, 2*C, 4*C`，不需要改变 c 外层载体或共同窗口。这里无需增加 `N > 0` 作为旧定理的额外前提。

旧 `Part3OriginalCommonPoissonLanes.lean` 中 `globalCutoff (D : OriginalData)` 的形状是 `ceil ((C/B)*x^epsilon)`，没有前面的 10；该原文件 blob 为 `00a797ac77cb444479ce097f4b44c56930489e32`。如果未来恢复这一原定义，可以令 `R = x^epsilon/10`，第二 b-scale 使用 `2*R`，严格匹配原 J。`x > 0` 保证该 R 为正；固定的 `10^(r-1)` 进入尾估计常数，无需改写原 cutoff。

上述结论针对固定 B、C 的同一族，尤其是本轮六项和同一实际源。若更外层的原族还包含不同的 B、C，仍需给出外层共同上界或有限最大值及其大小预算；本文不由这一步推断完整全族 cutoff 任务已闭合。

## 4. 当前接口上最小的组合工作：没有 keys.card 损失

旧定理 `frequency_hard_window_tail r hr` 先固定 `r ≥ 2` 及常数，随后对全部正尺度、正模数、残数、有限窗口给出绝对尾界。它保持原 `inverseResidue`，并且不需要 z 为单位。旧 `completedKernel_common_hard_tail` 与 `source_common_hard_tail` 将其提升为：

\[
\left\|\sum_{s\in U}w_s K_s-\operatorname{hardSourcePiece}(U)\right\|
\le \frac{A_rC^2}{R^{r-1}}\operatorname{sourceAbsMass}(U),
\qquad
\operatorname{sourceAbsMass}(U)=\sum_{s\in U}\|w_s\|.
\]

下轮应完成的是这些旧结论与当前尾表示之间的薄接线：

1. 用真实 summability 和 `sum_add_tsum_subtype_compl`，将当前 `poissonTail` 的补集 subtype tsum 识别为“全级数减硬窗口有限和”；再把这一等式有限提升到 `tailKernel`。
2. 现有 `Part3PrimaryDyadicAssembly.lean` 中的 `finite_source_assembly rho S F` 对任意 `F : Source → ℂ` 成立。取 `F s = weight lambda omega s * tailKernel J M N C a (output s)`。
3. 对每个 primary block 使用当前 `weighted_pushforward`。这样全部 primary tail 精确合并为 `nonzeroSource S` 上的一次带权尾求和，**不引入 `keys.card`，也不分别丢掉块间抵消后再求一个粗糙块数界**。
4. 调用旧 `source_common_hard_tail`，令 `U = nonzeroSource S`。当前 `zeroSource S` 的 y=0 项仍保留完整整数 m 核，与这个尾估计分开。
5. 六项分别调用三次 `(B,R)` 和三次 `(2*B,2*R)`，同一个 `A_r` 可用于全部六项。再用有限三角不等式，得到以下目标界：

\[
\left\|\text{六项 primary 尾之和}\right\|
\le \frac{6A_rC^2}{R^{r-1}}
\operatorname{sourceAbsMass}(\operatorname{nonzeroSource}S).
\]

这是下一轮可接的明确接口，本文没有把它写为已编译的新 Lean 定理。它只需要已有旧尾证明和上述集合、有限求和、尺度转换，不涉及新的谱输入。

## 5. 仍欠的全族误差预算

带有 `sourceAbsMass` 的统一尾界与最终可忽略误差不是同一结论。后续仍需：

- 对实际 lambda、omega 恢复或复用真实范数供应者；对当前任意函数参数不能直接假设范数不超过一。
- 如采用旧 `rawLabelBudget`，将实际有限源的绝对质量、标签数、F 窗口、T 载体及 H 界接入该预算。
- 对实际允许的外层参数族，控制 C 与上述预算相对于 x 的增长。
- 在这些控制之后，选择固定且足够大的衰减阶数，证明所需的 x 误差结论；保留常数与参数的量词顺序。

旧 `globalCutoff_covers` 只是 `Nat.le_ceil` 的覆盖事实，本身不是尾估计。六项有共同 J 的精确恒等式也不能代替以上预算。

## 6. OriginalData 与 FixedBlock：字段和原行的识别仍须真实来源

已取回的 `Part3OriginalCompletedReciprocalSource.lean` 原 blob 为：

```text
a99ba7e76f13c45beac5bd459334c9a75dc7c5a7
```

其 `OriginalData` 分别包含 `block : FixedBlock` 与 `atom : MediumAtom`，**没有 `atom = block.atom` 字段**。该原文件 57–67 行中的实际数据流是：

- `bScale`、`cScale`、`fScale`、残数读取 `D.block.atom`。
- `sCarrier`、`lambda` 读取 `D.atom` 及其原分解标签。
- `hBound` 读取 `D.block.H`；`omega` 读取 `D.block` 与 rectangle。
- `row` 是 `finiteReciprocalRow 1 D.block.atom.residue D.sCarrier D.hBound (D.lambda r) D.omega`。

原 `row_eq_completedBare`（77–83 行）通过真实原字典定理连接该行与 `completedBare`。原 `completedAmbientEnergy_le_smoothSix`（185 行起）还需要原 ambient carrier、正平滑 cover 及真实入口定义。

原 `original_six_eq_signed_joint_source`（278–289 行）已经是现成有限组合：展开 `smoothSix`/`row`，调用当前已恢复的 `sixSmoothMass_eq_completed`，再使用 `completedPiece_eq_three_joint_betas`。在保持原字段的情况下，这个有限组合不要求额外添加 `block.atom = atom`，不应重新实现其分析内容。

另一方面，当前 actual 路线的行读取 `g*l`、signed residue、`baseCarrier e (D/delta)`、`sharedSmoothFrequencyBound` 和 `scaleF`。要把这条路线直接认作某个 OriginalData 的行，必须识别整组模数参数、残数、carrier、H、F 和系数；即便额外给出两个 atom 相等，也不能自动解决所有这些差异。下轮不得用简化的替代 FixedBlock、未经证明的 atom 等式或默认行认同绕过真实源恢复。

## 7. 两种零项与谱 J/A 边界

### 7.1 y=0 不是 Poisson m=0

稿件 695–699 行估计的是 **Poisson m=0**，使用 Ramanujan/gcd 及 divisor 求和。旧 `Part3ActualCompletedZeroDifferencePayment.lean` 中的 `zeroPiece_norm_le` 支付的是 **原有限源 y=0**，不能把它当作 m=0 估计。当前新的 actual smooth-mass consumer 明确保留 y=0 的完整 m 核。

零频的 divisor 步骤须有实际 `a*y ≠ 0` 许可。非零源给出 y 非零；a 非零则须来自完整实际假设。`MediumAdmissible` 的残数下界与 `c0 > 0`、正 scale 可以给出此结论，完整 `RestrictedMediumObligation` 的外层已包含 `c0 > 0`。裸 `MediumAtom` 或当前有限恒等式不包含这个许可。这里尚须接上假设链，不能把 y 非零单独当成乘积非零。

### 7.2 原生谱数据与 J/A 仍是独立义务

当前 `Part3ActualLiteralPacketIntegral.lean` 中的 `P3ActualLiteralPacketIntegralSourceOnly.PacketData` 包含具体 rows、packet、carriers、正尺度、归一化支持和连续 kernel。`Part3ActualCommonCompletedInterface.lean` 的谱组合仍明确要求实际核的 `hkernel` 认同，以及对同一个纯 m-side 系数族、全部加性相位成立的 `full_uniform`。

因此实际谱 PacketData/核、Fourier 系数、Theorem J 的原生全相位输入、Theorem A 的 n-side 输入及谱高独立性，不能从硬尾或本轮有限恒等式推出。此处应复用各节点已有成果并按真实接口接线，不擅自新增稿外谱定理。

稿中 `(V,2V]` 与现有 dyadic `fullBlock` 的端点换算已有 `mem_fullBlock_iff_classical_interval`；当前 `commonMBlock` 与共同区间库的 `commonBlock` 也采用相同定义。不要把这些已完成的有限区间工作重新列为缺口。

## 8. 结论与执行限制

本次只读定位未发现新的实质性数学证明缺口。建议的最小下一步是恢复并验收真实旧硬尾证明，再接入当前同一 J 的 actual/primary 尾接口；它属于已有证明复用与形式化接口组合。真实原能量入口的识别、全族大小预算、m=0 支付及原生谱 J/A 仍分别开放。

本报告只保存定位与证据，不把五份旧源正文写入当前 proof 树，不新增 Lean 证明，也未运行 Lean、测试或云端任务。后续报告若给出正式验收编号，应另外绑定真实正式回执，不修改这里对写作时证据等级的说明。
