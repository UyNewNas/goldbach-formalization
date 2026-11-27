# P3.1：共同硬频率尾之后的最近一步

日期：2026-11-27。只读定位；不修改本轮六个冻结模块，不添加 Lean 声明，不运行编译或远端任务。

本次检查的当前仓库是 `/workspace/scratch/e4b706aea1e3/goldbach-p31-closure-20261127`；检查时 HEAD 为 `092d7b48f470c2733308853e5ec42bf46463fc3c`，本轮新增消费者的最终工作树源码为 `ImbalancedChen/Part3ActualSmoothMassTruncation.lean`，SHA256 `69265f34ffe404c61dae853d325dd939b0e2b7836f2c954e2887a1eefedaf57b`。本文件不替代主任务对新源码固定提交的正式验收回执。

## 1. 结论：先接真实系数质量，再做原族参数预算

**最近的有效下一步是复用原 `rawLabelBudget` 和真实 `actualModeLambda/Omega` 范数供应者，把当前显式 `sourceAbsMass` 尾界接成实际模式的标签预算界。** 其中恢复旧证明与有限接线已有明确来源；把该预算变成全族随 `x` 衰减的误差，仍须接入真实尺度、`Z` 和外层重组条件。不要把新前提“总误差已经很小”或“当前任意系数范数不超过一”作为闭合替代品。[S1–S4、C1–C3]

| 部分 | 当前证据 | 分类 |
|---|---|---|
| 单项与六项共同 `J` 的硬尾，右端保留 `sourceAbsMass` | 本轮 `actual_smoothMass_common_hard_tail`、`actual_sixSmoothMass_common_hard_tail` | 本轮冻结实现；不重做 |
| `rawLabelBudget`、`sourceAbsMass_le_rawLabelBudget` | 原 `Part3ActualCompletedHardTailMass.lean`，107–138 行 | 现成源码可复用；本轮没有恢复这两项 |
| 原实际 `lambda/omega` 范数不超过一 | 原 `Part3ActualModeJointBetaPositiveCount.lean`，59–85 行 | 现成真实供应者；须恢复/定位其实际定义依赖，不能替换成前提 |
| `nonzeroSource` 质量不超过完整源质量 | 当前 `nonzeroSource` 是 `Finset.filter`，质量是非负范数和 | 只欠有限集合接线；无需新的分析输入 |
| 将 `R=x^ε/10` 代入共同硬窗口及尾界 | 本轮尾界 + 旧 `globalCutoff` 公式 | 只欠有限代换；不等于原族误差预算 |
| 将 `C² rawLabelBudget` 及真实外层重组损失统一控制为 `x` 的固定次幂 | 当前核验范围没有找到已接到该尾界的结论 | 尚未闭合；须由真实原族条件证明，不应作为目标型新假设 |
| 旧 `OriginalData` / `FixedBlock` 或实际 M2 原行身份 | 有旧字典定理，但当前两条路线参数不同 | 有限字典/原数据恢复义务；不能默认相同 |

以上“现成源码”不等于已在当前验收闭包中独立 strict/replay。对于下列候选，本轮只确认源码和数学接口；未重新检索既有远端验收报告，也不依据旧 `SOURCEONLY` 页首判定它从未编译。

## 2. 本轮消费者恰好给到哪里

当前 namespace 是 `ImbalancedChen.Part3.ActualSmoothMassTruncation20261127`。

- `primaryTail_common_hard_bound`：C1 的 139–149 行。
- `actual_smoothMass_common_hard_tail`：C1 的 198–218 行。
- `actual_sixSmoothMass_common_hard_tail`：C1 的 233–305 行。

对每个自然数 `r ≥ 2`，先取得一个 `A_r > 0`，再对所有正尺度、`R > 0` 和实际源参数给界。六项结论为

\[
\left\|\operatorname{sixSmoothMass}-\operatorname{actualTruncatedSix}_{J}\right\|
\le \frac{6A_r C^2}{R^{r-1}}\,
\operatorname{sourceAbsMass}(\operatorname{nonzeroSource}S,\lambda,\omega),
\qquad J=\left\lceil\frac{10CR}{B}\right\rceil.
\]

这里的 `lambda`、`omega` 仍是任意函数参数；定理没有 `MediumAdmissible` 假设，也没有把它们定义成原 mode 系数。`B`、`C` 也仍是该接口的尺度参数。`S = actualSource e D delta g l Z residueNegative` 的真实载体由 C2 的 43–47 行给出：

\[
T=\operatorname{baseCarrier}(e,D/\delta),\quad
H=\left\lceil\frac{64ZQ_1Q_3^2Q_2^2}{DV}\right\rceil,\quad
F=\frac{U}{gQ_1D}.
\]

这些定义对应 C3 的 18–26、34 行。`nonzero_actualSource`（C2，49–52 行）已经把该过滤源与现有 `actualNonzeroSource` 识别为同一对象；勿重新声明同名定义。[C1–C3]

## 3. 可直接复用的质量界及真实系数供应者

### 3.1 两个尚未恢复的原声明

S1 的原 Git blob 是 `b23e2e000301008244372e076411750ad4daa2bb`；本轮已完整归档原文件，所以不需要重新寻找这份证明。

`rawLabelBudget`（107–109 行）定义为

\[
\#\{f\in\mathbb Z:\lceil-F\rceil\le f\le\lfloor F\rfloor\}
\left(\#T\cdot\#\operatorname{poissonNonzeroFrequencyWindow}(H)\right)^2.
\]

`sourceAbsMass_le_rawLabelBudget`（111–138 行）证明完整 `carrier` 的质量不超过该数。它只在原 `T` 和原 signed nonzero `H` 窗口上要求 `‖lambda t‖ ≤ 1`、`‖omega h‖ ≤ 1`；证明从两个 `atomCoeff` 的范数界出发，再用原 `rawCarrier` 的积载体计数。这个一般性供应者的条件本身正确，但要得到“实际系数界”，必须从真实定义供应它们。[S1]

当前消费者用的是 `nonzeroSource(carrier ...)`。先用其 `filter_subset` 及求和项非负得到质量单调性，再调用原质量界，就是最近的有限接线。不可为方便再增加 primary `keys.card`；本轮已经在取范数前精确合并了全部 primary 源。[C1，119–149 行；S1，111–138 行]

### 3.2 公开 actual norm 定理已有，当前 curated tree 尚缺其真实定义闭包

S2 的 namespace 是 `ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly`。

- `actualModeLambda_norm_le`（59–74 行）：接受 `MediumAdmissible`、`D delta g l`、`[NeZero (g*l)]`、mode/sign/unit/residue 参数及 `t ∈ baseCarrier e (D/delta)`，结论是原 `actualModeLambda` 的范数不超过一。证明使用原 `gamma2` 的界、原可整除像载体、`s/Q2 ≥ 1`、log 内乘子的范数与根相位的单位范数。
- `actualModeOmega_norm_le`（77–85 行）：对原 shortened signed `h` block 和根剩余类指示后的 `actualModeOmega` 给界，不需额外 `MediumAdmissible` 假设。

必要 private 前置项位于同文件 22–56 行：`norm_branch_eq`、`norm_rootT_eq`、`baseCarrier_original_window`、`original_innerMultiplier_norm_le`。应复用这段原证明；本轮的源码清单检查没有在当前 curated tree 找到 `actualModeLambda`、`actualModeOmega` 或这两个公开范数定理的定义。[S2]

实际定义不是任意替身：

| 原文件 | 原声明/位置 | 用途 |
|---|---|---|
| S3 `Part3ActualM2FinitePoissonAdapter.lean` | `actualModeLambda` 55–58；`actualModeOmega` 62–66 | 原 gamma/log/root 系数及真实 block/residue 指示 |
| S5 `Part3ActualSeparatedRowFiniteMatcher.lean` | `commonLambda` 2291–2294；`commonOmega` 2296–2297；`rootT` 1767 起；`branch` 2103 | 原相位与根数据，不改变共轭放置 |
| S4 `Part3ActualSeparatedRowLogModeSupplier.lean` | `innerMultiplier` 2019；`norm_innerPhase` 2119；`norm_hMode_le` 2132–2137；`modeW/modeOmega` 2445–2450 | 原 log mode 的真实振幅与单位相位界 |

无需因此整文件导入所有旧分析闭包。先比对已有 declaration owners，恢复最小真实定义与这些原证明；不要重复恢复已在 `Part3ActualNonzeroSourceCore` 中拥有的 `actualNonzeroSource`。[C3、S2–S5]

S1 的 `actual_completedModePiece_common_hard_tail`（142–175 行）已经演示了全部真实系数特化：调用上述两个公开范数定理，右端仍为

\[
\frac{A_r\operatorname{scaleC}(e,D,g,l)^2}{R^{r-1}}
\operatorname{rawLabelBudget}(T,H,F).
\]

它不是完整 `x` 预算，也不是本轮新六项消费者；可以复用其参数接法，而不重复恢复已经拥有的 generic kernel/source 尾定理。`ActualBetaNativeSource` 的 beta/fiber 支撑字典并不供应这两个系数范数界，不应为了质量接线盲拉整套该文件。[S1，142–175 行；S2，59–85 行]

## 4. 已有计数与模式预算可继续复用，但没有现成总误差结论

限定的本地检索中，`rawLabelBudget`/`sourceAbsMass` 的旧结论仍止于 S1；未找到一个已把它们接到全族 `x` 衰减的源码消费者。以下更低层供应者已经有原证明，应优先复用：

- S5 的 `factorCarrier_card_le_add_one`（885–890 行）：真实闭区间 `factorCarrier Q` 的基数至多 `Q+1`，需要 `1 ≤ Q`。对 `baseCarrier`，另接 `card_image_le` 与 `filter_subset` 即可得到粗界；无需重新分析整除像。
- S7 的 `frequency_card_le`（90–98 行）：原 signed nonzero `H` 窗口基数至多 `2H`。
- S7 的 private `factor_card_small`（105–113 行）及 `actualZeroPiece_norm_le` 内部 415–428 行已有对 `0<Sinner<1` 也正确的基数处理；若需要精确 `T` 尺度，使用其真实 `D>0`、`delta>0`、`delta ∣ D` 许可证。
- S4 的 `coeff_l1_fourth`（2175–2183 行）和 `coeff_l1_original_five`（2186–2193 行）已有原模式 Fourier 系数的可求和预算，后者保留 `x^(5*kappa)` 的原损失。这是未来处理实际外层 mode 重组可用的供应者，不能直接把“每个 mode 的统一界”当作无限 mode 求和界。

原 `rawLabelBudget` 的 `f` 窗口是完整闭区间，包含零端点可能性；不能无许可删除 `+1` 或把其基数直接写成 `2F`。S7 的 `signedF_card_le` 针对额外过滤 `f ≠ 0` 后的集合，不能不经集合识别直接套到完整 `Icc`。若追求 `x` 的粗多项式界，保留端点项通常已足够。[S1，107–138 行；S7，115–125 行]

## 5. `R=x^ε/10` 是有限接线；缺口在它后面

旧 `Part3OriginalCommonPoissonLanes.lean` 的 `globalCutoff` 原 blob 为 `00a797ac77cb444479ce097f4b44c56930489e32`，公式是 `Nat.ceil ((C/B) * x^epsilon)`。该事实复用已发布上轮审计 P0 的第 4、5 节，本轮没有再次抓取稳定原文件。

当 `x>0` 时令 `R=x^ε/10`，由实幂正性得到 `R>0`，并有

\[
\left\lceil\frac{10C(x^\epsilon/10)}B\right\rceil
=\left\lceil\frac CB x^\epsilon\right\rceil.
\]

第二 b-scale 的 `2B` 继续配 `2R`；本轮 `common_cutoff_double_scale` 已处理同一 `J` 的相等关系。取整外面的代数一致后，不需要新增 cutoff 分析。尾式对应变为

\[
6A_r10^{r-1}\,C^2\operatorname{sourceAbsMass}(\operatorname{nonzeroSource}S)
\,x^{-\epsilon(r-1)}.
\]

**这个式子本身仍非全族小误差。** 当前接口的 `lambda/omega` 可任意缩放；`Z` 也是任意实参数，使实际 `H` 可任意增长；当前 `C` 尚未被识别为原 `scaleC`。因此不能对所有这些自由参数只凭固定 `r` 宣称 `O(x^{-L})`。[C1，233–246 行；C3，18–34 行]

真正需要证明的是原合法参数族中的增长控制。例如，当已经从原数据推出

\[
C^2\operatorname{rawLabelBudget}(T,H,F)\le K_0x^K
\]

并支付真实外层模式/标签重组成本后，才可在 `epsilon>0` 时固定一个 `r`，使 `epsilon*(r-1)>K+L`，得到所需的 `x^{-L}` 界。这里的展示只说明应证明的预算及选择顺序，**不是建议把这条目标预算作为新假设加入最终 theorem**。

固定阶数与误差常数必须先于变化的原族成员选定，正如 C4 的 `RestrictedMediumTarget`/`RestrictedMediumObligation` 在 152–162 行的量词顺序。每个原块可以按同一个原公式取 `J`；它在该块六项和被谱平均的 level 上公用，并不意味着对所有不同 `x` 强行使用同一个数值整数 `J`。[C4；M，700–703、1049–1067 行]

## 6. 家族预算的具体未接项目

以下是需要实际数据证书的接口，不是新外部分析定理：

1. **尺度身份和正性。** S6 的原 `scaleB = l*U*Q3/delta`、`scaleC = U*Q3*Q2/(g*l*D)` 位于 295–297 行；`scaleF` 的 current owner 已在 C3。将自由 `B,C` 特化为真实尺度时，需要从真实 slice 成员或明确的正自然数/整除许可推出正性，不能擅自增加 `delta>0` 来替代原成员条件。
2. **`T,H,F` 与 `x` 的统一界。** C4 的 `MediumAdmissible` 提供 `U,V,Q_i ≥ 1`、`x=UV` 与原几何不等式；结合上述有限基数界可以做粗多项式估计。但实际 `Z` 的取值规则或统一上界必须从原 Poisson 截断/外层构造取得；裸 `MediumAdmissible` 不包含 `Z`。本轮未定位到一个已经把这些条件组合为该 `rawLabelBudget` 全族结论的消费者。
3. **原 mode 与外层费用。** S3 的 `actualModeRow_eq_trueFiniteRow`（118–136 行）保留 `modeCoefficient * modeAlpha` 在真实 reciprocal row 外面。需要使用原 mode 求和及外层计数，避免把无限 mode 数目或外部乘子默认为一。S4 的现成 `coeff_l1_*` 是可复用输入，不是整个该重组的既成结论。
4. **送回实际原行/误差目标。** 将尾界送到原 `signedError` 或旧 `completedAmbientEnergy` 仍需真实字典。当前核心定理没有构造这个数据流；C4 的最终均匀目标依然是原 signed modulus sum 的界。

手稿给出这些步骤的数学依据：M 的 449–453 行固定 one-bounded 系数；559–585 行给正平方完成、真实 `B,C,F` 范围、对数数量的块及外部 Cauchy 因子；588–620 行定义保留两份有序标签的 beta；700–703 行才是固定足够大阶数支付尾项。应补齐这些已有结构与参数的形式化连接，不能以一条包揽全部损失的假设跳过。[M]

这次有限审查没有发现此处必须引入新的稿外谱定理，也没有据有限未接线判定手稿存在实质证明缺口；目前明确缺的是实际定义闭包和全族参数/重组预算的正式连接。

## 7. `OriginalData` 路线：保留旧字段，勿用同名替身

P0 已核实旧 `Part3OriginalCompletedReciprocalSource.lean` 的原 blob `a99ba7e76f13c45beac5bd459334c9a75dc7c5a7`。本轮只复用这份已发布的稳定来源审计，没有重复远端搜索。

旧 `OriginalData` 独立含 `block : FixedBlock` 与 `atom : MediumAtom`，没有 `atom = block.atom` 字段。原行的数据流是：

- `bScale/cScale/fScale` 与 residue 读取 `block.atom`；
- `sCarrier/lambda` 读取 `atom` 及原分解标签；
- `hBound` 来自 `block.H` 的整数化，`omega` 来自 block/rectangle；
- `row = finiteReciprocalRow 1 block.atom.residue ...`。

旧 `row_eq_completedBare`（77–83 行）、`completedAmbientEnergy_le_smoothSix`（185 行起）、`original_six_eq_signed_joint_source`（278–289 行）都是现成原字典/组合。当前 actual 路线的模数是 `g*l`、残数带符号，且读取当前 `baseCarrier/sharedSmoothFrequencyBound/scaleF`。即使另加两个 atom 相等，也不能自动识别这些全部参数。[P0，第 6 节；C2–C3]

下一轮可以选择复用 S3 的 `actualModeRow_eq_trueFiniteRow` 直接连接真实实际 M2 路线，或恢复旧 `OriginalData` 路线及其真实字典；不应为了便利造一个简化 `FixedBlock`。若声称原 `OriginalData` 目标已经闭合，必须说明模数、残数、载体、H/F、尺度、系数与外部乘子的完整识别。

## 8. 保留的独立边界

- 本轮尾控制的是非零源 `y≠0` 的高 Poisson `m` 尾；截断核保留 `m=0`，`y=0` 源则保留完整整数 `m` 核。
- S7 的 `zeroPiece_norm_le`/`actualZeroPiece_norm_le` 支付源 `y=0`；不能将其作为 M 的 695–699 行 Poisson `m=0` 的 Ramanujan/gcd 支付。后者还需真实 `a*y ≠ 0` 许可；仅 `y≠0` 不给出 `a≠0`。
- 真实 PacketData/核的 `hkernel` 认同、原生 Theorem J 全相位输入、Theorem A 的 n-side 输入及谱高独立性，仍在其各自已有接口中解决；质量界与 `R` 代换不证明这些边界。[P0，第 7 节；M，695–699、1040–1067 行]

## 9. 建议下一次实现的最小交付

1. 复用 S1 的 `rawLabelBudget` 与 `sourceAbsMass_le_rawLabelBudget` 原片段，接 `nonzeroSource` 的非负有限和单调性。
2. 按真实 owners 恢复 S3/S4/S5 的必要 actual 系数定义与 S2 的公开范数证明；对本轮实际六项消费者做真实系数特化。不要重新定义 C3 已有的载体或重做本轮尾证明。
3. 同一次有限消费者中可以完成 `R=x^epsilon/10` 和原 cutoff 的对齐，但交付说明仍明确右端的真实标签预算。
4. 后续单独把真实 `Z` 许可、尺度与标签基数、外层 mode 及原行重组接成统一原族预算，再选择固定衰减阶数。只有这一步完成后，才能宣称稿 700–703 行所需的原族可忽略尾误差，而不是仅有一个带源质量的参数一致尾界。

## 10. 来源索引与固定身份

### 当前仓库

- **C1** `ImbalancedChen/Part3ActualSmoothMassTruncation.lean`，16006 bytes，SHA256 `69265f34ffe404c61dae853d325dd939b0e2b7836f2c954e2887a1eefedaf57b`。
- **C2** `ImbalancedChen/Part3ActualModeCommonPoissonLanes.lean`，当前已有 actualSource/primary lane owner。
- **C3** `ImbalancedChen/Part3ActualNonzeroSourceCore.lean`，2361 bytes，SHA256 `db6f8342ee7b2977dda26001458a9924e29bd7b998a01223007f07c53ca77c99`。
- **C4** `ImbalancedChen/Part3DistributionTargets.lean`，8889 bytes，SHA256 `a0b43f877bb7bcdf7606e19281521a0165538c08c0495a2a3e2d58b66aeb08cc`。
- **P0** `docs/part3-distribution/p31-smooth-mass-lanes-20261127/NEXT_P31_STEP.md`，15223 bytes，SHA256 `d81cb13f7e3066b86418862531334128c7eac6027bdd9250020db35fb06e1c92`；旧 OriginalData/cutoff 稳定审计沿用此证据，不作新远端发现。

### 原源码参考

以下绝对根目录为 `/workspace/scratch/e5f883a2215a/reference/ImbalancedChen/`；表中 Git blob 从原文件字节计算，用于精确识别，不自行授予当前分支的编译验收等级。

| ID | 文件 | bytes | Git blob |
|---|---|---:|---|
| S1 | `Part3ActualCompletedHardTailMass.lean` | 9910 | `b23e2e000301008244372e076411750ad4daa2bb` |
| S2 | `Part3ActualModeJointBetaPositiveCount.lean` | 8681 | `cd7095c80aedaa4073f93946831ff27cfe5d4efd` |
| S3 | `Part3ActualM2FinitePoissonAdapter.lean` | 16539 | `ba8e1eeb633013a4da29f3a139c724d3bbc48cf4` |
| S4 | `Part3ActualSeparatedRowLogModeSupplier.lean` | 136642 | `03b5be64535090929448d59e6faf1113175d3eb1` |
| S5 | `Part3ActualSeparatedRowFiniteMatcher.lean` | 116891 | `c90d4709b3dde3704006ddb8b959c5dc85bcb60a` |
| S6 | `Part3ActualPositiveLatticeSmoothCover.lean` | 24631 | `a094a3dcd2b43124f42e8219e2b1b6ef9ac26cb4` |
| S7 | `Part3ActualCompletedZeroDifferencePayment.lean` | 33745 | `c9e790baf7e031b40fa5ed211c5f15b9e66d21d6` |

S1 还已完整归档到当前仓库 `docs/part3-distribution/p31-common-hard-tail-20261127/upstream/Part3ActualCompletedHardTailMass.lean.txt`，与上述原 blob 相同。S4 的 SHA256 为 `d78396829cbd5257345423f03dd39b4a3abace23f596466a906d330a20b89bb8`；S5/S6 即上轮已审计 donor，无需重做稳定来源寻找。

**M：冻结 1106 手稿。** `UyNewNas/chen-imbalanced-semiprimes` commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`，`paper/release-20261106/en/analytic-appendix.tex`，45951 bytes，Git blob `7cf3bbb16cd8924565eb439e474e0674f04631da`，SHA256 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`。本次直接读取相同原字节本地参考；相关位置为 449–453、559–620、689–703、1040–1067 行。

本检查没有访问云端编译环境、重扫远端分支、运行 Lean/验收器、修改任何 Lean 或 verifier；唯一新增交付是本定位文档。检索结论只限当前仓库及上述既有参考，不声称不存在其他会话中的工作。
