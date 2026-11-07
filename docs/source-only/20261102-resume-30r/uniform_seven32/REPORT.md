# R24 — uniform_seven32 / D22

**PARTIAL：实际 OriginalData 的六核 hard tail 已给统一固定阶/共同阈值付款；两个零项已接入同源有限估计。真正 Eq.(24)、完整 Eq.(25)、统一 7/32 与所有外层费用仍 HOLD。真实谱能量前提消除数为 0。**

`compiled=false; kernel_verified=false; formal_credit=0; finite_guards=UNEVALUATED`。只写本目录；未运行 Lean/Lake/编译器、guard、CI、数值 replay、Git 或子代理。报告中的源码级完成不表示 elaboration 或 kernel acceptance。应用重启后恢复本任务；中断前仅阅读，没有把未落盘内容算成交付。

## 原稿范围与去重

直接核对 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:201–254`、Medium `proof-library/source/distribution-medium-completion-20261010.txt:299–424`、Classical `paper/source/modules/final-classical-input-correspondence-20261010.txt:23–137`。实际原文先保留零差源，随后对非零 y 保留 m=0，再对非零 m 使用一个 global cutoff、共同 m interval/phase；(24) 是全谱二次型，(25) 才是其后尺度代数。Medium:417–424 明确固定有限阶、一次 `5*kappa` 与一个额外 D。

已读 Q20 REPORT/REGISTRY、Q29 独审，P `exceptional_j_eta` REPORT/REGISTRY 与实际 additional-cost 源，O/P/Q 的实际 source/primary/Poisson/Fourier 字典。内容和文件名检索覆盖 production `ImbalancedChen`、全部 `docs/source-only`、隐藏 `.lake/proof-continuation/source-reviews/drafts`，以 OriginalData、globalCutoff/commonHard、sourceAbsMass/rawLabelBudget、六核 tail、zero native caller、actual spectral 等精确名称去重。

特别复用以下既有结果，**没有重新记为新证明**：

- hidden `20261028-Medium-Polynomial-Sol6/Part3ActualSixKernelCommonHardTail.lean:33` 的 `sixKernel_common_hard_tail`；production `Part3ActualCompletedHardTailMass.lean:84,111` 的 source tail/rawLabelBudget。
- 同一 hidden 目录的 `Part3ActualChartSixHardActualBudget`、`Part3ActualPhysicalRawLabelPolynomial`、`Part3ActualPhysicalHardEpsilonSelection` 已经给旧 `actualCompletedChartSix` 的真实六片质量、`x^23` tail 成本与固定阶付款。它们不是“只有单频 tail”。旧 `tChart/actualModeLambda` 与 O/Q `commonS/completedLambda/OriginalData` 没有已供同一化，故没有直接把旧 chart 的最终定理冒充当前源的结果。
- 旧 `full_signed_f_card_le`、`frequency_card_le`、occupied key caps、`actual_rough_owner_geometry`、`hard_rate_absorption`、`exists_hard_order` 均实际调用。新工作是当前源转换与其实际参数，不重复一般 Schwartz 证明或旧计数。
- Q20 的 ABL coprimality、每 dilation K=1、A/J 支持资格完全复用：`M_class=V-1/2`，level 的两个 `Q_class`，阈值比较因子 4，原 common phase 分母 `64V` 都未改动。

一手 [Pascadi v3](https://arxiv.org/html/2404.04239v3) 亦重新打开：Theorem A 明确以真实 Maass cusp basis/Fourier 系数为输入，不能由算术系数模平方替代。本文使用双倍参数 `7/32`；原文常用的 eigenvalue 参数是 `7/64`。本轮没有把该文献陈述改成 Lean 公理。R21–R23 对 ABL/Young/regular/trace 的一手版本核对见其各自报告；这里不把未亲读的其他 PDF 称为独立复核。

## 新源码与实际消除的前提

### 1. `Part3OriginalSixTailBinding.lean`

拟模块 `ImbalancedChen.Part3OriginalSixTailBinding`。新定义只是 Q 原 remainder 的明确分项，未新建 spectral PacketData。

- `sixRemainder_eq_zeros_add_tail:81` 将 Q 原 `sixRemainder` 分成 `sixZeros + sixTail`；`sixZeros` 仍含全 m 的 y=0，以及只作用于非零 y 的 m=0。`pieceTail_eq_original_source:89` 实际消费 `finite_source_assembly`，在取范数前恢复所有 computed primary/sign/y-dyadic rows 的非零原始源。没有额外乘 primary row 数。
- `globalCutoff_window_eq_commonHard:102` 证明有限集合的精确等式

  `mWindow(globalCutoff D x eps) = commonHardWindow C B (x^eps/10)`。

  两者都是闭整数窗口，零点出现一次。没有丢 ceil 端点，也没有把 earlier rough-s 频率 r 当成 Poisson m。
- `original_tailKernel_eq_hard_difference:134` 使用原 Poisson 绝对可和性；`sixTail_eq_original_hard_difference:152` 得到 **Q 的实际六尾** 是同一非零原源上 `sixKernel − commonHardSixKernel` 的加权和。六尺度仍为 `(B,C),(B,2C),(B,4C),(2B,C),(2B,2C),(2B,4C)`，原 `10*C` carrier/c-unit gate 和 signed f 都在。
- `original_lambda_norm_le_one:169` 从实际 admissible atom 的 polarization 和 `completedLambda_norm` 推导 lambda bound，omega bound来自原 signed rectangle indicator。`original_sourceAbsMass_le_raw:175` 与 `original_nonzero_sourceAbsMass_le_raw:185` 直接消费 production raw-label supplier，不把 norm-one 或 mass bound 当字段。
- `original_sixTail_raw_bound:197` 对每个固定 `dord>=2` 给一个先于所有源参数的 K：

  `norm(Q-sixTail at J_eps) <= K * C^2 * rawLabelBudget(T,H,F)/(x^eps)^(dord-1)`。

  K 已含 `10^(dord-1)`。六核费用只付一次；y=0 全谱没有再次进入这个 tail。

### 2. `Part3OriginalSixTailPhysicalPayment.lean`

拟模块 `ImbalancedChen.Part3OriginalSixTailPhysicalPayment`。

`tightOriginalData:51` 直接以已有 `tightPoissonAtlasBlock` 构造 **同一个 O OriginalData record**；rectangle、两个 smooth labels、三个 polarization labels仍各自独立。没有输入“假定 D 是真实源”的证明结构，也没有输入大核或谱能量估计。

`original_sCarrier_card_le:70` 从原 commonS support 推导 `#T<=2S`。`occupied_keyRealH_le_power:85` 消费原 occupied-key caps，得 `H_real<=64*x^12`。`tight_original_physical_tail_cost:121` 得

`C^2 * rawLabelBudget(T,ceil(H_real),2U/Q1) <= 21632000*x^33`。

其实际有限成本依次是：`S<=2x`、`R<=2x`、`C<=4x^3`、`F<=2x`、`#T<=4x`、`ceil(H_real)<=65x^12`、两个 signed nonzero-h windows 各最多 `130x^12`，于是 raw mass 最多 `1352000*x^27`。这是仅用于任意阶 Schwartz tail 的粗多项式包络；不改论文的任何范围、保存常数或目标 saving，也不能充当主谱能量估计。

`exists_tight_original_sixTail_threshold:218` 给实际所需的固定阶/共同阈值：

`forall A>=0, eta>0, exists dord>=2, 34+A <= (eta/2)*(dord-1), exists X>=1, ...`

其后才量化 `b,sigma,kappa,c0,atom,z,y,key,Csep,j,small,negative,rectangle,st,st',polarS,polarR,polarN,r`。输入只有原 `MediumAdmissible`、`sigma>=0`、原 occupied `keyBank`/`activeD` 和 `x>=X`。结论为

`norm(sixTail D r (globalCutoff D x (eta/2))) <= x^(-A)`。

具体选择先由旧 `exists_hard_order (A+11) (eta/2)` 固定 dord，再取得其 tail 常数 K，最后用 `X=max(1,21632000*K)` 吸收常数。没有随 moving source 改阶数或取阈值。此局部 order selection 不依赖 kappa；全谱 Fourier moment/classical eps 的共同最终预算尚未声称完成。

### 3. `Part3OriginalZeroLaneBinding.lean`

拟模块 `ImbalancedChen.Part3OriginalZeroLaneBinding`。

- `originalZeroY_eq_zeroPiece:57` 是原 Q y=0 joint source 与 production `zeroPiece` 的定义等式；`:63` 推导其真实有限上界 `72*M*N*F*H*S*tauEnvelope`。系数 bound 与 source cardinality由前两文件供应，没有另加 zero estimate 输入。
- `original_zeroMKernel_eq_native:78` 实际调用既有 bump 的 `5/2` 支撑，将 `N<=4*C` 的原 `10*C` sum 同 native zero kernel 对齐。原三个 N 值都满足此范围，不需要 endpoint correction。
- `originalZeroM_eq_native:95` 在原 primary rows 上先精确重组，再调用 I 的 `nativeZeroPiece`。`:109` 对同一个 `U=nonzeroSource(originalSource D)` 给

  `norm(originalZeroM)^2 <= (6*M*zeroFourierMass*tau_max(U,a))^2 * #output(U) * sum_output norm(beta_U)^2`。

  **右侧 tau、真实 output cardinality、joint beta norm仍未变成最终归一化小费用。** 这是实际 source binding 和有限估计，不是宣称零项总预算已闭合。
- `original_six_eq_zeros_tail_and_full_modulus:127` 直接消费 R20 `original_six_eq_remainder_and_full_modulus`，得到原 `smoothSix = sixZeros + sixTail + tsum(fullSixMode)`。R20 新增 c 范围的整个 Fourier correction 精确为零，所以没有新增 endpoint/tail 账。它仍是实际 arithmetic source identity，不是 normalized Kuznetsov。

R20 另已提供实际 test 的 `actual_weighted_test_jets_budget` 与 `actual_uniform_test_jets_budget`：固定 n 后，原 `actualCoeff` 加权的 n 阶导数总量为 `C*(1+rho)^(4*(n+3))/Y^n`。这是同源 mode/test 的真实供应；n=0 给 12，n=4 给 28。它不识别 automorphic transforms，也不消除真正谱能量的前提。本文件没有重复该证明。

## 完整费用账与真实缺口

| 项目 | 本轮状态与边界 |
|---|---|
| 同 OriginalData 六片、两 Z、原 J 的非零-y hard tails | 已给上述实际统一付款候选；不是只供应单频尾。其 proof body 仍未编译。 |
| y=0 全 m 与非零-y m=0 | 已给同 Q 对象到实际 native 有限估计的接入；归一化 divisor/output/beta 支出仍 HOLD。旧 I 的 floor-H/countingF 来源与当前 ceil-H/`2U/Q1`、commonS masked source 不能未证等同。 |
| 全正模数 endpoint correction | R20 已给 exact zero correction并在本轮消费；不是新的小量假设。其 admissible test/变换范围以 R20 报告为准。 |
| normalized Kuznetsov 与真实 Fourier products | R21 本轮仍没有实际全谱恒等式供应；cusp算术输入不等于 trace。 |
| 每 dilation ABL / 全 continuous fiber | Q20 只有既有 K=1 资格。R22 的实际 principal Hecke/oldform 局部转换不能自动供应所有 oldclasses、character-pair Plancherel、实际 Maass 7/32 范数或全 continuous 零幂。 |
| A/J/regular/gap | R23 已明确本轮实际能量供应为 0；native signed Fourier 共轭不是 normalized R 或 cuspidal gap。 |
| Medium (24)→(25) | 标量 polynomial 已有，但 (24) 的真正同谱二次型仍缺。没有另写 hEnergy consumer，也没有重命名 completedEnergy。 |
| W0 / W4 / cutoff | R20 实际 test jets 已保留一般 `4*(n+3)` 成本；P 的 q=14只付 `2eta+12eta`，order-four `28eta` 仍独立。其最终 automorphic transform/真谱产品上的接入未供，不能以 Bessel/coefficient packet 支付。 |
| common interval/phase、A/J endpoints | 保留 Q20 `M_class=V-1/2`、两 Q_class 和 factor4，phase仍 `64V`。实际 `(z,j)` 谱 Hilbert norm上的 common-mask log² 接入尚缺。 |
| 外层 scalar atoms、endpoints/classes/divisors/multiplicity、dyadic/Fourier summation | 本轮 tail阈值对每个 original branch统一，但尚未证明所有外层 signed/scalar weights 的完整总付款。不能以“对所有分支统一”代替总质量上界。 |
| 最终参数顺序、一次5kappa、一个D、level Cauchy sqrt(Z) | 既有确定局部供应保持；本轮没有第二次收费，也没有把未供费用列为零。全目录共同预算与原物理 PP 返回仍 HOLD。 |

因此本轮真正移除的是：Q tail 与已有六核估计的对象/窗口接缝，当前源 lambda/omega/raw mass 的独立假设，当前实际 tight-atlas 源质量的多项式假设，以及该 tail 的“存在充分固定阶与共同阈值”假设；另消除两个零项的 native source binding 接缝。**删除 hTrace、actual oldclass/fiber norm、A、J、regular、gap、Eq24 或 hUniformPP 前提均为 0。**

分类：新增 tail/source/zero转换为 class II；未安装的 source-only imports与 elaboration是 class I；真实 normalized full spectrum、经典估计及全源主能量为 class III。当前形式化来源缺项不构成原稿反例。完整 D22 与 P3.5.uniform_spectral 保持 HOLD，不能据此关闭 hLower/hUpper 或 PP 父目标。

## 字节、imports与验证边界

本轮三个新文件及两个最小 API 修复副本的完整 imports、声明行与原始 SHA256，所有直接导入来源的实际路径，以及新增/复用/文献/未完上游的区别均在 `REGISTRY.json`。拟安装位置是 `ImbalancedChen/<basename>.lean`；实际文件只在本目录。R20 是本轮直接依赖；先按下述明确映射替换两个依赖并安装其余 O/P/Q/hidden/R20 源，再安装 TailBinding→PhysicalPayment→ZeroLaneBinding。未声称递归 import closure 已可编译。

对 `poissonTail_eq_sub` 所用接口已核对 manifest 固定的 mathlib revision `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`：[Group.lean 的 `prod_mul_tprod_subtype_compl`](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Topology/Algebra/InfiniteSum/Group.lean#L316) 带 `@[to_additive]`，供应原 O 和本轮所用 `sum_add_tsum_subtype_compl`。实际读取原始字节保存为 `primary/Mathlib_InfiniteSum_Group_e4c91783.lean.txt`，SHA256 `4fff055c5ab67f8bdb076a964e46bbe41ba7bd934a7d36d8baba96d51627580e`。该补集接口本身无需修复；此核对不能等同编译通过。

另核 [固定版 `Finset.sum_mul`](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Algebra/BigOperators/Ring/Finset.lean#L56)：其方向是乘积到逐项乘法的和。新增 TailBinding 的常数提取已改为先展开 `sourceAbsMass`，再 `rw [← sum_mul]`。直接依赖的两个同类确定问题按 BRIEF 允许范围归档为最小修复副本；冻结原件未改，声明、常数、假设及结论完全保持。这仅是 class I 修复，不记新数学供应。

| 修复副本 | 替换来源与唯一变化 | raw SHA256 |
|---|---|---|
| `repairs/Part3ActualCompletedHardTailMass.lean` | production 同名文件 `source_common_hard_tail:104` 的 `rw [Finset.sum_mul]` 改为反向 | `b162d847347dfc2398fe500e1bde453834352d67a81b99be952b7596431468e1` |
| `repairs/Part3ActualZeroPoissonNativeSource.lean` | I `spectral_eq24/Part3ActualZeroPoissonNativeSource.lean` 的 `nativeZeroPiece_sq_le:147` 的 `rw [sum_mul]` 改为反向 | `e8ce433351fa313416d3e406be8f8b9b0b90d055a9fbd8520397ce9a33f16df6` |

同一固定版 Ring/Finset 原始字节另存 `primary/Mathlib_Ring_Finset_e4c91783.lean.txt`，SHA256 `472cd5000412d8ec35c8b9ee919b2aeedbf0a830033a55009aad436595923809`。未声称这两处修复穷尽递归依赖的 elaboration 问题。

| 新源码 | raw SHA256 |
|---|---|
| `Part3OriginalSixTailBinding.lean` | `a2e29298bed7a880140cb4cfa6160baa03e65809d75af579eea31a9c4d5f8ab1` |
| `Part3OriginalSixTailPhysicalPayment.lean` | `a19d6ca03e92790c891fc6c062c3004c5b67f466cd64793652e6bcccac397df7` |
| `Part3OriginalZeroLaneBinding.lean` | `6d94d7b41a4938d45074e9558bf69fd41f2b9a0bbdb2751b5361c07e55373697` |

只执行了文件读取、静态声明/import/禁止词检查及哈希/JSON元数据生成。未执行 proof body、有限 guard、数值或编译。R30 独审另行记录，不能由本作者报告替代。
