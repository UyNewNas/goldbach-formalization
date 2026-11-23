# 全黄色节点的整项任务与稿内源码

按最新看板设置 **36 个独立节点任务：13 个实际叶任务、23 个父级汇总任务**。每个节点都保留原完整义务和验收条件；父任务由对应负责人汇总，复用子项证明。

本检查点已实际派发 13/13 个整叶负责人。当前环境允许同时运行 3 个子代理；任务在精确依赖处交接后释放运行名额，所有权继续保留。全部节点合同及调度状态见 [完整任务表](../../verification/20261123-yellow-leaf-continuation/ALL_YELLOW_TASKS.md) 和 [机器可读合同](../../verification/20261123-yellow-leaf-continuation/ALL_YELLOW_TASKS.json)。

本源码包收录 **67 份未编译候选**，共 665,912 字节。另有 8 个新增入口已通过本地编译、精确模块 kernel 与 55 条定理的类型／传递公理检查，详见 [已验证入口](../../verification/20261123-yellow-leaf-continuation/README.md)。这些已验证源码在标准模块位置，不在本包重复复制。

**整叶关闭数仍为 0。36 个黄色节点、13 个实际黄色叶、23 个黄色汇总父项及原 52 项绿色验收保持原范围。源码存在、局部核验和整叶验收分别登记。**

## 逐节点负责人

| 负责人 | 实际黄色叶 | 额外父任务数 | 显式模型／推理 | 本检查点状态 |
|---|---|---:|---|---|
| Y01 | 原增益搬运与剩余误差、预留支付 | 5 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y02 | 同源闭包编译、kernel replay、传递公理检查与独立复核 | 0 | gpt-6.2-sol / high | 已定位阻塞，整项未闭合 |
| Y03 | 完整 W1/W2 因果载体与 Gamma 许可 | 4 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y04 | 真实normalized trace/Fourier乘积、完整连续谱/ABL/gap及含全部费用的统一7/32能量 | 1 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y05 | 原causal策略的共同Q覆盖、过滤补集付款、定量调和质量见证及所需稀疏正质量族供应 | 0 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y06 | 超出已证级别范围的高秩／增强及其他系数类、完整同rho PP总装 | 2 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y07 | 完整 hUniformPP 供应与同 rho 上界总装 | 2 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y08 | 完整 Member 实例与原策略许可 | 3 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y09 | W1/W2 异常衔接与剩余分析付款 | 1 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y10 | 全部bank逐项舍入权重、point读取及candidate→profile/基项比较，解析seed/count与同rho PP许可 | 0 | gpt-6.2-sol / high | 已交阶段成果，依赖及剩余义务未闭合 |
| Y11 | 全历史质量控制与 430+11 共同实例 | 1 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y12 | 把八组真实供应闭合到同一原始实例 | 2 | gpt-6.2-astra / max | 已交阶段成果，依赖及剩余义务未闭合 |
| Y13 | 消除hLower/hUpper并导出无条件主定理 | 2 | gpt-6.2-astra / high | 已交阶段成果，依赖及剩余义务未闭合 |

数学路线尚有实质分析工作、作用于多条主定理链的任务使用 Astra/max。有限银行语义和闭包工程使用 Sol/high。最终端点总装的路线较明确，使用 Astra/high。每个实际派发都显式指定模型和推理强度。

## 已交回的整项进展与剩余义务

### Y01 · 原增益搬运与剩余误差、预留支付

在同一 Fine 见证上连接原87域真实积分、Q96数值、原8素数Member、独立Rosser宽度与带两项修正的附着reserve。复用原BV后，支付三个真实核的完整经典范围、素数均值及上下光滑端点。

**整项剩余：** 两个历史差系数和最终singleton系数在 pan cutoff 以上的各自 signed PP；同一Fine switched计数的 remainingAtlas；历史过滤与最终Fine选择仍须按各自量词绑定。

候选源码：

- [P1Full87FineArchiveCount.lean](y01_gain_reserves/ImbalancedChen/P1Full87FineArchiveCount.lean)
- [P1Full87HistoricalMiddleSmoothing.lean](y01_gain_reserves/ImbalancedChen/P1Full87HistoricalMiddleSmoothing.lean)
- [P1Full87PhysicalKernelSmoothing.lean](y01_gain_reserves/ImbalancedChen/P1Full87PhysicalKernelSmoothing.lean)
- [P1Full87SharpClassicalCut.lean](y01_gain_reserves/ImbalancedChen/P1Full87SharpClassicalCut.lean)
- [OriginalEighthCommonBetaWidthPayment.lean](y01_gain_reserves/selected-api/ImbalancedChen/OriginalEighthCommonBetaWidthPayment.lean)
- [P1OriginalSingletonMiddleWeight.lean](y01_gain_reserves/selected-api/ImbalancedChen/P1OriginalSingletonMiddleWeight.lean)

### Y02 · 同源闭包编译、kernel replay、传递公理检查与独立复核

独审首五个新入口及50条类型/公理记录；历史父 P5SubdivisionStoredParentTypes 无重编译通过原对象复用、单模块kernel和5项结构声明检查。19个旧后像另通过无构建与57项类型/公理检查。

**整项剩余：** 原1664完整同源闭包、九floor与原终端类型门仍未通过；大官方对象包受下载接口大小限制，AffineSimplexMomentLaw原源码有44条编译诊断。19个候选后像本轮kernel超时，未新增核验信用。

### Y03 · 完整 W1/W2 因果载体与 Gamma 许可

复用已有Γ普通质量与child字典，写出原21项种子、Γ9–15逐行单位价，以及同一经典母盒的 5(Phi−(1−1/50)Theta)≤G+P+εTheta；联合前缀窗profile单独已核验。

**整项剩余：** P为实际prime测试减681/400倍同父未筛质量；还须完整增强carrier、70+36历史行及四轮、H247的29个实际函数比较。Y09已交消去G的原36×4 good-pair源码候选，尚未整闭包编译。

候选源码：

- [P2OriginalSeedGammaRowPrices.lean](y03_w1w2_gamma/ImbalancedChen/P2OriginalSeedGammaRowPrices.lean)
- [P2OriginalSeedPositiveBalances.lean](y03_w1w2_gamma/ImbalancedChen/P2OriginalSeedPositiveBalances.lean)
- [P2OriginalWuSeedGammaSignedCount.lean](y03_w1w2_gamma/ImbalancedChen/P2OriginalWuSeedGammaSignedCount.lean)
- [P2WuJointWindowOriginalCount.lean](y03_w1w2_gamma/ImbalancedChen/P2WuJointWindowOriginalCount.lean)
- [P2WuJointWindowCarrier.lean](y03_w1w2_gamma/ImbalancedChen/P2WuJointWindowCarrier.lean)
- [P2WuJointWindowTheta.lean](y03_w1w2_gamma/ImbalancedChen/P2WuJointWindowTheta.lean)
- [P2WuOriginalWindowUpperWall.lean](y03_w1w2_gamma/selected-api/ImbalancedChen/P2WuOriginalWindowUpperWall.lean)
- [P2WuOriginalWindowUpperTheta.lean](y03_w1w2_gamma/selected-api/ImbalancedChen/P2WuOriginalWindowUpperTheta.lean)

### Y04 · 真实normalized trace/Fourier乘积、完整连续谱/ABL/gap及含全部费用的统一7/32能量

直接复用已发表两符号六尺度trace及连续投影；新增原抛物非零Fourier、几何Eisenstein、printed连续谱与原窗口替换候选。单位模加权曲线辅助单独已核验。

**整项剩余：** 原离散Maass/holomorphic ABL、native Kim–Sarnak/gap、完整J范围、同一test的变换与全部六尺度费用。另有六份注册源码的所需精确字节尚缺；已有可靠文献缺Lean绑定不等于稿件命题被反驳。

候选源码：

- [Part3ActualParabolicNonzeroRows.lean](y04_spectral_732/ImbalancedChen/Part3ActualParabolicNonzeroRows.lean)
- [Part3GeometricCriticalEisenstein.lean](y04_spectral_732/ImbalancedChen/Part3GeometricCriticalEisenstein.lean)
- [Part3OriginalGeometricWindowEnergy.lean](y04_spectral_732/ImbalancedChen/Part3OriginalGeometricWindowEnergy.lean)
- [Part3OriginalPrintedContinuousTrace.lean](y04_spectral_732/ImbalancedChen/Part3OriginalPrintedContinuousTrace.lean)
- [Part3OriginalPrintedPrescribedRows.lean](y04_spectral_732/ImbalancedChen/Part3OriginalPrintedPrescribedRows.lean)

### Y05 · 原causal策略的共同Q覆盖、过滤补集付款、定量调和质量见证及所需稀疏正质量族供应

对原U5全三角按真实rootQ分割，保留selectedPolicy/缓冲根/平方条件；商k=1的真实整数系数为+1。事先固定64倍窄窗、去掉N的素因子和零权后有显式逆对数质量及Theta。全原短补集任意log精度，完整经典域直接复用Y01后接Y06两HB分支。

**整项剩余：** 全部实际历史的、在N之前冻结的共同Q母盒和全部正查询；完整signed几何补集与稀疏族加总；经典域之外的真实算术。单个非平台头纤维的c/q不能代替逆log质量；原Gamma的rootQ与native缓冲seed保持区分。

候选源码：

- [P5OriginalU5ClassicalComplement.lean](y05_causal_q_mass/ImbalancedChen/P5OriginalU5ClassicalComplement.lean)
- [P5OriginalU5FixedSparseReceiver.lean](y05_causal_q_mass/ImbalancedChen/P5OriginalU5FixedSparseReceiver.lean)
- [P5OriginalU5HeadSupply.lean](y05_causal_q_mass/ImbalancedChen/P5OriginalU5HeadSupply.lean)
- [P5OriginalU5MarkedMass.lean](y05_causal_q_mass/ImbalancedChen/P5OriginalU5MarkedMass.lean)
- [P5OriginalU5NativeRootCover.lean](y05_causal_q_mass/ImbalancedChen/P5OriginalU5NativeRootCover.lean)
- [P5OriginalU5ShortComplement.lean](y05_causal_q_mass/ImbalancedChen/P5OriginalU5ShortComplement.lean)
- [P5OriginalU5UnitMark.lean](y05_causal_q_mass/ImbalancedChen/P5OriginalU5UnitMark.lean)

### Y06 · 超出已证级别范围的高秩／增强及其他系数类、完整同rho PP总装

原双素数全合法宽度proper-power付款及合法小trim向现有消费者的转移；U5全原标记含q>N的正成本、平滑和HB校正，原补集还原到同整数rho的medium+noMedium。粗糙阈值辅助单独已核验。

**整项剩余：** 各真实原系数和源族的保留算术、完整(S)/(F)、高阶及增强分支、原同父Theta相对prime差额。U5系数不替代P1两个历史差；compiled密度序不替代raw系数signed误差界。

候选源码：

- [P3OriginalProperPowerChartPayment.lean](y06_same_rho_pp/ImbalancedChen/P3OriginalProperPowerChartPayment.lean)
- [P4BOriginalAllWidthProperPowers.lean](y06_same_rho_pp/ImbalancedChen/P4BOriginalAllWidthProperPowers.lean)
- [P4BOriginalFineRetainedCalibration.lean](y06_same_rho_pp/ImbalancedChen/P4BOriginalFineRetainedCalibration.lean)
- [P5OriginalU5AllMarkCosts.lean](y06_same_rho_pp/ImbalancedChen/P5OriginalU5AllMarkCosts.lean)
- [P5OriginalU5AllMarkHBReserves.lean](y06_same_rho_pp/ImbalancedChen/P5OriginalU5AllMarkHBReserves.lean)
- [P5OriginalU5AllMarkSmoothing.lean](y06_same_rho_pp/ImbalancedChen/P5OriginalU5AllMarkSmoothing.lean)

### Y07 · 完整 hUniformPP 供应与同 rho 上界总装

用两原Rosser密度非负证明raw附着密度不大于compiled Fine密度，构造同一实际attached Q/rho的上界选择、全宽恢复和任意实b的消费者。

**整项剩余：** 每个固定合法宽度和每个精度，同一Selection上全部原remainingRows的N/log^p界；移动宽的remainingAtlas另按其原阈值接口处理。依赖Y06全实际signed算术。

候选源码：

- [P4BOriginalFineAttachedRetained.lean](y07_uniform_upper/ImbalancedChen/P4BOriginalFineAttachedRetained.lean)
- [P4BOriginalFineAttachedUpper.lean](y07_uniform_upper/ImbalancedChen/P4BOriginalFineAttachedUpper.lean)
- [P4BOriginalFineRemainingCount.lean](y07_uniform_upper/ImbalancedChen/P4BOriginalFineRemainingCount.lean)
- [P4BOriginalRosserDensityOrder.lean](y07_uniform_upper/ImbalancedChen/P4BOriginalRosserDensityOrder.lean)

### Y08 · 完整 Member 实例与原策略许可

对两原根及全部0–430位置给实际Member查询，保留原标记、owner和定向读数；付款full/selected physical平方薄层。原严格截断的等号情形用固定η移位，并以实际Selberg两线筛和自己的Theta支付真实筛窗，含full、outside、rootMask。

**整项剩余：** 实际adopted/action的signed算术、far rejected、完整factorization与第三槽、原正域极限质量，以及430+11同一联合实例。新增5份源码未编译；两份仅导入兼容文件不计数学进展。

候选源码：

- [Part5OriginalH430AllLaneMemberQuery.lean](y08_member_policy/ImbalancedChen/Part5OriginalH430AllLaneMemberQuery.lean)
- [Part5OriginalH430EmittedSquareBuffer.lean](y08_member_policy/ImbalancedChen/Part5OriginalH430EmittedSquareBuffer.lean)
- [Part5OriginalH430RoughCutoffSelberg.lean](y08_member_policy/ImbalancedChen/Part5OriginalH430RoughCutoffSelberg.lean)
- [Part5OriginalH430SquareStripPrimeMass.lean](y08_member_policy/ImbalancedChen/Part5OriginalH430SquareStripPrimeMass.lean)
- [Part5OriginalH430StrictCutoffTransfer.lean](y08_member_policy/ImbalancedChen/Part5OriginalH430StrictCutoffTransfer.lean)

### Y09 · W1/W2 异常衔接与剩余分析付款

原36×4经典Wu good-pair全部写到同盒Theta与原半开载体，连接种子不等式消去Y03的G；原U3/U4历史cutoff单调及rough root下真实mask bank窗口为零。106项原有净价保留原前代、壳层与重数。

**整项剩余：** 实际同Q/rho signed PP、unmasked/rejected ordinary前代净价及四轮真实许可。另有注册源码P2N48TermOneAllPatternClosedVolumes精确字节缺失，这是独立的档案缺件；masked薄模块避开该缺件，未宣称hgain已付。

候选源码：

- [P2OriginalHalfOpenOrdinaryPairTheta.lean](y09_w1w2_exceptions/ImbalancedChen/P2OriginalHalfOpenOrdinaryPairTheta.lean)
- [P2OriginalWuGoodPairLabels.lean](y09_w1w2_exceptions/ImbalancedChen/P2OriginalWuGoodPairLabels.lean)
- [P2OriginalWuGoodPairPayment.lean](y09_w1w2_exceptions/ImbalancedChen/P2OriginalWuGoodPairPayment.lean)
- [P2OriginalWuSeedAfterGoodPairs.lean](y09_w1w2_exceptions/ImbalancedChen/P2OriginalWuSeedAfterGoodPairs.lean)
- [Part5OriginalH430ActualMaskedBankWindows.lean](y09_w1w2_exceptions/ImbalancedChen/Part5OriginalH430ActualMaskedBankWindows.lean)
- [Part5OriginalH430MaskedSievePlateau.lean](y09_w1w2_exceptions/ImbalancedChen/Part5OriginalH430MaskedSievePlateau.lean)
- [Part5OriginalH430MonotoneSieveHeight.lean](y09_w1w2_exceptions/ImbalancedChen/Part5OriginalH430MonotoneSieveHeight.lean)
- [Part5OriginalH430OriginalReceiptSwitches.lean](y09_w1w2_exceptions/ImbalancedChen/Part5OriginalH430OriginalReceiptSwitches.lean)
- [Part5OriginalH430SelectedReceiptPlateau.lean](y09_w1w2_exceptions/ImbalancedChen/Part5OriginalH430SelectedReceiptPlateau.lean)

### Y10 · 全部bank逐项舍入权重、point读取及candidate→profile/基项比较，解析seed/count与同rho PP许可

精确复用原证据包7/8份JSON，逐项核对70 W1、36 W2的原points与反馈权重，不重算430代或17572行。四份候选将两阶段W1基底接到真实K*I/8和同Q三素数差额；保留高knot的前代Buchstab floor差、W2原符号和唯一外层/5。

**整项剩余：** 唯一未取回的原certify_combined_finite_table.json阻塞候选闭包；真实36条W2 bases、种子四轮、实际同rho PP和H247的29项真实端点比较仍缺，其中H247仍0/29。数值权重核对不替代这些解析许可。

候选源码：

- [P2HistoricalArchivedActionFeedback.lean](y10_bank_semantics/ImbalancedChen/P2HistoricalArchivedActionFeedback.lean)
- [P2HistoricalPointProfile.lean](y10_bank_semantics/ImbalancedChen/P2HistoricalPointProfile.lean)
- [P2HistoricalW1RealBase.lean](y10_bank_semantics/ImbalancedChen/P2HistoricalW1RealBase.lean)
- [P2HistoricalW2BaseRepricing.lean](y10_bank_semantics/ImbalancedChen/P2HistoricalW2BaseRepricing.lean)

### Y11 · 全历史质量控制与 430+11 共同实例

两原根的全部原收据与真实接收者按每个原键自身的1–431历史重数精确还原，取消旧额外p-rough限制；对所有加法素数先求和再用各自Theta。表原子重选与真正裸Member门分开处理，补全部401原子之外的门变化，并付款改变前缀后的全部后代实际素数盒。865项目源和207外部边界已逐字节选定；有理幂端点的2条定理单独通过本地验证。

**整项剩余：** 稳定正质量母盒的真实有号h/H收益、增强支正质量、每格106项/seed/四轮与同rho PP的价格，nonclassical/U4/full/rejected的sharp账，以及与其余根同一次430+11因果见证。431C粗上界和几何o(H_N)不替代采用常数；其余7源36条公开定理未编译。

候选源码：

- [Part5OriginalH430AllOriginalReceiptIncidence.lean](y11_history_430_11/ImbalancedChen/Part5OriginalH430AllOriginalReceiptIncidence.lean)
- [Part5OriginalH430AllReceiverPrimePassage.lean](y11_history_430_11/ImbalancedChen/Part5OriginalH430AllReceiverPrimePassage.lean)
- [Part5OriginalH430AllTaggedHistoryUnits.lean](y11_history_430_11/ImbalancedChen/Part5OriginalH430AllTaggedHistoryUnits.lean)
- [Part5OriginalH430ChangedPrefixDescendants.lean](y11_history_430_11/ImbalancedChen/Part5OriginalH430ChangedPrefixDescendants.lean)
- [Part5OriginalH430DisagreementCounts.lean](y11_history_430_11/ImbalancedChen/Part5OriginalH430DisagreementCounts.lean)
- [Part5OriginalH430ReselectedReceivers.lean](y11_history_430_11/ImbalancedChen/Part5OriginalH430ReselectedReceivers.lean)
- [Part5OriginalH430WholeMemberScreen.lean](y11_history_430_11/ImbalancedChen/Part5OriginalH430WholeMemberScreen.lean)

### Y12 · 把八组真实供应闭合到同一原始实例

十一项的原有(3,1,−1,−1,1,1,−2,−1,−1,−1,−1)权重同阈值计账：U5对全部足够小beta的原Rosser下投影和整个三角的独立delta5付款；U7/U8/U9同raw Q/rho、一次原质量及六个signed PP；两起点、两真根全430单位收据和同mask U6/U10/U11物理sigma一起进入实际下界。模块头问题已修为复用公开极限的普通import，原公开声明保持。

**整项剩余：** 采用bank的起点增益、完整h34全/拒绝正质量与原h/H许可、U5的采用密度及D_B外HB负误差、六个marked signed PP与有理上包实例、同mask product crop和四前缀parent/fallback付款；这些真实原组未到固定价格，hLower未消除。三源13公开定理均未编译。

候选源码：

- [P5OriginalFineSwitchedCosts.lean](y12_lower_assembly/ImbalancedChen/P5OriginalFineSwitchedCosts.lean)
- [P5OriginalU5SharedAttachment.lean](y12_lower_assembly/ImbalancedChen/P5OriginalU5SharedAttachment.lean)
- [P5OriginalElevenSignedSources.lean](y12_lower_assembly/ImbalancedChen/P5OriginalElevenSignedSources.lean)

### Y13 · 消除hLower/hUpper并导出无条件主定理

三个原坏数外层测试与U7/U8/U9六个标记测试，全部绑定同一Fine见证的实际附着Q/rho；三固定宽在N之前选，一个N0和同一U6/U11掩码。利用K与K+10⁻⁸的严格有理余量，固定端点路线省去三个下Simpson输入，并将三个上积分输入还原成具体有限有理上包成本。原计数下界留半严格余量，尚有费用的三份源码不等于无条件终端。

**整项剩余：** 五个原下界组的实际偏差、六个marked signed PP、三条外层同rho误差及足够细的有理价格；全实b主定理还需完整无条件L/U。三个端点特定测试不能替代所有固定b的结论；10个直接输入没有匹配的本地已安装对象，未编译。

候选源码：

- [P6OriginalFineOuterRow.lean](y13_main_assembly/ImbalancedChen/P6OriginalFineOuterRow.lean)
- [P6OriginalMarkedIntegralPrices.lean](y13_main_assembly/ImbalancedChen/P6OriginalMarkedIntegralPrices.lean)
- [P6OriginalSameRhoEndpointRows.lean](y13_main_assembly/ImbalancedChen/P6OriginalSameRhoEndpointRows.lean)

## 选源与验证边界

[独立复核记录](REVIEW_STATUS.json) 覆盖加入本记录前的 92 份发布文件，以及裸 Member 与终端原子区别的额外数学阅读。两类模块头问题、Y12/Y13 的最终直接输入和已验证入口的实际输出均已按明确范围核对。候选源码仍须编译，局部类型／内核证据仍不构成整叶验收。

[PUBLIC_SOURCE_MANIFEST.json](PUBLIC_SOURCE_MANIFEST.json) 给出每个新模块的精确字节、Git blob、直接导入、原黄色职责及各同名 API 的前后像。三份可见性修订只移除列明的 private；共同 beta 修订保留原三个公开声明并增加对所有足够小 beta 的入口。上述四份改动已做逐字源码比较，尚未编译。

对既有数学工作先复用原源和对应范围：没有重跑 17,572 行生产器、430 迭代或数值积分；没有冷重建已存在的可靠旧对象来代替复用。原九个 floor、原 R17 终端与完整 1,664 名单保持独立验收要求。历史父对象的单入口复用记录单列在验证目录，不转记为完整闭包通过。

谱支的 [精确源码选择](Y04_SPECTRAL_SOURCE_SELECTION.json) 记录已读来源与六份仍缺的注册字节。现有本地源字节和已从远端读回的 blob 分开登记；此清单不承诺公共仓库已提供可编译的全闭包。其它分支的直接选源见主 manifest。

Member 与 W1/W2 的 [去重源码图](Y08_Y09_SOURCE_SELECTION.json) 保留逐模块 SHA-256、Git blob、导入边及逐根缺件，明确区分源码可得和对象已验证。其重叠源已与谱支清单比较；这个源码检查不能代替跨模块编译。原注册的 P2N48TermOneAllPatternClosedVolumes 尚缺精确字节，未用另一个重写证明冒充恢复。

[两份导入兼容文件](IMPORT_COMPATIBILITY.json) 仅把旧 Mathlib 模块名映射到固定版本的官方目标，没有数学声明，不计入上述数学候选或已验证模块。候选 API 后像、兼容文件与全部依赖仍须在最终选源工程中重新检查。

[历史 bank 数值记录](Y10_ARCHIVED_BANK_EVIDENCE.json) 给出原 JSON 的精确身份和只读逐项比较；7/8 份原档已匹配，certify_combined_finite_table.json 的指定字节尚缺。两阶段 W1 基底界和原反馈权重的匹配，不等于种子、W2、H247 或真实 signed PP 已有解析许可。

全历史的 [选源增量](Y11_HISTORY_SOURCE_SELECTION.json) 复用上述源码图，另列新增依赖及真正 Member 门的处理。下界 [逐项依赖清单](Y12_LOWER_SOURCE_SELECTION.json) 与终端 [同实例选源清单](Y13_ENDPOINT_SOURCE_SELECTION.json) 记录精确输入；Y12 的最终证明体小修与普通导入修正均已同步。三个固定端点所需的费用、主定理对全部固定实 b 的范围和完整原 hLower/hUpper 仍分别保留。

遇到困难均先核对固定稿件：表达／API 对应、可补的省略推导和可能的实质证明缺口分别处理。可靠外部定理尚缺 Lean 绑定，不据此判定稿件命题为假。严格截断、同一 rho、同父 Theta、固定宽与移动宽、各自独立 reserve 和选择阈值次序均保留。

未派发远程工作流；证明 goal 和定时续推保持暂停。本包仅提交可审阅源码及其真实状态，不改变看板颜色。
