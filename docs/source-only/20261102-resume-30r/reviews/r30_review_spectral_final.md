# R30 — 真实谱源及最终实际前提独立复核

2026-11-02，`/root/r30_review_spectral_final`，明确任务设置 `gpt-6-astra/max`。范围为 R20–R24 / D18–D22，以及既有最终 `hLower`、`hUpper` 消费者的实际前提审计。**下文列明的局部新增证明通过限定 `SOURCE_REVIEW_PASS`；完整 D19–D22、Eq.(24)/(25)、实际 uniform 7/32、同 rho PP 及最终 hLower/hUpper 均 HOLD。** D18 的原 family 全模数与实际 test 资格已供应。此结论接受实际局部推进，不授整条黄色节点完成；最终发布后的字节审计另列。

只写本文件，未修改作者、生产、旧批次或原稿；未运行 Lean/Lake/编译器、CI、有限 guard、数值 replay 或 Git，未派子代。`SOURCE-ONLY / compiled=false / kernel_verified=false / formal_credit=0 / finite_guards=UNEVALUATED`。本文的限定静审结论不是 elaboration、kernel acceptance 或递归 import closure 验证。

`R/Q/P/O/M/K/J` 指 `docs/source-only/20261102-resume-30{r,q,p,o,m,k,j}/`。工作根为 `E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation`。先读 R BRIEF、Q03 `NEXT_DIRECT_PROOF_REVIEW.md` 的 D18–D22、Q19/Q20 REPORT、Q29/Q30 最终独审，再直接读原稿和真实源码。检索覆盖 production、所有 source-only 与忽略的 `.lake/proof-continuation/source-reviews/drafts`；重复快照不计作不同证明。

## 原稿与恢复基线

Body 为 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`，Medium/Classical 为相邻 `paper/source/modules/distribution-medium-completion-20261010.txt`、`final-classical-input-correspondence-20261010.txt`。独读 Body:207–254,343–354、Medium:299–424,463–483、Classical:29–137，原要求是同一个原 arithmetic source 的 normalized Kuznetsov、两 cusp Fourier 产品、逐 dilation 的 ABL、全 singular-cusp continuous quadratic form、实际 A/J/regular/gap，以及六片/zero/tail/完整费用。它不要求新的任意 PacketData 定理，也没有把 coefficient/Bessel energy 等同于 automorphic energy。

恢复后实际读取的 `BRIEF.md` 为 3682 bytes，`DISPATCH.json` 为 10461 bytes，非空；后者列明 30 个任务及 R30 范围。最初按 `.md` 后缀未找到 DISPATCH 是路径选择失误，未算作空文件检查。

| 基线文件 | raw SHA256 |
|---|---|
| R `BRIEF.md` | `3643ffc4134691ee32a782a2ff1afa9c351dd9fd5c1686f667fd7159b63baa67` |
| R `DISPATCH.json`（恢复时） | `97c28b6069e38b62f6b4ccd9d2c88db85cd66467ea4ef3d7446dcecd2729520c` |
| Q03 `NEXT_DIRECT_PROOF_REVIEW.md` | `5645cbf9204d7ed41cd458ce5a46c4b5f9ccd72817c37d437c82f8e032c18f78` |
| Q `reviews/q29_review_automorphic.md` | `f015c341663dba8796d1da8aa6608bcbfafb14d657ff42655014176228445494` |
| Q `reviews/q30_review_history_final.md` | `436780998c45664f07328cbf7dc4d6b7648144df8ac30c040b8c51e326b2cd2d` |
| Body | `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` |
| Medium | `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7` |
| Classical | `9604bfb8fdf7325205c8ebe431c7c5e977a3e5bea07e79b8d209548e1a4069db` |

## R20：实际 finite-c → 全正模数

已逐行读 `full_modulus_test_support/Part3OriginalFullModulusSupport.lean`、`Part3OriginalFullModulusAssembly.lean` 和 `Part3OriginalFullModulusTestJets.lean` 的 proof bodies，复查 Q 的 `chartModeAtom/original_chart_atom_hasSum`、P 的 normalized scalar、production `normalizedF`/cutoff 和既有全族 HasSum。

支撑链有实质内容。原 bump 的真上端为 `5/2`，六片 `N≤4*C`；因此每个正 `c∉Ioc 0 floor(10*C)` 都满足原 `scaledDyadicCutoff N c=0`。新源先用此事实在 **unseparated normalizedFrequency** 层面证明新增项真零，统一扩大到 `floor(128*C)`。随后对每个 separated mode，用实际 `v,w,z∈[1,2]`、`q/Y=chartT(c/N,v,w,z)≤2/(c/N)` 及 χ 非零支撑 `q/Y>1/16` 得 `c<32*N≤128*C`。统一 carrier 先于 z/n/p/j/ell、两个 Z 和符号选取。

Assembly 的 `fullModulusRow_hasSum` 从这个共同有限支撑导出真正的正 c 级数收敛，明确剔除 c=0、保留 `(c,z)=1`；`fullChartMode_eq_enlarged` 只交换有限 p/c 求和；`enlargedChartPhysical_eq_original` 逐个新增 unseparated summand 消零；`fullChart_hasSum` 使用 Q 的真实点态重构，并在原 z/n/p 全族求和。`full_minus_capped_chart_hasSum_zero` 的结论是**整个带 actualCoeff 的 Fourier correction 和为零**，没有宣称 Q 的单个 capped mode 等于 full mode。

`original_six_eq_remainder_and_full_modulus:248` 保留原六尺度、同一 `globalCutoff`、两个固定 Z、同一 completed interval/phase 和 Q 的 **原样 `sixRemainder`**。故这个 modulus enlargement 本身没有新增须估计的 endpoint error；它也没有支付既存 zero-y、m=0 或 hard tail。

TestJets 的 `spectralTest_tsupport_strict:33` 用真实 χ 的闭支撑位于严格正区间，而非把一个粗 open support 取闭包后冒称仍严格；`:57` 给全部固定阶端点 jet 消失。`:65,72` 证明 test 及 test/q 的 Lebesgue 可积，后者用零邻域外的连续非零分母延拓。`:129,143` 的 Leibniz/缩放公式实际保留 `Y^(-n)` 和 modeFrequency；`:203,246` 得 `C_n*(1+|ell_0|)^n/Y^n`，C_n 只依赖原固定 cutoff 和先选阶数。`:262,279,307` 把真实 actualCoeff 的导数质量接回既有 actualW 与 uniform weighted-l1，明确费用 `(1+rho)^(4*(n+3))`。四阶对应 `28*eta` 的既有物理权重，须保留但不重复加收一次；它不能免费并入另一条 `q14` 账目。独读 pin Mathlib iteratedDeriv 的乘积、缩放、支撑 API，与使用顺序相符；仍未执行 elaboration。

这完成 D18 所需原 family → full modulus 和实际紧支撑光滑 test 资格的限定源供应。未发现当前数学链的确定阻断。它不供应 normalized trace、Bessel 变换谱估计、A/J 或父目标 uniform_spectral。

## R21 与 R23：两种不同的符号转换

已逐行读 R21 `actual_kuznetsov/Part3OriginalSignedTraceInput.lean`，包括新增 `traceNegative/traceIndex_eq_signedY`。已复查 production `Part3ActualReciprocalSquarePoisson.lean:388–400` 与 J `Part3OriginalNonzeroCuspOneSource.lean:273–314`。

R21 在完整 primary/Poisson 块上固定 residue sign、y sign、Poisson sign 的复合符号，实际使用 `S(-m,n)=S(m,-n)` 令 completed index 为正；第二 trace index 是 `±a*(signedY*(nu*n))`。反向 cusp 转换相位为 `e(-traceIndex/z)`，依赖 n/z/原块而不依赖未来 c/p/height。`traceBeta` 的原 beta 与共同 m phase 均不共轭。外因子为 `M*sqrt(Z)`，内分母为真实 `c*sqrt(z)`，测试变量为 `4*pi*sqrt(p*abs(traceIndex))/(c*sqrt(z))`。`original_chartModeAtom_eq_normalized_cuspOne` 是原 Q atom 的实际算术侧字典；仍以 matrix-defined cusp sum 结束，未构造 normalized spectral trace。

已逐行读 R23 `actual_spectral_energy/Part3OriginalSignedNativeCuspFourier.lean` 及两份 repairs；独立文本比较确认两旧源的唯一替换为 `AddCircle.fourier* → _root_.fourier*`。另读 exact mathlib pin 保存的 AddCircle 定义与 `integral_conj` 使用点，确认 Fourier 声明位于根 namespace。

R23 的对象是 Γ0 不变上半平面函数在旧/新 cusp-one chart 中、固定高度 y 的 normalized-Haar Fourier 积分。共轭恒等式同时改变函数和 Fourier index；负行的正 index 表达同时共轭原 `blockBeta` 与函数。两 sign 的 `cuspPhase` 正确取消实际 chart translation 相位；原 full nCarrier、重数、coprime gate 和 occupied level 保留。它没有假定单个 form 的系数为实数，也没有给 spectral basis 的反射完备性。**fixed-y Fourier coefficient 尚未识别成 height-independent automorphic R(n)**；因此本地恒等式不能供应 A/J、regular cumulative 或 Kim–Sarnak。

另独读 R21 `Part3OriginalFullModulusCuspInput.lean` 全文。`bareCuspTerm_hasSum:49` 直接用 R20 的 **test 自身**支撑证明裸 c 级数有限支撑，未从 `beta*series` 的零值或收敛除以可能为零的 beta。`:80,102` 把 R20 实际 fullModulusRow/fullChartMode 精确写为 `M*sqrt(Z)*commonWeight*traceBeta` 乘上述裸 cusp sum；有限 z/n/p carrier、符号及 coprime gate 原样保留。这避免了一个重要的零系数漏洞，但仍是算术侧。

R21 REPORT 的谱端常数与 Drappeau v4 (4.9)–(4.19) 相符：weight-zero 正号 J-difference 变换、负号 K 变换，Maass 的 cosh 分母、全 singular-cusp 连续项外置 `1/(4*pi)`，正号 holomorphic 的 `Gamma(k)` 与高度 `k-1`。此项核对的是报告所列的经典目标，**不是新 Lean 文件已证的恒等式**。对实际 source 求和后 infinity functional 的权重须先共轭，再在谱乘积中取共轭，原 beta 保持原值。

另逐行核完 R21 最后新增 `Part3ActualMaassWhittakerNormalization.lean`。旧 `quotientRho` 是 `sqrt(y)*K` 的真实 Fourier 振幅，旧 `quotientR=sqrt(abs(n))*quotientRho` 不能按其 header 直接认成文献 R。新源 `:63,68,72,79` 明证 `rho_W=rho_K/(2*sqrt(abs(n)))`、`R_W=rho_K/2=old quotientR/(2*sqrt(abs(n)))`；`:97,106` 实际调用旧 quotient 的物理 K 定理，显示同一个 Fourier 积分等于 `rho_W*2*sqrt(abs(n)*y)*K` 或 `2*R_W*sqrt(y)*K`。`:116` 的真实局部乘积带 `1/4`，没有谱求和。`:130,165` 从原 cusp-local PDE/periodicity/strip L2 和已有唯一 imaginary-K 结果导出规范幅度的存在唯一性，保留 signed n、tau=0、严格 y>Y；未在 imaginary-K 零点除法，也未将 K-shape 当输入前提。代码没有另定义 W 函数，其标准 Whittaker 身份通过下列一手文献核定；同一 full basis/固定 scaling 的完整谱组装仍未交付。

独核 [DLMF 13.18.9](https://dlmf.nist.gov/13.18.E9) 的 `W_(0,nu)(2z)=sqrt(2z/pi)*K_nu(z)`，代入后得到 `W_(0,nu)(4*pi*abs(n)*y)=2*sqrt(abs(n)*y)*K_nu(2*pi*abs(n)*y)`；ABL §3.2 明确沿用 Drappeau 的 normalization。上述因子转换是必要的真实来源修正，不能再将其列作全然未写，也不能将 cuspidal strip-L2 输入直接套给非 L2 的 incoming Eisenstein。imaginary 链的 d4d0a/c51501 安装 HOLD 保留。

R21 是 Kloosterman 的算术 sign involution，R23 是实际 Haar Fourier integral 的共轭；二者数学断言不同，不重复记功，也不能相互替代。两者当前限定数学链未见确定阻断；真实 trace 和 A/J/regular/ABL/gap/energy 前提消除数均为 0。

## R22：真实 principal completed 子族，不是全 continuous 谱

已逐行读 `oldform_continuous/Part3ActualPrincipalOldformRemoval.lean`、`Part3ActualPrincipalCuspOneRemoval.lean`、`Part3OriginalPrincipalTraceRow.lean`，并独读被实际调用的 hidden `20261026b-FrickeNonzero/Part3CompletedIntegerNonzeroFourier.lean`、`Part3ActualFrickeNonzeroFourier.lean` 与 production `Part3ActualFrickeCuspPhase.lean`。新源使用实际 completed E*、整数 dilation、真实 finite canonical oldformTerms 及 complementary indices，不是指定任意 rho 后证明乘法公式。

第一文件 `principal_dilation_Gamma0_invariant:66` 确认 d|N 的实际变换不变性；`completed_integer_fourier_eq_principalAmplitude:106` 是真实正高度单位周期 Fourier 积分。主 amplitude 为 `1_(d|n)*sqrt(d)*normalizedDivisorAmplitude(n/d,s)`；`:154,177` 的 n-removal 实际消费原 Q20 行的 `(abs(a)*nu,z)=1` 和 `(n,abs(a)*nu)=1`。critical-line 单项幂范数为 1，给出的 `tau(abs(a)*nu)^2` 平方成本包括 t=0，未在中心除以 K/Gamma/zeta。

`:236–317` 将相同 multiplier 穿过原 finite reflected oldform list 和原 Euler normalization，得到实际 level-z Fricke Fourier integral；所有 complementary dilations 保留。第二文件将这一 principal family 实例化进原 Γ0 section，复用 `sigmaOne=T*W_N*T_(1/N)` 与真实 normalized Haar coefficient，得到 signed `e(j/N)` 和原 primary row 的相位取消后 removal。这里处理的是 principal completed E* 的固定高度系数及明确 K amplitude；没有将它重命名为 raw Whittaker rho 或一般 ABL 的 R(n)。完整 character-pair fibers、formal norm 分母、全 cusp Plancherel、各 Maass/holomorphic oldclass 的真实范数仍未供应。

第三文件 `original_traceIndex_principalFourier:74` 消费 R21 的完整复合符号，字面接到该 principal cusp-one Fourier 积分，保留径向 argument 中的 A*n。`:116` 的 finite row removal 用真实 `traceBeta`、Q modulatedBeta、原 full nCarrier 和 residual signed n phase；`:135` 给该实际单 incoming channel 的 `tau(A)^2` norm bound。该子族的 multiplier 可共同提出，因为已对这个具体 divisor amplitude 证明；它不要求、也未声称一般 Maass oldclass 的每个 dilation multiplier 相同。整个证明不接受目标范数或谱恒等式前提。

独核 historical `batch34/dots-api-delivery-holds.json`：整数 Fourier 旧源的确定问题是过宽 `simp_rw [add_mul,mul_assoc]`。修复副本只加 provenance 注释并把该项限定为 `mul_assoc (2 * (Real.sqrt y : ℂ))`，原所有声明/假设不变。fixed65 的排除记录及原 frozen bytes 均保留。另在新 CuspOne 和 inherited FrickeCuspPhase 中发现 `AddCircle.fourier*` 根 namespace 问题，通知作者后已复核修复：新 body 使用 `_root_.fourier*`；FrickePhase replacement 除 provenance 注释外，唯一变化是该 namespace 前缀。复用 R23 两份 base repair，未修改生产源。这是 class I 的确定来源修补，不算新数学功劳，也不据此解除所有 inherited API HOLD。

最后 TraceRow 的 `prefixPeriod` 对应 `OriginalSimultaneousPrefixCompletion20261102`，作者已在第24行显式打开此 namespace；未改数学体。独审还发现 REGISTRY 把注释中的 `staging: ...` 误计为 import，作者已修正解析并重冻。这个元数据修正不改变实际依赖或数学结论。

## R24：原 sixTail 的真实统一支付及未付 zero 费用

已逐行读 `uniform_seven32/Part3OriginalSixTailBinding.lean`、`Part3OriginalSixTailPhysicalPayment.lean`、`Part3OriginalZeroLaneBinding.lean`，并复查 hidden 六核 hard-tail 与 production completed source mass 的实际声明。

SixTailBinding 的 `sixRemainder_eq_zeros_add_tail:81` 对同一个 Q remainder 精确拆账：zero-y 保留全 completed m；m=0 只在 nonzero-y 源上；sixTail 是 nonzero-y 的共同 hard window 之外。`:89,152` 在取范数前消费原 primary partition，将全部 row 汇回原 source，因此不会额外付一次 primary/sign/dyadic multiplicity。`:102,134` 核同一个 `J=ceil((C/B)*x^eps)` 与 `R=x^eps/10`；原六片为 M=B/2B、N=C/2C/4C、原 c≤10C，边界含等号方式一致。`:169,185` 实际证明原 lambda/omega 范数与 rawLabelBudget，`:197` 接既有六核 Schwartz 估计，没有 hEnergy 输入。

PhysicalPayment 的 `tightOriginalData:51` 使用原 tightPoissonAtlasBlock，保留 atom/key/small/rectangle、两平滑标签、三个 polarization 和共同 s-frequency。`:121` 用真实 occupied-key 界给出 `C^2*rawLabelBudget≤21632000*x^33`；其粗多项式只支付 Schwartz 尾，不用于主谱能量。`:218` 对每个先给 A≥0、eta>0，先选固定 dord≥2 且 `34+A≤(eta/2)*(dord−1)`，再选 `X=max(1,21632000*K)`；X 在 b/sigma/kappa/c0/atom/key 等所有移动参数之前。于是同原 eta/2 cutoff 下每个 tight original source 的 sixTail≤x^(−A)。这是实际统一尾项叶子，不能再仅称“抽象 coefficient tail”或“单频尾”。

ZeroLaneBinding 的 `originalZeroY_eq_zeroPiece:57` 与 `originalZeroM_eq_native:95` 是原对象的实际来源识别。y=0 已接有限 native 界，但显式留下 `72*M*N*F*H*S*tauEnvelope`；nonzero-y,m=0 保留 `zeroFourierMass`、residue divisor maximum、完整 output support cardinal 和 nativeCoefficientNorm。没有把这些粗量称为归一化小幂付款。`:127` 结合 R20 得字面 `smoothSix=sixZeros+sixTail+Fourier(fullSixMode)`，R20 的零 correction 不重复计费。**完整 normalized zero-lane payment、全真谱 Eq24、原源统一 7/32 与 Eq25 返回仍 HOLD。**

最终 SixTailBinding:227–229 的求和提取已改为 `unfold sourceAbsMass; rw [← sum_mul]`。另外两份 repair 独立与 production `Part3ActualCompletedHardTailMass.lean`、I `spectral_eq24/Part3ActualZeroPoissonNativeSource.lean` 逐字比较，唯一正文差别分别为 `rw [Finset.sum_mul]` 与 `rw [sum_mul]` 改成逆向。原式是和内公共乘子提取，逆向与 pinned Mathlib `Finset.sum_mul` 声明相符；旧源未动，三处都属于确定 API 方向修补，不是新的尾项或零项数学付款。

## 真实谱已有来源与不可替代边界

已独立读以下真实边界，不按文件名推断内容：

| 实际定义/声明 | 可复用内容 | 不能据此关闭的目标 |
|---|---|---|
| `ImbalancedChen/Part3ActualLiteralPacketIntegral.lean:210–231` | 有限 carriers、归一化坐标与给定连续 kernel 的重构 | 任意 PacketData 不构造 automorphic realization。 |
| `ImbalancedChen/Part3ActualCommonHeightKFactorizationFullGram.lean:47–50,103–115` | completed coefficient sum 与实际 K transform 的有限/积分分解 | 无两 cusp Fourier 因子；其模平方不是真谱能量。 |
| K `exceptional_j/Part3ActualExceptionalJPacketAdapter.lean:64–68` | 给定 packet 改用共同 J/q kernel | 覆盖 kernel 会删除预塞入的 Fourier product，不能补救 full trace。 |
| K `regular_continuous/Part3OriginalContinuousPacketExhaustion.lean:231–312` | supplied raw rho 下正确的 infinity 共轭、`R=sqrt(n)rho`、全 cusp `dt/cosh(pi*t)`、外置 `1/(4*pi)`、耗尽 | 实参仍是 raw rho、local L2、两累计界和 transform bounds；不是全 cusp 临界线实现。 |
| `ImbalancedChen/Part3Gamma0ActualUnboundedScalarMeasure.lean:19–22,38–62` | 真 Γ0 resolvent 的非负 scalar measure 和 norm² 总质量 | 保留可能的 λ=0；无 cuspidal basis/normalized trace/975/4096 gap。 |
| hidden `20261026b-GammaCompactness/Part3ActualFullCuspEigenbasis.lean:94` 与 `20261026b-AffineRellich/Part3ActualFullCuspLambdaSquaredDomain.lean:45,84,119` | entire 原 ActualFullCuspL2 的 HilbertBasis；真实 native graph、lambda² domain 与 operator Parseval | 保留 be3646/0f1f transitive API HOLD；尚不等于全 continuous/holomorphic、normalized trace 或 A/J。不能再泛称完整 cuspidal operator basis 的 source body 不存在。 |
| hidden `20261026b-ZeroModeHardy/phase16-spectral-kernel/Part3ActualCuspSmoothEigenprofileFamily.lean:42,50,66,106` | 同一 full basis 的一致光滑 Γ0 本征 profile、原 finite quotient/carrier norm=1、先于 index 的 compact jets | 保留 eigen-regularity 等 API HOLD；不是所有谱支的 Whittaker-normalized trace。不能再称 smooth realization 尚未写。 |
| hidden `20261026b-CuspWeakModes/Part3ActualEigenOriginalFourierClassicalModes.lean:141` | 每个实际 normalized cusp 的 classical Fourier C²/ODE，所有整数 mode 在同一个 conull 高度集与原 frameFourier 相等 | 没有以任意 canonical L2 representative 在零测水平线上取值；不自动给 trace identity。 |
| hidden `20261026b-RealCuspK/Part3QuotientRealKFourierCoefficient.lean:63`、`20261026b-ImaginaryKLimitPoint/Part3ActualImaginaryMaassFourierK.lean:35`、`Part3CuspLocalImaginaryKShape.lean:36` | 实际 quotient/PDE/strip L2 到 real-order K、signed imaginary-order K，均包含中心参数；后者用远处非零 anchor 而非在任意高度除 K；本轮 R21 已补正确的局部 Whittaker 幅度转换 | imaginary 链保留 d4d0a/c51501 derivative-L2 INSTALL HOLD；尚须同一 full basis/固定 scaling 的完整连接与所有谱支，不能由局部系数转换宣称 normalized trace。 |
| `Part3ZExceptionalParameter:74` 及 scalar polynomial 源 | 给定 gap 后的 7/32 参数代数、Eq24→Eq25 标量运输 | 不证明实际 gap 或 Eq24 真正二次型输入。 |
| hidden `20261028-Medium-Polynomial-Sol6/Part3ActualSixKernelCommonHardTail.lean:33`、production `Part3ActualCompletedHardTailMass.lean:84,111` | 真六核 common hard tail、sourceAbsMass 与 rawLabelBudget；R24 已实接 tight OriginalData 的统一尾付款 | 不因此支付两种 zero lane 或主谱二次型。 |

本轮重新打开并核对一手文献：[ABL v1 Lemmas 3.1–3.2](https://arxiv.org/pdf/2005.13915v1)、[Pascadi v3 Theorems A/J](https://arxiv.org/html/2404.04239v3)、[Drappeau v4 Lemma 4.3/Proposition 4.7](https://arxiv.org/pdf/1504.05549v4)、[Young v2 §8/Proposition 8.2](https://arxiv.org/pdf/1710.03624v2)。ABL 的 multiplier 可随 dilation 变化；Maass 的平方幂是 `(|a|nu)^(7/32)`，holomorphic/continuous 可除去该幂。A 使用固定 level 的任意复系数；J 使用共同 interval/phase 与 infinity scaling Id。Drappeau 的 regular 输入含 holomorphic、Maass、全 singular-cusp continuous，且长度≥1/2、T≥1。这些文献不是新增 Lean axioms 或已安装定理。

Young §8 明确 t=0 可能例外；普通 t≠0 的 formal fiber 换基可在连续积分中按 `{0}` 零测处理，不能要求中心 fiber 无条件线性独立。这与 Bessel transform 的 t=0 limiting value 是两个不同义务。此区别来自实际 primary source，未给原稿增设更强定理。

## 最终 hLower / hUpper 实参基线

直接独读 `ImbalancedChen/P5OriginalFixedDensitySupplierAssembly.lean`、`P4BCurrentSmoothBadUpperSuppliers.lean`、`P6OriginalEndpointAssembly.lean` 与 `CurrentMainTheorem.lean:278–298`。最终接口从未因局部谱进展自动成为无条件定理。

P5 的 `eventual_D12_of_fixed_original_grouped_suppliers` 仍接受八组：`hstarts,h34,h5,h6,h7,h8,h9,h1011`。starts 是实际 `3*U1+U2`；h34 是原两组 table gains 的 U3+U4；h5/h6 保留真实计数与同 E；后四组必须消费实际 density/PP/原 harmonic 与 near-cap 来源。P5 已内部供应数值 coefficient 条件，重复写一个总消费者不消去任何上述实参。

P4B `current_realBad_upper_of_actual_density_and_uniform_smooth_PP:40–52` 同时接受 **同一** `epsilon/retain/cap`、`attachedUpperModuli`、`attachedUpperCoefficient` 的 `hdensity` 与 smooth outer-ramp `hUniformPP`。每个固定精度先 N→∞、再精度→0；不要求跨所有精度使用一个固定 rho，也不要求 upper87 与 lower441 共用额外的统一 history 类型。

下表由上述实际消费者的直接阅读、本审 R20–R24 proof-body 审查，以及已读 R25–R29 数学/范围正文交叉确定；最终冻结 pin 见末表。本审没有冒称重审 R03–R19 的全部新证明体。

| 最终实际入口 | 本轮真实推进与准确剩余 | 实际最终前提消除 |
|---|---|---|
| `hstarts`，P5:123–125 | R11 固定 box 的真实递归 carrier、floor/alpha/p5z 转换和 R13 全 ordinary U3 classical-tail rowError/trueTheta 起点已存在；原 adopted 四轮 `2327/100000`、旧 H/h 许可及完整 starts/count induction 仍缺。ordinary tail 不直接供应 `3*U1+U2`。 | 0，HOLD |
| `h34`，P5:126–128 | R14 full Member/401 queries 的首分歧 strips 与 native 联合可测性；R15 两根完整 amplitude−H430 weighted L1；R16 真实106 bank parent rows 规范质量≤12、Theta=0、literal430 preceding profile 阈值及保留 unpaid base/absolute-coefficient 的 localBudget 恒等式已供应。完整 typed Member/Buchstab/source licences、正/等号层母质量、实际 hlocal 与同一441实现未供应。 | 0，HOLD |
| `h5`，P5:129–130 | 18 short-word unit 与 Γ16–19 的 literal nonunit cost 字典可复用；Γ5 常 a0 square identity 不是 quadrature/unit 付款。完整 causal selected/inherited/adopted count 来源、Γ5 和 Γ9–15 grouped costs 仍缺。 | 0，HOLD |
| `h6`，P5:131–132 | 固定 box same-mask carrier、true alpha 与原 `/2`、W2 `4+1+3+4` 的 `/5` occurrence 运输有实进展；原 root/full/selected/adopted 与完整 same-E L6 下界仍缺。W1 开/半开端点、W2 原 N-window 与排 `p|oldProduct` 的 child 字典不能混同。 | 0，HOLD |
| `h7`，P5:133–135 | 原 rank3/rank4 来源与 source mass 已有；本轮 upper rank2 rough-prime reserve 精确零并不供应这里原 PP3+PP4 signed sum 的分布/同 coefficient density 与 smooth approximation。 | 0，HOLD |
| `h8`，P5:136–138 | 原 rank3 与 unit/diagonal arithmetic pieces 可复用；其实际 hdensity/hPP 未由 R19 或局部谱转换供应。 | 0，HOLD |
| `h9`，P5:139–141 | 原全部三 branch 的 ordered physical signed decomposition 已存在；各原 sharp/smooth source 的许可与 same-rho branch 分布仍缺。 | 0，HOLD |
| `h1011`，P5:142–145 | 原共同 sixteen-policy/near-cap support、主项近似和 lowered-singleton correction 可复用；共同 actual source 的完整 PP/joint raw endpoint 与最终总供应仍缺。 | 0，HOLD |
| `hdensity`，P4B:40–44 | R03 全87原行/ideal-prefix 字典、R05 all292633 indexed reserve、R06 局部14/13 signed continuation、R07 普通 catalog5 全域付款、R08 两个具体对象、R09 finite-admission compiler 子族与 R10 same-witness catalogue 均有实进展。全87 actual parent/common history、独立 oldBranchDefect、完整 All22、全部 changed 到已付 catalogue 覆盖及总 `<u_c`、其余同 schedule density 总 `<3u_d/4` 仍缺。 | 0，HOLD |
| `hUniformPP`，P4B:45–52 | R17 joint absolute upper/zero-Theta、R18 chosen-grid 及实际 all-mother per-row conductor、R19 原 upper ramp rough-prime exact zero、R20–R24 局部谱接缝与原 sixTail 付款可复用；同一最终 attached coefficient 的 active support/analytic cover、remaining trim/proper-power/retained modes、全允许 branches/families、positive-Theta 相对误差与真实全谱能量仍缺。 | 0，HOLD |

交叉审查末轮采用 R25/R26 对 R07 新尾项三源的最终独审纠偏：真实原 `smallOmittedSum` 已在普通 T=1 source 下支付，`exists_complete_actual_catalog5_approx` 不再保留尾项；不应沿用较早 `eta + abs(smallOmittedSum)` 为最终阻断。本审又直接抽读该新定理 `SmallThirdPayment:167–298`，并完整读 R10 `P4AActualCompleteCatalogFiveCapPayment.lean`：`:43` 消费完整 catalog5 的 `eta/2` 和两 cap 合计 `eta/2`，对同 d/m/buffer 得 `catalogFiveCapError<eta`，同时调用 R08 原4/5 signed gains，无 hGap/目标 tail 小性输入；新结果替代较弱的中间目录，费用不能相加。该 ordinary source 进展不自动支付 beta 附接、完整同 rho 总账或两个 reserve。R06 的局部新十四树内部已花 beta 的 `eta/2`，最后不能重付或当作 free input。R17 的 joint upper 绝对误差不等于正族 `epsilon*Theta`；零 Theta 绝对为零是真供应，但不建立正 Theta 下的统一下界。R18 per-row full conductor 调用已真实供应，不能再次仅列为 norm/level 准备；完整外层求和仍是独立义务。最终实参消除数为零的交叉结论不因这次局部加强而改变。

因此 P5 八组、P4B 两组最终实参本轮**没有任何一项完全消去**，P6/CurrentMain 中 `hLower/hUpper` 仍显式。该判断未要求任意 signed sharp coupled-domain 强化 PP、完整 Python/facet 穷尽，或不同上下界构造共享人为 history 类型；只保留原稿真实必要来源与费用。

| 最终接口基线文件 | raw SHA256 |
|---|---|
| `ImbalancedChen/P5OriginalFixedDensitySupplierAssembly.lean` | `716aa10228dfa7fefe8cd30bc0e878882d35bb0b14c355c229ff50d6bd4d5096` |
| `ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean` | `0eddc7dfde67bb42021e9f4176c1827e5a28966a5024f79930f1b59221304d59` |
| `ImbalancedChen/P6OriginalEndpointAssembly.lean` | `7c22fc14a97425b0c5b5a215c9655cc90b9464250f41c300da5845ceea7aebd0` |
| `ImbalancedChen/CurrentMainTheorem.lean` | `68a2a3aad8ccdc73ed8e5076e31b9984bc659c307d71150920a71b5fc98f067d` |

## 最终作者源码字节

以下 13 份新 Lean 与 6 份最小 repair 均直接读取并重新计算 raw hash；R21 第三源、R22 TraceRow namespace 修正及 R24 三处 sum_mul 方向修正均包含在最终阅读中。路径均相对 R 根。哈希只固定本次独审字节，不意味着安装、编译或完整递归依赖被验证。

| 文件 | bytes / lines | raw SHA256 |
|---|---|---|
| `full_modulus_test_support/Part3OriginalFullModulusSupport.lean` | 11662 / 232 | `d6b50adc19fa821ae11f410e0cbdc27dd1e82d84f65c346686957963c18f8cbf` |
| `full_modulus_test_support/Part3OriginalFullModulusAssembly.lean` | 13590 / 287 | `9f8ed52f1cae06208830c7f98d148e9fbbf2e8ce6c3931ca9bcee9d0f01fa121` |
| `full_modulus_test_support/Part3OriginalFullModulusTestJets.lean` | 15502 / 327 | `cf4c4840f8bcdfa778848bb1ded656636dccf5e249e9f957092955a5f7b262dd` |
| `actual_kuznetsov/Part3OriginalSignedTraceInput.lean` | 8826 / 180 | `2ba47c389ce2ffab05eb090c29877a678cde69b23b180e8875840905fe588341` |
| `actual_kuznetsov/Part3OriginalFullModulusCuspInput.lean` | 5848 / 123 | `8c1b404b0b594d792cf21f9a861b3cdc19322fa9077e97451271cf2021caf877` |
| `actual_kuznetsov/Part3ActualMaassWhittakerNormalization.lean` | 9214 / 190 | `ec750f6b9648087254185628163e3bd3e147fdb06424383ae6d236de1774cfba` |
| `oldform_continuous/Part3ActualPrincipalOldformRemoval.lean` | 16048 / 321 | `e01268ddc23f20b9f4e9a284e60cdc368e9e66c8c93bec9cb1b1f60cf70401fa` |
| `oldform_continuous/Part3ActualPrincipalCuspOneRemoval.lean` | 8472 / 181 | `ed8455fa89aee48ad661004e2774a1d5accc588fa4dda981f8405e277689e085` |
| `oldform_continuous/Part3OriginalPrincipalTraceRow.lean` | 7133 / 149 | `734d59fb3b38808eb64c31843464440fbb6f22c0ded12edcbaa9c899d8550650` |
| `oldform_continuous/repairs/Part3CompletedIntegerNonzeroFourier.lean` | 9821 / 201 | `f7ce04999654c36596a8ec68dd0b73d6c34b77c0f82c1a787ab973152d5b3724` |
| `oldform_continuous/repairs/Part3ActualFrickeCuspPhase.lean` | 8053 / 150 | `749882d348253efdfb33387299a30653f0484b0810eeac84a761c2433609fddf` |
| `actual_spectral_energy/Part3OriginalSignedNativeCuspFourier.lean` | 10472 / 217 | `766d00b552b66d4467d857e9e02553fc9431410d9028276fdd491f45ec747336` |
| `actual_spectral_energy/repairs/Part3CuspTranslationFourierPhase.lean` | 4931 / 114 | `5aa2566f75a7ff66b58ee848f9ecad3384a7498f85af6f4970f32d9de1b85756` |
| `actual_spectral_energy/repairs/Part3ActualCuspFourierSection.lean` | 9444 / 217 | `7cc15af0858e3df58f09c0b94463ed2475629119a291c1045a37067036ebe36a` |
| `uniform_seven32/Part3OriginalSixTailBinding.lean` | 11645 / 239 | `a2e29298bed7a880140cb4cfa6160baa03e65809d75af579eea31a9c4d5f8ab1` |
| `uniform_seven32/Part3OriginalSixTailPhysicalPayment.lean` | 13347 / 272 | `a19d6ca03e92790c891fc6c062c3004c5b67f466cd64793652e6bcccac397df7` |
| `uniform_seven32/Part3OriginalZeroLaneBinding.lean` | 6582 / 138 | `6d94d7b41a4938d45074e9558bf69fd41f2b9a0bbdb2751b5361c07e55373697` |
| `uniform_seven32/repairs/Part3ActualCompletedHardTailMass.lean` | 9914 / 178 | `b162d847347dfc2398fe500e1bde453834352d67a81b99be952b7596431468e1` |
| `uniform_seven32/repairs/Part3ActualZeroPoissonNativeSource.lean` | 9183 / 174 | `e8ce433351fa313416d3e406be8f8b9b0b90d055a9fbd8520397ce9a33f16df6` |

末次独核原稿 Body/Medium/Classical 以及上述 P5/P4B/P6/CurrentMain raw hash，全部仍等于本文基线，没有作者修改生产消费者来移走前提。

| 作者包 | REPORT raw SHA256 | REGISTRY raw SHA256 |
|---|---|---|
| R20 `full_modulus_test_support` | `711fccf507f9815efe7d34ba366adcdf53d29e57013dd7cdcc98fc08f9453fe3` | `5aeb3442dc89bb58efef65e44cd77959b0da0311edae3ee5af51fb5267f0f9a6` |
| R21 `actual_kuznetsov` | `2199a419bcd8939daf81dc5be6d89650927bea54a026aafa0e97a9ac4d7a8371` | `68e3e82835863433d182a798f4ec0d7f1fa1329a4b7008b952a4a966f1488bab` |
| R22 `oldform_continuous` | `a78ad7f95e62b7ae055845b93ce0ee644947cbb4c4c0aa90477fd14a870e3152` | `ec97e5230edb1062c377d82885e4cf6a006ab74c670bfae77f91d48f797aadd9` |
| R23 `actual_spectral_energy` | `82add18db7204bc8963aad3be9f4efcc230ce06ca106e199e0f320dde8202314` | `8cdb0b03d2b1f476d035ee7ed7ad20cb64d69d89983c43a4d8a315dcaf89c77a` |
| R24 `uniform_seven32` | `4254df2405a45a74adf04eb2df5d483752c767e23577915720b651c33b32ceed` | `2a815e8c8eb7ed99dae8ae5130bfb36ac44d9742f14192952b735950abf3140b` |

独立元数据核对覆盖 R20 的42条 path/hash 与120个声明（其中54个提供精确行号，其余按名称核）；R21 的72条记录/253个声明行；R22 的61条记录/709个声明行；R23 的44条记录/145个声明行；R24 的76条记录/642个声明行，其中76含13个直接 import resolution 引用。记录含依赖与重复引用，不等于新定理数。原始 bytes、hash、所列行数和声明位置最终未见失配。R22 旧 Mathlib 四个带末尾撇号的声明另按实际行直接核读，避免将正则词边界误报为源码问题。R24 最后一处旧 R21 REPORT pin 已由作者刷新到本表最终字节；其余新源与 REPORT 未变。

这类 JSON/名称/字节核对不执行 proof bodies、不证明递归 imports 可 elaboration；未运行根的静态 QA 脚本或任何 guard。实际证据来自上文逐行读取、原稿/一手文献对应与有限文本修复比对。

分类保持：I 为表达/API/未执行验核，II 为确切源对象的可补推导，III 为尚缺真实全谱/全域来源。一般 trace 与 ABL/A/J/regular/gap 的实质输入不能归咎于未编译；形式模型尚未构造某对象也不自动成为原稿反例。本轮没有建立原稿反例，没有绿色或 kernel-credit 建议。

## 主清单拟稿与最终交叉范围

直接读取 `E:/timot/Documents/FilesForGPT/Myath/output/r-batch-20261102/MAIN_AFTER.md`、同目录 `MAIN_CHANGE.json` 与 R `README.md`，最后采用下列字节；先前 `f9b58c...`、`c7c24e...` 仅为已被替代的计划快照。

| 所读交付计划 | bytes | raw SHA256 |
|---|---|---|
| `../output/r-batch-20261102/MAIN_AFTER.md` | 12581 | `eda2afd45edaa3d00072bb677dd5eb3c9937c40d63ac23149ebbe3581cbeaca9` |
| `../output/r-batch-20261102/MAIN_CHANGE.json` | 7970 | `95463f4e78cba6b0d83ff440912963ec298b6c16faf77043524d64d48d539b02` |
| R `README.md` | 9965 | `f906ff4c3c1a0c45548fb65a8ef517a1bc4efc06328bc33edbc575bdddcea3fa` |
| 原实际 `../1_+_1.748_lean_proofs/main.md`，发布前 | 10093 | `1f710a830667c1934ad28541377176b7c6c566c7c968e4582ff9a22d82dd6c97` |

本次直接比较拟稿与原 main 的全部绿色行，逐条字符串相同；变更 JSON 列26项、`new_green=0`、`broad_yellow_nodes_closed=0`，前后 raw pins 与实际文件相符。这个字节检查不是数学或有限 guard。

逐条复核拟稿:89,94–98：R20 的128C 与 all-jet 权重、R21/R23 不同符号转换、R22 principal completed 子族及 R24 原 sixTail 的统一付款均被限制在实际证明范围；第97行完整 trace/全 continuous/ABL/gap/全部费用 uniform7/32、第98行 same-rho PP 继续黄色。第94行明确保留四阶28eta、不并入14eta；README 还明确不重复收取28eta。R24 的两个 zero lane 没有被登记为完成归一化付款。

README 的 R21 行及 reuse 段已承认完整 native basis、smooth profiles、normalized-cusp Fourier ODE、实/虚 K-shape 和本轮 rhoW/RW/quarter 局部转换；剩余限定为同一完整谱/scaling 的 trace 与所有 continuous/holomorphic/realnorm/经典估计。该口径正确，不再把既有 native 源码重新列缺。

拟稿:125,128 将 R07/R10 最新普通 T=1 无尾付款写成限定蓝叶；:129–130 的全 All22/同 rho density 总供应、:137 的 hdensity/hUniformPP、:144,161 的八组最终 causal suppliers、:168 的无条件 hLower/hUpper 消除仍黄色。此前上文的10实参结论保持。

已独立读取并固定的交叉独审最终 pin 如下；这些分工的 proof-body 审查由相应 reviewer 负责，本审核其终端范围与实际消费者的一致性。

| 独审 | bytes | raw SHA256 |
|---|---|---|
| `reviews/r25_review_archive_history.md` | 30732 | `39b7ea076c133eb8c0c757d2342981d2b1ff28ee83c732f581148d38ec3998ea` |
| `reviews/r26_review_reserves_density.md` | 33271 | `7bc8583d528cec4171980ad95adb3a82112a8c0182ce111e861d27d27417c18b` |
| `reviews/r27_review_bank.md` | 24343 | `6a2e5ba501aff59d3cdef976c4fbd6fd26e9e8e9da68033e189111aebfce9afc` |
| `reviews/r28_review_h430.md` | 23548 | `cbf742d41f127541098b3a216cfcefc4ffa0df5904bcf09e9c60a9f8166f450a` |
| `reviews/r29_review_gamma_pp.md` | 28281 | `ee3174823bffce61797e69f9be9282f6014b5d50c83fd7a556f1e03455cc5d65` |

R25/R26 末轮普通全尾、R04 九源边界与 R10 compose 的最终正文和 pin 均已重新实读。R25 明确原 physical gap 来自 whole secondGuard，不是额外 hGap；R04 weight/ratio/branch 推导仍未付固定 oldBranchDefect。这些纠偏已纳入本审10实参表。

**本文件至此冻结为最终作者/计划范围审稿。** 不能将它冒称 actual main 已写入、GitHub 已发布或最终 manifest 已匹配；发布后的 final-hash 回读与本 review 的冻结字节分开回传，避免把计划当结果，也避免修改已经进入 manifest 的审稿形成 hash 循环。R20–R24 的上述局部供应通过源码范围审查，完整 D19–D22、实际全谱 7/32/PP、八组下界实参与两组上界实参保持 HOLD，消除最终 hLower/hUpper 前提数为0。
