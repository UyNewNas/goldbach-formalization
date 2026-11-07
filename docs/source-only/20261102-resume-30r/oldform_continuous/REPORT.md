# R22 — oldform_continuous / D20

结论：**PARTIAL；完整 D20 HOLD。** 本轮写出实际 completed principal Eisenstein 子族的逐 dilation 移除、临界线零 Ramanujan 幂 divisor 界、Fricke/原 cusp-one Fourier 关联，并作用于 R21 的实际 `traceBeta` 有限行。一般 Maass oldclass、holomorphic 分支、全 character-pair 临界线换基及 Plancherel 范数仍未供应；完整 D20 目标前提消除数为 **0**。

`compiled=false; kernel_verified=false; formal_credit=0; finite_bodies=UNEVALUATED`。未运行 Lean/Lake/编译器、guard、CI、数值 replay 或 Git；未派子代理，未改生产、旧批次或用户 main。来源静读、字节 hash 和最小文本替换核对不算 elaboration。所有新源码、两份必要修复及本报告/登记均限于本目录。

## 原稿核对与分类

已读 R BRIEF/DISPATCH、Q03 D20、Q20 REPORT/REGISTRY、Q29 独审、P29 旧谱审查及 K full-continuous 报告；原稿锚为：

- `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:238–254`；
- 同目录 `modules/distribution-medium-completion-20261010.txt:349–424`，尤其 `:360–380`；
- 同目录 `modules/final-classical-input-correspondence-20261010.txt:23–80`；
- `../chen-imbalanced-semiprimes/proof-library/source/fixed-d-abl-packet-input-audit-20261010.txt`。

原稿的移除针对 `R(n)=sqrt(|n|)*rho_ABL(n)`，先逐 dilation 使用 ABL，再以正交基/Frobenius 支付旧类范数；不同 dilation 的 multiplier 可以不同。连续谱是全 singular-cusp 的 formal Plancherel fiber，不能把单个 Eisenstein 函数视为普通 L2 cusp vector。没有发现所核经典参数导致原稿反例；工程中缺少实例化不等于论文数学错误。

分类：旧 Fourier namespace 与已记载的 associativity rewrite 属 **I：确定 API 修复候选**；本轮 concrete principal amplitude、真实 Fourier chart 与实际有限行的接缝属 **II：可补的推导**；一般 oldclass、holomorphic/character-pair 原生谱数据与规范化范数属于 **III：仍需实质经典来源供应**。没有把 class III 改写成同义结构字段。

## 新源码与实际证明内容

文件的拟安装模块均为 `ImbalancedChen.<文件名去掉 .lean>`，完整 imports、声明行号、raw bytes/hash 见 `REGISTRY.json`。

| 新文件 | raw SHA256 |
|---|---|
| `Part3ActualPrincipalOldformRemoval.lean` | `e01268ddc23f20b9f4e9a284e60cdc368e9e66c8c93bec9cb1b1f60cf70401fa` |
| `Part3ActualPrincipalCuspOneRemoval.lean` | `ed8455fa89aee48ad661004e2774a1d5accc588fa4dda981f8405e277689e085` |
| `Part3OriginalPrincipalTraceRow.lean` | `734d59fb3b38808eb64c31843464440fbb6f22c0ded12edcbaa9c899d8550650` |

记 `a0=|a|*nu`，`A(r,s)=r^(s-1/2) * sum_(d|r) d^(1-2s)`，`s_t=1/2+it`。`A` 是旧来源已有的 `normalizedDivisorAmplitude`，不是自由输入。

1. **实际 positive dilation。** Oldform 文件 `:58,66` 从 literal degeneracy matrix 与既有 completed E* 的 SL2 不变性证明 `E*(d z,s)` 在 `d|N` 时的 Gamma0(N) 不变性。`:82` 的幅度是 `B_d(r,s)=1_(d|r)*sqrt(d)*A(r/d,s)`。`:89,106` 把它识别为实际 `E*(d(x+iy),s)` 非零 Fourier 积分中的幅度：完整系数为 `2*sqrt(y)*B_d(r,s)*K_(s-1/2)(2*pi*r*y)`。`r/d`、divisibility gate 和乘后 K argument 均保留；两个 Fourier 符号均覆盖。
2. **临界线真实 multiplier。** `:119,125,133` 直接对正整数底的 complex power 及 divisor finite sum 证明 `|A(r,s_t)| <= tau(r)`，所有实 t（含 0）一致，没有 spectral/Ramanujan 估计入参。`:154` 由既有 divisor multiplicativity 推出 `(a0,d)=(a0,n)=1` 时 `B_d(a0*n,s)=A(a0,s)*B_d(n,s)`，含 gate 为零的分支。`:177,190,211` 消费 Q20 已证的原始行互素性，得到实际 dilation 移除、单幅平方 `tau(a0)^2` 界与物理 Fourier 等式；没有重证 K=1。
3. **实际 completed level/Fricke 表达式。** `:236,241,266,293` 使用原 `oldformTerms(canonicalPrimeList N)`、全部互补 dilation `N/d`、原有限系数和 `oldformNormalization`。先证明每项的实际幅度，再在这一个显式 principal 表达式中抽出已经证明相同的 `A(a0,s)`。该特殊相同性没有被推广到一般 oldclass。
4. **原 cusp-one chart。** CuspOne 文件 `:43` 供应具体 critical completed level 函数的真实 Gamma0 不变性。`:51,56` 定义 genuine normalized-Haar Fourier coefficients；`:66,76,103,122` 依次使用既有 `sigmaOne=T*W_N*T_(1/N)`、Haar/单位区间积分关联和实际 Fricke Fourier 公式。对于 `epsilon=+/-1`，原 cusp-one 幅度为 `e(epsilon*r/N)*B_N^Fricke(r,s_t)`。`:153,168` 在原始行证明先取消 `e(-epsilon*a0*n/N)`，再移除 a0，残余相位严格为 `e(-epsilon*n/N)`。
5. **实际 R21 有限行。** TraceRow 文件 `:36–69` 使用 `traceNegative D key negativeM`，符号含原 a、y 与 Poisson sign；没有用 y-sign 替代整块符号。`:74` 将真实 `traceIndex` 接到上述 actual cusp-one Fourier integral，仍保留径向因子 `K_it(2*pi*a0*n*y)`。`:95,105` 的两行只使用原 `nCarrier`、R21 `traceBeta`/Q `modulatedBeta` 和这个已实现的 principal 幅度；`:116` 证明整行等式 `principalTraceRow=A(a0,s_t)*principalReducedTraceRow`，`:135` 给其平方范数 `<=tau(a0)^2` 乘残余行平方范数。没有为 beta 新添高度、m 或 c 依赖，也没有新建任意 rho/localL2/cumulative 字段。

上述幅度是 **completed K amplitude**。代码从物理 Fourier 积分证明其来源，未除掉可能零的 K 值，未在临界线除 completion/zeta/Gamma 因子。特别在 t=0 保留 completed 值，不将它偷换为未完成的 ordinary Eisenstein。物理非零频数定理保留 `a != 0`、实际 carrier 与 `y>0` 等必要来源条件。

## 复用、最小修复与安装边界

Q20 `Part3OriginalRowOldformArithmetic` 原 SHA `fbda3e52f45e76e76330ffad9e01e054297c047af8b9ba749e23263288c76e5b`，实际 n/level 互素性与 K=1 原样复用。P 的原 `Row/nCarrier/blockBeta`、Q 的共同 Fourier 模式、R21 的实际复合 trace sign 与 `traceBeta` 均未重定义成替代来源。

hidden `20261026b-FrickeNonzero/Part3ActualFrickeNonzeroFourier.lean` 已有 genuine critical Fricke nonzero integral，本轮精确复用。其依赖 `Part3CompletedIntegerNonzeroFourier.lean` 的 frozen raw SHA 为 `7d0e55831502f720010225424a70ea821de9c4539ae882b46da6e451f5e7354c`；`20261026b-code-only/batch34/dots-api-delivery-holds.json` 已记载 broad `simp_rw [add_mul, mul_assoc]` 的错误作用范围。本目录修复副本只把该 proof step 改为 `simp_rw [add_mul, mul_assoc (2 * (Real.sqrt y : ℂ))]`，另加普通头注释，SHA `f7ce04999654c36596a8ec68dd0b73d6c34b77c0f82c1a787ab973152d5b3724`。这是旧数学的修复候选，未授新证明信用，未抹除历史 HOLD。

mathlib pin 为 `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。该版 `AddCircle.lean` 的 `fourier`、`fourierCoeff`、`fourierCoeff_eq_intervalIntegral` 是根 namespace 声明；`AddCircle.haarAddCircle` 才保留在 AddCircle。本轮新源使用 `_root_.fourier*`。[锁定原始 Fourier 源](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Analysis/Fourier/AddCircle.lean)。

同一错误在生产 `Part3ActualFrickeCuspPhase.lean` 的实际接缝中存在，故本目录 `repairs/Part3ActualFrickeCuspPhase.lean` 只执行逐字前缀替换 `AddCircle.fourier` → `_root_.fourier` 并加普通头注释；修复 SHA `749882d348253efdfb33387299a30653f0484b0810eeac84a761c2433609fddf`。其基础模块使用 R23 已有修复，**不另复制、不修改 R23 或生产源**：

| 拟安装原模块 | 精确选择的 R23 修复 | raw SHA256 |
|---|---|---|
| `Part3CuspTranslationFourierPhase` | `actual_spectral_energy/repairs/Part3CuspTranslationFourierPhase.lean` | `5aa2566f75a7ff66b58ee848f9ecad3384a7498f85af6f4970f32d9de1b85756` |
| `Part3ActualCuspFourierSection` | `actual_spectral_energy/repairs/Part3ActualCuspFourierSection.lean` | `7cc15af0858e3df58f09c0b94463ed2475629119a291c1045a37067036ebe36a` |

以上拟安装名保持原 imports。生产树没有被安装/覆盖；未声称整个递归 import closure 可 elaboration。登记区分 exact reuse、minimal repair 和 new source body，包含原/修复字节映射。

## 全范围检索后可复用的真实谱来源

检索覆盖 `ImbalancedChen`、全部 `docs/source-only` 和 `rg -uu` 可见的 `.lake/proof-continuation/source-reviews/drafts`；publisher/frozen 重复副本按原来源去重。以下成果存在，不能再笼统记成“缺实际谱基/只在 Re(s)>1 有任何 Eisenstein”：

| 已有来源 | 已提供的内容 | 不能据此推出的 D20 内容 |
|---|---|---|
| hidden `20261026b-GammaCompactness/Part3ActualFullCuspEigenbasis.lean:94` | **整个** actual full-cusp Hilbert 空间的 orthonormal eigenbasis；无 hBasis/hComplete 字段。 | 规范化 cusp Fourier/oldclass identity、Kim–Sarnak 或完整 continuous spectrum。其 inherited be3646/0f1f API HOLD 保留。 |
| hidden `20261026b-AffineRellich/Part3ActualFullCuspLambdaSquaredDomain.lean:45,63,119` | native graph/domain 的 lambda coefficient 描述与实际 operator Parseval。 | Kuznetsov Fourier-product Plancherel measure；operator coefficient 不是 automorphic Fourier coefficient。 |
| hidden `20261026b-ZeroModeHardy/phase16-spectral-kernel/Part3ActualCuspSmoothEigenprofileFamily.lean` | actual basis 的 smooth Gamma profiles、a.e. realization、PDE、carrier mass one 与统一 compact jets。 | 完整规范化 trace；不得再把 smooth realization 本身列为全然未写。历史 eigen-regularity/API HOLD 保留。 |
| hidden `20261027-Hecke-Joint/Part3ActualCuspFiniteJointHeckeDiagonalization.lean` | actual native graph eigenspace 中 commuting good-prime Hecke 的 joint basis。 | 跨旧类的实际规范化 dilation、变动 multiplier 和所需平方范数支付。 |
| hidden `20261027-Hecke-Fourier/Part3ActualNormalizedHeckeFourier.lean` | real K-order quotient Fourier/Hecke 关联。 | `quotientRho` 是 K 振幅，不能仅按同名 `quotientR` 当作 ABL 的 Whittaker-normalized R。 |
| hidden `20261026b-ImaginaryKLimitPoint/Part3ActualImaginaryMaassFourierK.lean:35` | actual periodic C2 PDE 与物理 strip L2 导出 signed imaginary-K 唯一幅度，含 tau=0。 | 仍须绑定上述 native basis 与规范化 Fourier/trace；其 d4d0a/c51501 installation HOLD 没有被本轮取消。 |
| R21 `actual_kuznetsov/Part3ActualMaassWhittakerNormalization.lean` | actual quotient/cusp-local K 振幅的 `rho_W=rho_K/(2*sqrt(abs(n)))`、`R_W=rho_K/2` 与局部产品 `1/4`；本轮已读，作为现存供应登记。 | 不直接将其中 cuspidal strip-L2 定理用于非 L2 的 incoming Eisenstein；普通/完成因子与全 cusp formal norm 仍需接入。 |
| production completed level Eisenstein、`Part3AllLevelContinuedMaass`、critical scattering | 本轮真正使用的 completed principal 临界线家族、native continuation 和实际 automorphy。 | 所有 character-pair fiber 与全 cusp scattering matrix；full-level scalar scattering 不能代替后者。 |
| production `Part3CharacterEisensteinSeries` | 实际 character-weighted primitive series 的初始域构造。 | 完整 critical-line continuation/full-cusp Plancherel。hidden `Part3CharacterUntwistedSquareSpanSeparation` 还证明初始域的 nonprincipal 分量不在 untwisted 三 dilation span 中。该分离定理没有被误作临界线结论。 |
| K `Part3OriginalContinuousPacketExhaustion:231–312` | supplied rho 下正确共轭、all-cusp measure、外置 `1/(4*pi)` 与 `dt/cosh(pi*t)` 的 consumer。 | actual rho/measurability/localL2/cumulative 的供应。新 principal 行不填充这些全谱入参。 |

另有 scalar `Part3Gamma0ActualSigmaPlancherel`，其实际 spectral theorem 不能充当上述 complete cusp Fourier trace；Q/R02 指出的 `Part3ActualFixedSliceGlobalZABLNorm` 仍只是实际算术 coefficient 重索引/计数范数，未返回 ABL/Kuznetsov。检索结论只限这些受查来源，不声称没有任何外部形式化。

## 经典输入的版本及适用范围

[ABL arXiv:2005.13915v1](https://arxiv.org/pdf/2005.13915v1)，§3.2、Lemmas 3.1–3.2、(3.3)–(3.9)：原行特化为 `(q,r,s,Q)=(1,z,1,z)`。K=1 之外仍须逐 dilation 的真实 Hecke/Fourier 关系、norm-one dilation 与 orthonormal oldclass 的范数比较；Maass 的 amplitude exponent `7/64` 对应 squared `7/32`。holomorphic 使用 Petersson normalization 及 Deligne，continuous 使用真实 character-pair basis 的零实部界。本文不安装上述文献陈述为 Lean axiom。

[Young arXiv:1710.03624v2](https://arxiv.org/pdf/1710.03624v2)，§8、Theorem 8.1、Proposition 8.2：formal Eisenstein inner product 中 cusp series 的范数为 `4*pi`，basis-independent 表达式保留真实形式范数分母；任意 level 的此处结果不应误限为后文 squarefree newform 定理。§8 开头的维数/独立性明确可能例外于 `t=0`。**推论边界：**将来 continuous Lebesgue integral 的换基只需 a.e. t，可单列零测 singleton；这不允许删除 D21 的中心 test-transform 极限。当前既未形式证明该全谱 a.e. 换基，也未以 completed principal 中心值替代它。

Young v2 PDF 实际读取的 raw bytes 为 480212、SHA `8fbf79dfa0d4cdf999786e6443a172ba998790a80c8cc9b266b6cd9aaf9b35a8`（内存读取，未另存 PDF）。ABL 使用已有精确 v1 本地副本，其 hash/path 在登记。Mathlib 的 coprime/divisibility 与 critical cpow norm API 亦按上述 pin 或原已归档同 pin 源核读，未猜 namespace。

## 真正消除的局部前提与仍需完成的义务

本轮无任意 rho、未给目标同义的 equality/estimate 字段，也没有新 `hTrace/hOldform/hLocalL2/hCum`。具体 principal 子族中不再需要另假设：positive dilation 的实际 automorphy、selected amplitude→物理 Fourier、coprime n-removal、临界线 multiplier divisor 界、原 cusp-one signed phase association、或 R21 实际 finite row 的此单通道 norm inequality。已有 Q20 coprimes/K=1、原 beta 来源与旧 actual nonzero Fourier 供应没有重复记信用。

剩余义务必须原样保留：

- 同一 D19 realization 中的 actual oldclass labels、每个合法 dilation 的 normalized R 系数转换；一般 multiplier 可以随 dilation 变，旧类 Gram/Frobenius 成本不可用本 principal 的共同标量消去。
- Maass 的实际 Ramanujan/Kim–Sarnak amplitude 供应及 `a0^(7/32)` 平方费用；holomorphic 真实 weight-k/Petersson basis 与 theta=0，不能把 weight-k 当作本文件的 weight-zero scalar 函数。
- 全 character-pair 临界线 series、ordinary/completed normalization、all singular cusp Fourier matrix、formal norm denominators、basis-independent full quadratic form；保留共轭、`R=sqrt(|n|)*rho`、外置 `1/(4*pi)` 和 `dt/cosh(pi*t)`。
- 本轮的 actual finite principal channel 平方界不是全 cusp 求和/积分，不是 orthonormal oldform fiber 的 bound，更不是原双 Fourier-product 谱能量。径向 Fourier equality 没有将 K 从含 n 的有限和中抽走，也没有把 completion 因子默认作 1。
- D21 实际 A/J/regular/gap 以及 D22 原六片全源/费用、共同 pre-N 阈值继续由相应供应槽处理；不能由本报告关闭 Eq.(24)/(25)、P3.5.uniform_spectral 或任何父目标。

独立审查由 R30 记录；本报告给的是 source-level 候选证明与精确边界，不替代独审或 kernel 接受。
