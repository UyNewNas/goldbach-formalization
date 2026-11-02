# R21 / D19 — actual signed trace input

**PARTIAL：补成原实际全模数源到 normalized Kuznetsov 算术侧的精确转换，并修正实际 K 振幅到 Drappeau/ABL Fourier 归一化的来源转换；完整 automorphic trace 与全谱 Fourier products 仍 HOLD。** 新增三份有证明体的 Lean 源码文件。完整原生 cusp Hilbert 基、光滑本征函数族与实/虚阶 K-shape 已有源码，直接复用；本轮不将这些旧成果重新列为缺口。没有引入 `hTrace`、任意 raw-rho、空谱或目标同义结构。因此本轮消除的真实 trace / spectral-energy 前提数仍为 **0**。

`compiled=false; kernel_verified=false; formal_credit=0; finite_guards=UNEVALUATED`。本目录内只做源码写入、静态读取/检索、版本固定和 raw hash。未运行 Lean/Lake/编译器、guard、CI、数值重放、Git 或子代；未修改生产、旧批次或用户主稿。R21 恢复后确认本目录此前没有半写/空文件。

## 原稿与复用判定

核对 Body `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:238–254`，Medium `paper/source/modules/distribution-medium-completion-20261010.txt:349–380`，Classical `paper/source/modules/final-classical-input-correspondence-20261010.txt:29–65`。它们要求实际 level `z`、trivial character、cusps infinity/1、固定 scaling、真实 Fourier 产品和完整连续谱；原 ABL phase 在 n-removal 后为 `e(-n/z)`，相反符号须作对应 signed identity。

先读 R BRIEF、D19、Q20 REPORT/REGISTRY、Q29、J regular REPORT/源码、K continuous 源码和 R02。检索覆盖生产 `ImbalancedChen`、全部 `docs/source-only`、以及隐藏 `.lake/proof-continuation/source-reviews/drafts`；同名 frozen/publisher 快照不重复计成果。末轮补读使复用边界进一步收窄：隐藏 `20261026b-GammaCompactness/Part3ActualFullCuspEigenbasis:94` 已构造整个 `ActualFullCuspL2` 的 `actualCuspHilbertBasis`，`Part3ActualCuspEigenbasisNativeLabels:79` 把同一基连接到原生 Maass graph；`20261026b-AffineRellich/Part3ActualFullCuspLambdaSquaredDomain:45,84,119` 已给原生 graph/domain 与加权系数 Parseval。`20261027-Hecke-Joint/Part3ActualCuspFiniteJointHeckeDiagonalization` 另给每个实际 Laplace eigenspace 的 good-prime 联合正交基。不能据后者的有限 fiber 形式否认前者的全 cusp 完备性。

`20261026b-ZeroModeHardy/phase16-spectral-kernel/Part3ActualCuspSmoothEigenprofileFamily:42,50,66,106` 已给同一基的实际光滑 Γ0 不变本征函数、原 carrier L2 归一化及 uniform compact jets；`20261027-KernelAction/Part3ActualCuspSmoothFiniteKernelDescent:21,39,110` 将它们降到真实 quotient，保留原 Borel 有限核作用。`20261026b-CuspWeakModes/Part3ActualEigenOriginalFourierClassicalModes:141` 已对每个 normalized cusp 给原 Fourier 的 C²/ODE 及同一 conull 高度集合。上述旧链明确继承 be3646/0f1f、eigen-regularity / namespace 等 API HOLD，不能算本轮解除，也不能因此写成源码不存在。

生产 `Part3ActualRealMaassFourierK:77`、`Part3QuotientRealKFourierCoefficient:63` 已供应实际 quotient 的实阶 K 系数（含阈值）；隐藏 `20261026b-ImaginaryKLimitPoint/Part3ActualImaginaryMaassFourierK:35`、`Part3CuspLocalImaginaryKShape:36` 已从实际 PDE/periodicity/strip L2 证明所有 signed 非零频率的唯一虚阶 K 振幅（含 tau=0）。后两者继承 `Part3ImaginaryRadialTailDerivativeL2` 所需 `d4d0a1047d6dd5ad881c1c8fac10a5b0d8ecb6bfa278f912ebd4d56c0e3ffc15` 对旧 target `c51501c5ae949018d44907601ddbb27bd3fdad4c33e45e4f5e4c2ee9086ae09c` 的安装 HOLD。本轮直接导入候选源，不改旧 target，不规避该 HOLD。

已经供应的内容直接复用：

- Q19 两固定 Z、原六片 Fourier/Poisson 全族等式、实际 beta 和三种 remainder；Q20 原始行 coprime / 每个 dilation K=1 / A、J 支持端点资格。这些不再列作缺口。
- 生产 `Part3ActualReciprocalSquarePoisson.kloosterman_negative_linear:388` 已证明所有余数上的符号反演，含 `c=1`；本轮只补它在 Q actual atom 的必要调用。
- J `Part3OriginalNonzeroCuspOneSource:160,191,273,298` 已给真实 Gamma0 双陪集完整枚举和 `S(m*zbar,n;c)=e(-n/z)*cuspOneMatrixSum(z,c,m,n)`。实际 scaling 为 `sigma_infinity=Id`、`sigma_1=[[sqrt(z),0],[sqrt(z),1/sqrt(z)]]`，正模数为 `sqrt(z)*c`。
- R20 `full_modulus_test_support` 已把共同 c 窗在未分离前扩大，再按 mode 精确得到全正模数；其 `fullModulusRow`、`spectralTest_modulus_support`、`original_trace_test_admissible` 被新文件实际调用。这里没有再假定有限 c 与全 c 的 mode 逐项相等。

第一类问题是旧 namespace/import/API HOLD 与尚未执行的 elaboration。第二类可补省略是 Q/R20 原 signed atom 到经典正 m trace 算术侧的符号、相位和外因子转换，以及旧 K 振幅与文献 Whittaker 振幅的不同归一化；本轮补了这些局部来源转换。第三类仍是将已有同一原生基、固定 cusp scaling 与完整 holomorphic/全 singular-cusp continuous 分支实际组装为 normalized trace。它超过一个名称/API 修补。经典论文中有相应定理，所以此形式缺口本身不是原稿反例。

## 三份新证明

`Part3OriginalSignedTraceInput.lean`，拟安装 `ImbalancedChen.Part3OriginalSignedTraceInput`：

1. `traceIndex:43` 定义实际第二索引 `h = (-1)^negativeM * a * decode(k,z,n).y`。`traceNegative:49` 在选择 `z,n,c,p` 前固定 residue/y/Poisson 三者的复合符号。`traceIndex_eq_signedY:53` 证明 `h = signedY(traceNegative, |a|*nu*n)`；`traceIndex_natAbs_pos:76` 从实际 `nCarrier` 和 `a≠0` 得非零频率资格。
2. `sourceKloosterman_eq_positive_m:86` 把 Q 的 `S(signedY(negativeM,p)*zbar,a*y;c)` 精确写为 `S(p*zbar,h;c)`。负 m 的 Fourier `actualCoeff` 参数保持原值，既没有将 beta 共轭，也没有改共同 additive phase。
3. `sourceKloosterman_eq_positive_cuspOne:99` 复用 J 得逆相位 `e(-h/z)`。因此直接调用正 m 经典 trace 时，不能仅使用 primary y-sign；负 m 改变了第二 cusp 的符号及其逆相位。
4. `sourceArgument_eq_traceArgument:119` 给字面 `4*pi*sqrt(p*|h|)/(sqrt(z)*c)`，`chartScalar_eq_trace_modulus:133` 给外因子 `M*sqrt(Z)` 与内分母 `sqrt(z)*c`。没有连续 c 积分或 Jacobian。
5. `traceBeta:142` 是 Q 的实际 `modulatedBeta * e(-h/z)`，对未来 `p,c,height` 无依赖；`norm_traceBeta:147` 保持原 `blockBeta` 范数。`original_chartModeAtom_eq_normalized_cuspOne:156` 将这些转换实际应用到整个 Q atom，而非对一个新 chosen kernel 作自洽定义。

`Part3OriginalFullModulusCuspInput.lean`，拟安装 `ImbalancedChen.Part3OriginalFullModulusCuspInput`：

- `bareCuspTerm:36` 保留真实正 c/coprime gate、J matrix-defined cusp sum、上述实际 signed index 和 R20 原测试函数。
- `bareCuspTerm_hasSum:49`、`bareCuspTerm_summable:70` 对裸 trace 算术级数证明共同有限支撑；利用 R20 的非零 test 必有 `c<32N≤128C`。这一步不从 `beta*series` 的收敛除以可能为零的 beta，故全零原 coefficient 也不会伪造 bare convergence。
- `fullModulusRow_eq_normalized_cusp_sum:80`、`fullChartMode_eq_normalized_cusp_sums:102` 是 R20 实际行/整个 z,n,p 族的等式，准确形式为

  `M*sqrt(Z) * commonWeight(p) * traceBeta(z,n) * sum_c [ S_infinity,1(p,h;c*sqrt(z))/(c*sqrt(z)) * spectralTest(4*pi*sqrt(p*|h|)/(c*sqrt(z))) ]`。

没有将原子 `actualCoeff` 合并成另一个 phase；没有丢 `a`、`nu`、符号、重数、`c=1` 或原 n、p 端点；没有重付 Q 的零项和尾项。上述结论在 R20 的全 c representation 上成立；其与原六片的 Fourier 和关联仍复用 R20，不宣称等于 Q 原 finite-c 的每一个 mode。

`Part3ActualMaassWhittakerNormalization.lean`，拟安装 `ImbalancedChen.Part3ActualMaassWhittakerNormalization`：

- `realQuotientWhittakerRho:63`、`realQuotientWhittakerR:68` 从旧实际 quotient Fourier 振幅定义正确转换；`realQuotientWhittakerR_eq_half_native:72`、`realQuotientWhittakerR_eq_old_quotientR:79` 证明 `rho_W=rho_K/(2*sqrt(|n|))`、`R_W=rho_K/2=old quotientR/(2*sqrt(|n|))`，保留 `n≠0`。
- `actual_quotient_fourier_eq_whittaker_normalization_real:97`、`actual_quotient_fourier_eq_normalizedR_real:106` 实际调用旧 quotient 的物理 K 定理，得到同一个 Fourier 积分等于 `rho_W*2*sqrt(|n|*y)*K`，亦等于 `2*R_W*sqrt(y)*K`；不是假定 Fourier shape 后包装。
- `realQuotientWhittakerR_product:116` 给实际系数乘积 `conj(R_W(U,m))*R_W(V,n)=conj(rho_K(U,m))*rho_K(V,n)/4`。它只断言原函数局部振幅乘积，没有制造谱求和。
- `actual_cusp_local_unique_whittaker_amplitude:130`、`actual_cusp_local_unique_normalizedR:165` 从原函数 cusp-local PDE、periodicity、raw strip L2 和旧唯一 imaginary-K 定理给正确振幅的 `∃!`，包括 tau=0、signed n 和严格 `y>Y`。没有除以可能为零的 imaginary K；旧安装 HOLD 原样继承。

代码故意显示物理 `2*sqrt(|n|*y)*complexOrderK` 表达式，没有新定义一个叫 W 的函数来宣称完成谱识别。标准 Whittaker 身份及与同一基/固定 scaling 的完整连接仍须按下节精确口径使用。

## 固定文献下的谱端：精确目标及适用转换

本次在线核读并在本目录保存原始字节：[Drappeau arXiv:1504.05549v4](https://arxiv.org/pdf/1504.05549v4)，Lemma 4.3、§4.1.2、(4.9)–(4.19)；[ABL arXiv:2005.13915v1](https://arxiv.org/pdf/2005.13915v1)，§3.2、(3.2)–(3.9)；[Pascadi arXiv:2404.04239v3](https://arxiv.org/html/2404.04239v3)，§3.2–3.4、Proposition E；[NIST DLMF 13.18.9](https://dlmf.nist.gov/13.18.E9)，保存页面自报 Version 1.2.8、release 2026-09-15。下载文件 hash 见下表与 REGISTRY。这里只固定数学文献的版本/原字节，不把网页当作已安装 Lean theorem。

ABL §3.2 明确沿用 Drappeau 的 notation/normalization。Drappeau 使用标准 `W_(0,nu)(4*pi*|n|*y)`；DLMF 13.18.9 给 `W_(0,nu)(2x)=sqrt(2x/pi)*K_nu(x)`。故对**同一函数、同一 scaling**，由此推得 `W_(0,nu)(4*pi*|n|*y)=2*sqrt(|n|*y)*K_nu(2*pi*|n|*y)`。旧 `quotientRho` 是后者 `sqrt(y)*K` 的振幅，因此旧 header 中的 “ABL normalization” 不能直接采用；新源码已补上所差的 `2` 和 `sqrt(|n|)`。这不是原稿反例，也没有修改旧定义。

为了避免两文献 Fourier/Whittaker/transform 常数混用，下面完整采用 Drappeau 的 weight-zero convention。令 `rho` 为其 (4.7) 及随后的实际 Fourier 展开系数，并令 `R_f,a(q)=sqrt(|q|)*rho_f,a(q)`。令 `phi=spectralTest ell (chartY0 ...)`。R20 已提供紧支撑、光滑、正支撑区间；本轮提供 `p>0` 的实际 completed carrier、`|h|>0`、全部 cusp 模数及正确相位，所以纸面上的 Lemma 4.5 可在同一源索引逐项特化。

令 `sigma=+1` 或 `-1` 是本轮固定的复合符号。其 Maass 变换保持 (4.10)/(4.11) 的原归一化：

\[
H_\phi^+(t)=\frac{2\pi i}{\sinh(\pi t)}
\int_0^\infty (J_{2it}(q)-J_{-2it}(q))\phi(q)\,\frac{dq}{q},
\qquad
H_\phi^-(t)=8\cosh(\pi t)
\int_0^\infty K_{2it}(q)\phi(q)\,\frac{dq}{q}.
\]

在 `t=0` 使用该变换的可去奇点延拓，不能将未定义商设为零。正号 holomorphic 变换为 `dot(phi)(k)=4*i^k*integral J_(k-1)(q)*phi(q)dq/q`，其高度仍为 `k-1`。以 `R` 写出的单个裸 arithmetic trace 的谱端是

\[
\sum_{f\in\mathcal B_0(z)}
 \frac{H_\phi^\sigma(t_f)}{\cosh(\pi t_f)}
 \overline{R_{f,\infty}(p)}R_{f,1}(h)
 +\frac1{4\pi}\sum_{\mathfrak c\ \mathrm{singular}}
 \int_{\mathbb R}\frac{H_\phi^\sigma(t)}{\cosh(\pi t)}
 \overline{R_{\mathfrak c,\infty}(p,t)}R_{\mathfrak c,1}(h,t)\,dt,
\]

并在 `sigma=+1` 时加入

\[
\sum_{k\in 2\mathbb N_{>0}}\dot\phi(k)\Gamma(k)
 \sum_{f\in\mathcal B_k(z)}
 \overline{R_{f,\infty}(p)}R_{f,1}(h).
\]

Maass 和包含 regular 与 exceptional；负号没有 holomorphic 项；连续项是所有 singular cusps 的 fiber 积分，`1/(4*pi)` 外置且 `dt/cosh(pi*t)` 不变。这里写的是经典文献的实际谱对象应满足的特化公式，**新 Lean 文件并未证明此公式，也未声明这些谱对象已经在工程中构造**。

在这个真实谱端，设 `w_p` 为原共同 m weight、`b_n=traceBeta(z,n)`。有限源求和后的两个线性泛函必须是

\[
M_f=\sum_p\overline{w_p}R_{f,\infty}(p),\qquad
N_f=\sum_n b_n R_{f,1}(h_n),
\]

所以乘积为 `conj(M_f)*N_f`。这是共轭位置的代数后果，原 beta 不被共轭；共同 phase 进入 `M_f` 时取共轭，trace 外再取共轭而恢复原相位。R22 若用 ABL，须在这一实际 `sigma` 下把 `e(-sigma*|a|*nu*n/z)` 变成相应 `e(-sigma*n/z)`，不能只沿用 y-sign。R23 的本轮 native signed Haar-coefficient conversion 可复用，但它也不构成这个完整谱 realization。

## 真正剩余及前提影响

已有原生完整 cuspidal basis、native graph/Parseval、smooth profiles、normalized-cusp Fourier ODE 和实/虚阶 K-shape 均作为现成来源保留。仍须把**同一基**的这些实际 Fourier 积分、原 infinity/1 scaling 与本轮正确的振幅归一化组装到经典谱对象；并供应所有 holomorphic 分支及所有 singular-cusp 临界线 Eisenstein realization/Plancherel，继而证明这些对象的 normalized trace，再接本轮原 arithmetic caller。新局部振幅乘积、真实 scalar Laplace measure 或有限 smooth kernel 都不能直接推出这一全谱等式。旧 transitive API/installation HOLD 另列，不拿未编译解释该实质 trace 缺口。

K `Part3OriginalContinuousPacketExhaustion` 的 normalizedR、共轭、all-cusp measure 和 exhaustion 仍可复用，但其 raw-rho/cumulative 前提不是已经构造的实际临界线数据。R22 的 full oldclass/continuous norm、R23 的 actual A/J/regular/gap、R24 的真实全源能量及完整费用分别保留。这里没有重新定义旧 `completedEnergy`，也没有把 Fourier 产品放进随后被 `withPositiveKernel` 覆盖的 kernel。

实际已消去的是：Q actual signed Kloosterman 到固定正 m cusp side 的来源转换、复合符号选择、`4*pi` argument/外因子对应、R20 full-modulus caller 与裸级数收敛，以及实际 K 振幅到正确 `rho_W/R_W` 的局部来源转换。**完整 D19、P3.5.uniform_spectral、Eq. (24)/(25)、same-rho PP 和最终 hLower/hUpper 均不得据此关闭。** 无条件 full trace 证明尚未交付，是本槽未完成的实质义务，不归咎于运行时、未编译或假想的原稿反例。

## 冻结来源与静态验证

| 文件 | raw SHA256 |
|---|---|
| `Part3OriginalSignedTraceInput.lean` | `2ba47c389ce2ffab05eb090c29877a678cde69b23b180e8875840905fe588341` |
| `Part3OriginalFullModulusCuspInput.lean` | `8c1b404b0b594d792cf21f9a861b3cdc19322fa9077e97451271cf2021caf877` |
| `Part3ActualMaassWhittakerNormalization.lean` | `ec750f6b9648087254185628163e3bd3e147fdb06424383ae6d236de1774cfba` |
| `references/drappeau-1504.05549v4.pdf` | `7d5b2f3c2dac35f09004f005bfc6de9696979cdf05c4330b25c346a81f4d924f` |
| `references/pascadi-2404.04239v3.html` | `078d4ddcb8a63970a491262e11773dbd19674654423210ada14ab960eb1ac3e0` |
| `references/abl-2005.13915v1.pdf` | `a7a0a12d7c53f69bf267384c1d72a9078f5bdf0c4f3e5d451743f5964af1a357` |
| `references/dlmf-13.18.html` | `1dcbf91e61fc49cdf9984ccb284131a016a971d69ad40cb871b205ccba218a08` |

REGISTRY 记录三份新源码全部声明、直接 import 与源路径对应、已用旧源/原稿/审查/本轮上游的实读 hash。缺少安装路径只记 staging，不能冒称源不存在。R30 已独读三份新源码与关键旧源，限定本轮来源转换未发现明确数学阻断；仍保留完整 trace/full spectrum HOLD。静态检查与独审均不是 elaboration 或 kernel verification。
