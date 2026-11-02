# Q29 独立复核：automorphic_dictionary / actual_spectral_energy

结论：**限定 PASS；完整目标 HOLD。** Q19 的两个固定 Z 全族 Fourier/Poisson 精确组装、Q20 的实际 primary 行 ABL 算术 K=1 与经典支持资格，均通过本次独立来源级静审。没有发现足以阻断这些局部结论的数学、对象保持或所查 API 问题。实际 normalized Kuznetsov、oldform/continuous Fourier realization、A/J/regular/gap 与 Eq. (24)/(25) 谱能量返回仍 **HOLD**；本轮消除的真实谱能量前提数为 **0**。

`compiled=false; kernel_verified=false; formal_credit=0; finite_guards=UNEVALUATED`。未运行 Lean/lake/编译器、CI、proof guard、数值重放或 Git；未改作者文件；未启动子代。PASS 不表示 elaboration、kernel acceptance、递归 import closure 已验证，也不把作者报告代替独立阅读。

仓库根为 `E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation`。下文路径相对该根；Q=`docs/source-only/20261102-resume-30q`，P/O/M/K/J 分别为对应 `20261102-resume-30p/o/m/k/j`。主原稿简称 Body，详细完成稿简称 Medium，经典对应表简称 Classical，确切路径和 raw SHA256 见末尾。复核先读 Q/BRIEF、P/t29 与 Q03 原稿证据，并针对 Body:201–254、Medium:299–424,463–483、Classical:23–137 和新增四份源码逐项检查；续接时未重证整个 P 链。

## PASS：本轮实际补成的局部叶

| 源码与行 | 独立核对的内容 | 限定结论 |
|---|---|---|
| Q19 `Part3OriginalTwoZSourceAssembly.lean:39–87` | `fixedZ` 在 z/n/c/p/ell 之前固定为 S² 或 2S²；实际 level carrier 在 2S² 用 `<`/`≤` 精确分组，边界只属上组。使用 P 的 normalized carrier，不添加非空假设。 | **PASS**：Q03:97–110 的两个固定 Z 分组缺口得到实际来源供应。 |
| 同文件 `:89–129,131–191` | q 保留 `4*pi*sqrt(abs(a)*p*(nu*n))/(c*sqrt(z))`，外因子为 `M*sqrt(Z)/(c*sqrt(z))`；直接调用 P 的逐点 scalar theorem，并在原 z/n/c/p 全有限族上求和。原 `(c,z)=1`、有符号 Kloosterman 两参数、离散 c 与原 beta 重数均保持。 | **PASS**：整族 normalized-F 等式已证明；没有把离散 c 求和换成 q 积分或引入任意 kernel。 |
| Q19 `Part3OriginalTwoZFourierAssembly.lean:46–83,105–181` | 从实际 `actual_global_separation_hasSum` 导出 O 的共同 weight `e(ell₁*p/(64*V))`，并有限求和。每个固定 j/M/N/符号块的 `actualCoeff` 对该块全部 z/n/c/p 相同。`modulatedBeta` 仅含原 beta 与 ell₂/ell₃ 相位，范数不变，不含未来 m/c/height。 | **PASS**：不是另定义一个未接入来源的共同 phase；保留原负 m 在 Kloosterman 参数和 sigma 中的作用。 |
| 同文件 `:191–203,207–250,252–310` | 两 chart、全 computed primary/y-sign keys、全部共同 dyadic m 块及两 m 符号，用有限 HasSum 汇合到同一 ell 的 tsum；六片仍保留各自真实 `actualCoeff(rho,sigma,ell)`。`sixRemainder` 独立定义为全 y=0 源、非零 y 的 m=0 与原 outside-window tail，最终等于实际 `smoothSix`。 | **PASS**：同一 J、同一 earlier r，r 未被认作 Poisson m。没有丢零项、重复算 y=0/m=0，或以“目标减主项”定义空泛误差。 |
| Q20 `Part3OriginalRowOldformArithmetic.lean:30–65` | 从实际 primaryBlock 成员的 computed key 恢复 nu 的素因子支持，调用已有 `rhoPrimaryNu_prime_support`；由真实 n/level carrier 推出 `(n,natAbs(a)*nu)=1`、`(natAbs(a)*nu,z)=1`。 | **PASS**：消除真实 ABL 行的算术资格，不是给任意 CoprimePacket 添目标字段，也没有把 c 当 level。 |
| 同文件 `:69–99` | 字面定义 `K=supportedPart(z/gcd(v*q_f,z),natAbs(a)*nu)`，证明 cofactor 整除 z，再由互素性推出 K=1。对全部自然 q_f,v 的较强整数断言当然涵盖合法 oldform labels；未声称非法标签有谱态。 | **PASS**：实际 s_ABL=1 的 K=1 局部叶；尚无 Hecke/oldclass 范数定理。 |
| Q20 `Part3OriginalClassicalSpectralSupports.lean:77–108` | 原始非零 signed row coefficient 还原到既有 dyadicBeta 后，调用 `nonempty_endpoint_bounds` 得 L=U/nu≥1/2；由真实 Z≤z 得 `1+Z/L≤2*max(1,z/L)`。全零系数无须强造非空谱。 | **PASS**：真实长度端点与固定 level A 参数比较。 |
| 同文件 `:34–72,111–178` | O 原块为 `[V,min(2V,J+1))`，确实含 m=V。以 M_class=V−1/2 得原块⊂(M_class,2M_class]，M_class≥1/2；原 phase 分母仍为 V。闭 level plateau [Z,2Z] 覆盖于 (Z/2,Z]∪(Z,2Z]，不丢 z=Z；Q_class≥1/2。J 阈值比较只损失绝对因子 4。 | **PASS**：实际端点资格，非任意 `(-32,32)` box 替代经典 dyadic 支持；不改变 Q19 的精确 source partition。 |

上述新证明只保留 OriginalData、实际 carrier membership、必要时非零原 coefficient 和原非零 a 等来源条件。未发现新 `hEnergy`、目标同义 inequality、预设 Fourier 字典、零谱结构或任意 raw-rho supplier。Q19 的最终精确等式不需要把 x/epsilon 的渐近预算当假设；它也没有给出预算。

静态接缝另核对了 `HasSum.congr_fun` 的新旧函数方向、`hasSum_sum` 的有限求和接口、`sum_filter_add_sum_filter_not` 的方向，以及 Q20 所用 coprime/prime-support 结果；所查数学链无确定阻断。源码-only O/P/Q 拟安装模块仍需按依赖顺序 staging，不能由声明行或 hash 推断现在可编译。

## HOLD：从这四份源码不能跳过的边界

| 边界 | 直接证据 | 仍需供应 |
|---|---|---|
| 有限 c 模式到经典 trace 测试 | Q19 Fourier `:93–100` 仍是 `c∈Ioc 0 floor(10*C)`；`:85–91` 每一模式使用较宽 χ 支撑的 `spectralTest`。Q19 REPORT:97 正确保留此条件。 | **HOLD**：不能按模式删掉原 c 截断直接调用全模数 Kuznetsov。须证明共同扩大/零延拓、测试函数支撑与相应交换，或另一个精确 admissible-test 关联。这是具体 class 2 接缝，不是本轮已证整族等式的错误。 |
| signed arithmetic source 到 normalized Kuznetsov | Q19 Source `:100–103` 和 Fourier `:85–91` 终点仍为原 signed Kloosterman。J `spectral_regular/Part3OriginalNonzeroCuspOneSource.lean:298–314,345–366` 已有 cusp-one 矩阵/相位算术，须复用。 | **HOLD**：真正 Γ0(z)、trivial character、cusps ∞/1、固定 scaling matrices、正模数 c*sqrt(z)、逆 cusp phase、归一化测试变换，及 regular/exceptional/holomorphic/全 singular-cusp continuous 的 trace identity。纯矩阵相位转换不等于全谱展开。 |
| ABL/oldform removal | Q20 Oldform `:13–14,91–99` 的结论仅是整数 K=1；Q19 Fourier `:71–83` 只是算术相位兼容。 | **HOLD**：从真实 Fourier product 抽出逐 dilation 的 Hecke 因子、构造旧类正交基并作 Frobenius/Cauchy 范数支付；`lambda_v(abs(a)*nu)` 不可当所有 dilation 的共同标量。Maass 平方费用 `(abs(a)*nu)^(7/32)`、holomorphic/continuous 的 theta=0 均未由新代码供应。 |
| 真实 A/J/regular/gap | Q20 Supports `:15–16,94–108,147–178` 只证明输入资格，无任何 automorphic Fourier 求和。 | **HOLD**：在真实同一 `(z,j)` Hilbert 范数内实例化 A、共同 interval/phase 的 J、regular cumulative bounds 与 Kim–Sarnak；原 signed frequency 的谱反射关联、t=0 变换极限、holomorphic height k−1 也须接入。 |
| 原始零项、尾项和全部费用 | Q19 Fourier `:207–218,252–277` 精确保留三种 remainder；其 theorem 没有任何误差上界。 | **HOLD**：在同一 OriginalData 六片族上实际支付 y=0、非零 y m=0、global-J tail 和所有 branch/endpoint/class/divisor 重数，保持一个 D、一次 5kappa、固定 moment/导数阶及共同 pre-N 阈值，再返回 Eq. (24)/(25)。 |

## HOLD：三个不同对象不能互换

`ImbalancedChen/Part3DistributionTargets.lean:80–91` 的 **CoprimePacket** 是 level/multiplier/residue/coprimality/beta 的算术载体。P 的 rowPacket 和本轮 prime-support 证明使它绑定原始来源；它没有谱基或 Fourier coefficient 产品。

`ImbalancedChen/Part3ActualLiteralPacketIntegral.lean:210–231` 的 **PacketData** 则是有限 carriers/scales 加任意连续 `kernel`。其 `m/n/level_normalized` 只要求 `(-32,32)`；既不提供经典 dyadic 支持，也不构造 automorphic realization。该 chosen packet 上的正确 Fourier 重构，不能代替从原 source 构造谱数据的 theorem。

`ImbalancedChen/Part3ActualCommonHeightKFactorizationFullGram.lean:47–50` 的 **completedPacketSum** 只有共同 m weight 与 signed arithmetic coefficient，没有 `R_(j,∞)(m)` 或 `R_(j,1)(n)`；`:103–115` 的乘积分解也直接显露这一点。M `exceptional_j_large_scale/Part3ActualExceptionalJAllScaleBudget.lean:202–203` 的 **completedEnergy** 是对该系数和的模平方按 `|actualCoeff|` 加权。K `exceptional_j/Part3ActualExceptionalJPacketAdapter.lean:64–68` 又将 `P.kernel` 覆盖为共同 Bessel-J/q；若预先把 Fourier 产品塞进 kernel，这一步会消去它。已有 M/O 的 W4/28eta 结果可对其定义对象复用，但没有等式或合格比较把该 coefficient/Bessel energy 升格为真实谱能量。

应接入的谱端至少含 `sum_j H(t_j)*conj(M_j)*N_j`，M_j/N_j 必须分别有同一 level 的 ∞/1 Fourier 因子；连续部分必须是全 cusp 的归一化积分。K `regular_continuous/Part3OriginalContinuousPacketExhaustion.lean:231–272` 已有 supplied raw rho 下的正确产品、共轭方向、`1/(4*pi)` 与 `dt/cosh(pi*t)`；`:287–312` 仍输入 raw rho、measurability、local L2、两条 cumulative bounds 和变换界。它是可复用 conditional consumer，不是实际临界线全 cusp Fourier 数据供应。

隐藏源也未被忽略：`.lake/.../20261024z-P3/actual-packet-fourier/Part3ActualFullPacketRawHeightEnergy.lean.txt:8–12,29–35,78–83` 明确是原 Lebesgue-dt Fourier energy；`.lake/.../20261025a-P3-AutomorphicCore/laplacian-equivariance/actual-gamma-unbounded-scalar-measure/Part3Gamma0ActualUnboundedScalarMeasure.lean:6–22,38–62` 是真实 Γ0 Friedrichs/resolvent scalar measure，保留可能的 lambda=0，未给 cusp Fourier trace、Kuznetsov density 或 gap。名字含 actual/Gamma0/Plancherel 不改变这些定理的实际类型。

## 外部输入适用条件的独立核对

本次实际打开一手 ABL v1、Pascadi v3、Young v2、Drappeau arXiv v4，并与原稿对应表核对。下表是数学输入检查，不是 Lean theorem 安装或 kernel 证明；没有据此声称原稿被反驳。

| 一手来源 | 与本任务直接相关的条件 | 本轮边界 |
|---|---|---|
| [Assing–Blomer–Li v1, Lemmas 3.1–3.2, (3.3)–(3.9)](https://arxiv.org/pdf/2005.13915v1) | `(q,r,s,Q)=(1,z,1,z)`、trivial character，`R(n)=sqrt(abs(n))*rho_ABL(n)`；Lemma 3.1 的互素条件和 s=1 时的 supported K 对应 Q20 的字面整数。 | K=1 局部 **PASS**；逐 dilation 的系数/范数关联 **HOLD**。临界线连续支的 Ramanujan 实部为零，不能照搬 Maass 7/64 后再重复支付。 |
| [Pascadi v3, Theorems A/J, Lemma D, Proposition E](https://arxiv.org/html/2404.04239v3) | A 为固定 level、任意复 n 系数，长度≥1/2、cusp density 1/z；J 的长度和 level 尺度均≥1/2、∞ scaling=Id、一个共同 additive phase，允许阈值与 `max(N,Q²/N)` 对应。trace/变换需真正平滑紧支撑测试。 | Q20 端点与阈值 **PASS**；实际 A/J 二次型 **HOLD**。共同部分区间的 Fourier completion 须在真实谱范数中用，不能变成任意逐 level mask。 |
| [Young v2, Proposition 8.2](https://arxiv.org/pdf/1710.03624v2) | formal Eisenstein inner product 给连续谱换基的基无关恒等式；须保留正确形式范数和全 cusp 积分。Eisenstein 函数本身不是普通 L2 cusp vector。 | **HOLD**：实际 character-pair fiber/oldclass 归一化未供应。没有把文中其他 squarefree-newform 结论误用成任意 level 的这一接口。 |
| [Drappeau v4, Lemma 4.3、Proposition 4.7、(4.27)](https://arxiv.org/pdf/1504.05549v4) | 4.3 的 s=1 特化给 c*sqrt(z) 与指定 cusp phase；4.7 要求 T≥1、N≥1/2，覆盖 holomorphic、Maass 和全 singular-cusp continuous 三种二次型，density 为 1/z；(4.27) 保留 `1/(4*pi)`。 | 真实 regular cumulative 输入 **HOLD**。不能用单个平滑积分或有限假谱态代替整个谱；累计壳层返回仍须接入正确变换界。 |

Body:238–254、Medium:360–390,463–483 与 Classical:29–137 所写的目标确实要求这些对象和条件。Q20 已修正容易漏掉的 m=V、z=Z 端点，足以支持其限定结论；这不减少完整谱实现的义务。

## 既有零项/尾项供应与费用不重复记账

不能笼统称“只存在单频 tail”。隐藏 `20261028-Medium-Polynomial-Sol6/Part3ActualSixKernelCommonHardTail.lean:33–38` 已有六核共同 hard-tail bound；production `Part3ActualCompletedHardTailMass.lean:84–105,111–138` 已有源 tail 与 rawLabelBudget。其窗口 `ceil(10*C*R/B)` 可按 `R=x^(eta/2)/10` 与 O 的 global J 作算术对齐，但仍需绑定当前 OriginalData 六片/source mass、固定充分导数阶并完成同一参数顺序下的归一化预算。I `spectral_eq24/Part3ActualZeroPoissonNativeSource.lean:89–109,121–171` 也已有真实零频来源分解和平方界；本轮未把它们实际应用成 `sixRemainder` 的完整总费用。

P 的 ceil、六片 rho、common-mask log²、primary-nu 和一个 occupied D 结果照旧复用，不分配新验证信用。P 的 q=14 只付 cutoff 2eta 与 W0 12eta；M/O 第四阶 28eta 独立保留。局部 `eta=min(epsilon,sigma/10)/172` 与 `15a/16` 支出不使未列举目录免费。Medium:417–424 的固定导数阶、共同阈值和一次 5kappa 仍是最终调用义务。

## 分类及最终前提影响

**PASS / class 2：** Q03 第 6 项的真实两固定 Z 全族 Fourier 关联已由四级有限求和与 HasSum 供应；第 7 项中实际 row 的 coprime/K=1 算术资格、第 8 项中 A/J 真实端点/尺度比较得到局部供应。这些是有内容的原来源证明，不是同名 wrapper。

**HOLD / class 1：** 拟安装模块、namespace/API、完整 import closure 与 elaboration/kernel 验证仍未执行；本报告的源码静审不能代替这些。

**HOLD / class 2：** c 模式支撑到全模数 trace 的 exact caller、原始零项/尾项绑定、全部费用目录和共同阈值仍须完成。

**HOLD / class 3：** 实际 normalized trace、离散/holomorphic/临界线全 cusp Fourier realization、oldform/continuous norm 与 A/J/regular/gap 的真实实例化仍是实质形式来源义务。所审模型缺对象不自动构成原稿反例；受查生产、公开 source-only、隐藏来源与一手数学输入中，没有发现可以直接无条件关闭这些接口的已安装供应。

给总审的前提结论：**本轮仅消除原始整族 Fourier 关联、actual-row coprime/K=1 与经典端点资格；真实谱能量前提消除为零。可登记为 source-only 局部 PASS 候选叶，不能据此把 P3.5.uniform_spectral、Eq. (24)/(25) 完整返回或任何 hLower/hUpper/hdensity/P6.3 父目标转蓝。** 后四者不在本专项的重审范围；本组未给它们任何新的整体验收供应。

## 冻结文件、行号与 raw SHA256

本复核直接读取并计算四份新 Lean 的 raw hashes；对 Q19/Q20 REGISTRY 所含的 **34/57 个唯一路径**递归核对 raw hash/bytes，均无不符。此项是元数据一致性，未声称逐一重证其全部内容。四份新 Lean 的 admissions/axioms/unsafe/evaluation 指令静态扫描无命中。以下报告和登记文件也已经实际读取，结论与其 broad OPEN/HOLD 一致。

| 冻结产物（相对 Q） | 行数/范围 | raw SHA256 |
|---|---|---|
| `automorphic_dictionary/Part3OriginalTwoZSourceAssembly.lean` | 194 行；核心 39–191 | `5ab4eddbbe4cdfac80d517a1558565e07c1a9bd819c02e8b0e0ae5af30a063cc` |
| `automorphic_dictionary/Part3OriginalTwoZFourierAssembly.lean` | 313 行；核心 46–310 | `f54ee12b12efd7a6de2c0323ae123f2e95d660bed8c44dba180a65af4001c990` |
| `actual_spectral_energy/Part3OriginalRowOldformArithmetic.lean` | 102 行；核心 30–99 | `fbda3e52f45e76e76330ffad9e01e054297c047af8b9ba749e23263288c76e5b` |
| `actual_spectral_energy/Part3OriginalClassicalSpectralSupports.lean` | 181 行；核心 34–178 | `17ef27e3c8d982eb49bef412d839758e2dc8d150c7818611972f07c6d5d2dbf0` |
| `automorphic_dictionary/REPORT.md` | 3–5,35–107,113–118 | `9cf5117fc892a8783acb33aec96e26f6878a47d6205c546246ca6733365811ac` |
| `automorphic_dictionary/REGISTRY.json` | 34 唯一路径元数据已核 | `5f9dfae1f7983f4a9dbab2fbb714ed14980bf91024cb52a621352455314a9337` |
| `actual_spectral_energy/REPORT.md` | 3–5,21–54,62–103 | `69fed3ec753f0635dd051e02e0fbde8f2d8bf78a9e04571184b116adb326267f` |
| `actual_spectral_energy/REGISTRY.json` | 57 唯一路径元数据已核 | `bea77d5aecc35963636491679cb04c1003a99144b1ed5876882960528655afce` |

| 原稿/复核依据 | 本次使用范围 | raw SHA256 |
|---|---|---|
| `Q/BRIEF.md` | 来源级规则和任务边界 | `727be2f0211dade53d575cef30e55cf57d61d3f858ea47b22ae996f15227046d` |
| `P/reviews/t29_review_spectrum.md` | P 局部 PASS / 谱整体验收 HOLD | `ea12bfe513770b0336b7ff8de3e2cc361999c4a42a357c5d93dd5c2fcd01a51c` |
| `Q/q03_original_gap_triage/REPORT.md` | 97–150 | `5dfb3069d4d021acad6d27bf36295adcef9e288388ad46ab1afbf15261b436cd` |
| `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`（Body） | 201–254 | `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` |
| `../chen-imbalanced-semiprimes/paper/source/modules/distribution-medium-completion-20261010.txt`（Medium） | 299–424,463–483 | `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7` |
| `../chen-imbalanced-semiprimes/paper/source/modules/final-classical-input-correspondence-20261010.txt`（Classical） | 23–137 | `9604bfb8fdf7325205c8ebe431c7c5e977a3e5bea07e79b8d209548e1a4069db` |

| 模型边界关键源码 | 核心行 | raw SHA256 |
|---|---|---|
| `ImbalancedChen/Part3ActualLiteralPacketIntegral.lean` | 210–231 | `500b7c1476c8afb777551807f1f737b17d785aeafec401c7b691fd46b0b9aa55` |
| `ImbalancedChen/Part3ActualCommonHeightKFactorizationFullGram.lean` | 47–50,103–115 | `3f47792d598ef407c117bd3938247646ad00484d2eea5f74fe7603cd6884bf47` |
| `K/exceptional_j/Part3ActualExceptionalJPacketAdapter.lean` | 64–77 | `9e2fe13c39c477a8798608c150c530b8e6711c4f0bc42c04070405360c5e56e5` |
| `M/exceptional_j_large_scale/Part3ActualExceptionalJAllScaleBudget.lean` | 202–203,222–278 | `e280bb9b25f1f1864ba08563820ff1c31c540547c50f00805d3f706fbf1a7aef` |
| `K/regular_continuous/Part3OriginalContinuousPacketExhaustion.lean` | 231–272,287–312 | `e1640ad048d20b469458c255d949460fb081b07f18e32f068c05a9ded5fb2597` |
| `.lake/proof-continuation/source-reviews/drafts/20261024z-P3/actual-packet-fourier/Part3ActualFullPacketRawHeightEnergy.lean.txt` | 8–12,29–35,78–83 | `5831a6534e7172af51b361a0f422e0c464459107c113d62b75197e45b3c075ce` |
| `.lake/proof-continuation/source-reviews/drafts/20261025a-P3-AutomorphicCore/laplacian-equivariance/actual-gamma-unbounded-scalar-measure/Part3Gamma0ActualUnboundedScalarMeasure.lean` | 6–22,38–62 | `f467ee8f23c750c641655c6ead0a88d2fad20838dec2dd145fcfaa2c9ce9d53a` |
| `.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Polynomial-Sol6/Part3ActualSixKernelCommonHardTail.lean` | 33–38 | `9f2dbda79256a09fc8b7d173ecddbf16b68db341e0b9cdd41e46deac10cb76a6` |
| `ImbalancedChen/Part3ActualCompletedHardTailMass.lean` | 84–105,111–138 | `2c84a397d5620e43c3e845046e75c5d506ae3ba0e27e1baddd3fd71a0ce2e188` |

复核人：`/root/q29_review_automorphic`。日期：2026-11-02。最终裁定仍是 **局部 PASS / 完整 HOLD**。
