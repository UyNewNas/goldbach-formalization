# Q20 actual_spectral_energy

结论：**PARTIAL — 真实 automorphic 二次型、统一 7/32、Eq. (24)/(25) 仍 OPEN/HOLD。** 新增两份严格 Lean 源码候选，只消除原始行的 ABL 算术资格与 A/J 端点/参数资格；没有把 coefficient/Bessel `completedEnergy` 重新命名为谱能量，也没有把目标估计放进前提。

`compiled=false; kernel_verified=false; formal_credit=0`。未运行 Lean、lake、编译器、CI、proof guard、数值/有限守卫、Git 或子代理。所有有限 guards 保持 **UNEVALUATED**。只写本目录；旧源码、主节点表、c/K 均未修改。

## 已核原稿、前轮和去重范围

先读 Q BRIEF、P BRIEF、P medium/eta REPORT 与 REGISTRY、P `reviews/t29_review_spectrum.md`，再核原稿 `manuscript-body.tex:201–254,343–354`。详细原始来源为 `distribution-medium-completion-20261010.txt:299–420,463–483`，尤其 `:360–380` 的 ABL/全谱/式 (24)，`:382–388` 的式 (25)。原稿 SHA256 仍为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。

内容/文件名检索显式覆盖 `ImbalancedChen`、全部 `docs/source-only` 和隐藏 `.lake/proof-continuation/source-reviews/drafts`，使用 `rg -uu`，检查 Kuznetsov、Pascadi、Assing/ABL、Kim–Sarnak、oldform、continuous、975/4096 等候选。对同名快照按原始来源去重，没有把许多 snapshot 当成不同证明。额外读取 Q03 triage、Q02 remote reuse、P external reuse 的边界。负搜索只说明上述受查范围，没有声称全世界不存在其他形式化。

Q19 的整族两 Z / Fourier 工作独立进行；本任务不重写其分组、原始 Poisson 等式或 Fourier 展开。P 已有的 row 相位抵消、全局 ceil/rho、W0/28eta、primary-nu、common-mask 和 D 费用亦不重证。

## 新增的必要局部证明

### 1. 原始 primary 行到每个 ABL dilation 的 K=1

`Part3OriginalRowOldformArithmetic.lean`，拟安装为 `ImbalancedChen.Part3OriginalRowOldformArithmetic`。

- `outputCarrier_multiplier_prime_support:30` 从实际 `primaryBlock` 的源成员和 computed key 得到 `p|nu => p||a|`。这是 P 的真实行，不是任意 `CoprimePacket` 的新增字段。
- `row_multiplier_prime_support:43` 利用实际 occupied level 的 n 见证。`original_index_coprime_abl_argument:51` 进而证明 `(n,|a|nu)=1`，精确对应 ABL Lemma 3.1 代入 `(n_ABL,m_ABL)=(|a|nu,n)` 的条件。
- `original_abl_argument_coprime_level:59` 证明 `(|a|nu,z)=1`。没有把 Poisson 模数 c 当 level，也没有声称 nu 整除 c。
- `oldformExceptionalInteger:71` 是 s_ABL=1 时的字面整数

  `supportedPart (z / gcd(v*q_f,z)) (|a|*nu)`。

  已有 `supportedPart` 正是保留第二参数素因子的完整幂。`original_oldformExceptionalInteger_eq_one:94` 先证明其第一参数整除 z，再由互素性证明 supported part 为 1。它对所有自然标签 q_f,v 成立，因此同时覆盖所有合法 `q_f|z, v|z/q_f`。较强的整数断言不声称非法标签对应某个 oldform。

这里只证明**算术 K=1**。Hecke 系数关系、不同 dilation 的 `lambda_v`、oldclass 正交基、Gram/Frobenius 成本和 `(|a|nu)^(7/32)` 的谱范数支付均未被证明。后续实际谱调用仍需 `a!=0`；算术函数在退化 a=0 情形有值并不许可该谱扩张。

### 2. A/J 的实际端点与尺度

`Part3OriginalClassicalSpectralSupports.lean`，拟安装为 `ImbalancedChen.Part3OriginalClassicalSpectralSupports`。

P 原始 n 支持是 `(U,2U]`；`original_nonzero_row_classical_length:77` 将真实非零 signed row coefficient 还原成已有 `dyadicBeta`，**实际调用** production `nonempty_endpoint_bounds`，得到 `L=U/nu>=1/2`，没有重写端点证明。`original_fixed_level_A_range:94` 用真实 `Z<=z` 得

`X0=1+Z/L <= 2*max(1,z/L)`。

这是固定 level A 的参数资格，不是 A 的能量结论；系数仍可以随 z 变。

O `commonMBlock:114` 是 `[V,min(2V,J+1))`，其中 `V=2^j`。直接说它在经典 `(V,2V]` 内会漏掉 m=V。本文件保持原块和相位完全不变，取只用于经典支持的 `M_class=V-1/2`：

- `classicalMScale_bounds:36`：`M_class>=1/2` 且 `V/2<=M_class<=V`。
- `commonMBlock_classical_support:49`：整个原块落在 `(M_class,2*M_class]`。整数上界 m<2V 给 m<=2V-1，故 m=1 与所有 dyadic 左端点均保留。
- `commonPoissonCompleted_classical_support:64` 同时保留 O 的同一 interval/weight，phase 的物理分母仍是 `64*V`，并未换成 `64*M_class`。

P 物理 level plateau 是 `[Z,2Z]`。`original_level_classical_cover:131` 保留 z=Z，将正谱范数所需的 level 支持覆盖于 `(Z/2,Z]` 与 `(Z,2Z]`。由 P 的真实 `scaleS_one_le`，`original_levelChart_one_le:122` 给 Z>=1，故两种经典 Q 都至少为 1/2。这只是每个固定物理 Z 的经典两区间覆盖，不改变 Q19 的原始 source partition。

`original_J_threshold_comparison:147` 证明对 `Q_class=Z/2` 或 Z，

`max(V,Z^2/V) <= 4*max(M_class,Q_class^2/M_class)`。

因此端点转换不会偷偷缩小 J 的许可阈值，所付常数独立于源、level、频率和目标规模。本文件没有对任何 automorphic Fourier 系数求和，没有调用或假设 A/J 谱界。

## 真正谱供应的核查结果

以下为现有来源的准确复用边界；所有原始路径、hash、声明、imports 见 REGISTRY。

| 来源 | 已有实际结果 | 仍缺什么 |
|---|---|---|
| `Part3OriginalNonzeroCuspOneSource`（J/spectral_regular） | 原始单位类到 Gamma0(z) 的 cusp-one 矩阵/double-coset 算术，真实正模数 sqrt(z)c 与相位 | 不是 normalized trace formula；没有全谱 Fourier 产品 |
| `Part3ActualCuspPacketPairing:27,57` | 任意真实 Gamma0 不变函数的 cusp Fourier chart 与算术系数配对 | 不构造 Maass/Eisenstein 谱基，不给 ABL 的 a*nu Hecke 关系 |
| `Part3Gamma0ActualUnboundedScalarMeasure:38,59,103` | 真商空间 Friedrichs/resolvent 的非负 scalar measure、norm² 质量与矩 | 文件 `:19–22` 明确保留 lambda=0；没有 cusp 完备分解、Kuznetsov normalization 或 975/4096 gap |
| `Part3GammaCuspidalEigenSpectralOrthogonality:36` | 真实 native infinity-cuspidal eigenvector 与 incomplete Eisenstein tests 的谱正交 | 只给已提供 eigenvectors；没有离散谱基存在/完备性、所有 cusp completeness 或 gap |
| `Part3ActualLevelComplexEisensteinFourier:225–227`、`Part3CharacterEisensteinSeries:8–10`、`Part3FiniteLevelEisensteinOldforms:206,215` | 实际 level/character Eisenstein 及有限 dilation identities | 参数限制为 Re(s)>1；不是全 cusp 临界线谱基。full-level scalar scattering 也不是一般 level 的全矩阵 |
| K `Part3OriginalContinuousPacketExhaustion:118,159,231,265` | 正确全 cusp `dt/cosh(pi*t)`、`R=sqrt(n)rho`、共轭 infinity 因子和外置 `1/(4pi)`，真实有限乘积展开 | `:290–312` 仍输入 raw rho、measurability、local L2、两条 cumulative bounds、transform bounds；没有把 raw rho 实现为实际全 cusp 临界线系数 |
| J `Part3RegularCumulativeShellPayment`、K `Part3RegularPositiveMeasureExhaustion` | 给定真正 cumulative quadratic forms 后的 shell/Cauchy/全积分耗尽 | 正规、holomorphic、continuous 经典 cumulative bounds 本身与实际谱态仍未供应；t=0 transform 极限、k-1 convention 须实际接入 |
| hidden `Part3ActualFixedSliceGlobalZABLNorm` | 实际 fixedSlice 原始系数的 ABL-nu 重索引和 counting norm | 没有 automorphic Fourier 因子；文件 `:5–9` 明确不证明 ABL/Kuznetsov/Pascadi return |
| `Part3ZExceptionalParameter:74`、`Part3ZExceptionalThresholdGeometry:146` | **以前提** lambda>=975/4096 推出 tau<=7/32 与阈值幂运输 | 没有证明真实 Gamma0 cuspidal eigenvalues 满足该下界 |
| `Part3ZRegularSpectralPolynomial`、`Part3ZExceptionalSpectralPolynomial` | 已有 Eq24 表达式到 Eq25 的尺度/截断代数 | 没有以真实谱二次型证明 Eq24 |

一手数学来源并未缺席。本轮重新打开 [ABL v1](https://arxiv.org/pdf/2005.13915v1) 的 Lemmas 3.1/3.2、(3.3)–(3.9)，以及 [Pascadi v3](https://arxiv.org/html/2404.04239v3) 的 A/J/C/D/H 与 [Young v2](https://arxiv.org/pdf/1710.03624v2) Proposition 8.2；Drappeau 作者站超时后，核对了本地 P/K 保存的第 16 页以及[一手 arXiv v4](https://arxiv.org/pdf/1504.05549v4) Proposition 4.7。不能将浏览到的数学定理直接算成已安装的 Lean theorem。

实际参数对应已逐项核清：ABL `(q,r,s,Q)=(1,z,1,z)`、trivial character、`R(n)=sqrt(|n|)rho_ABL(n)`，新文件消除其原始行的 coprime/K 条件；Maass 平方费用仍为 `(|a|nu)^(7/32)`，holomorphic/continuous 取零 Ramanujan 幂。ABL 的 multiplier 可随 dilation 变化，连续谱须在 character-pair formal Plancherel fiber 中换基，不能把一个 Eisenstein 函数当 L2 cusp vector。[ABL v1, pp. 8–11](https://arxiv.org/pdf/2005.13915v1)、[Young v2, §8](https://arxiv.org/pdf/1710.03624v2)。

Pascadi A 是固定 z、cusp density 1/z、任意复 n 系数的估计；J 是 infinity scaling Id、一个共同 phase 的 level average。新支持转换给实际 `L,M_class,Q_class>=1/2` 和阈值比较；共同 partial interval 的 Fourier completion仍须在**真正的** `(z,j)` Hilbert 范数中使用。相反符号频率亦须和实际谱 basis/reflection identity 相接，不能仅凭算术共轭相位就删掉 signed Fourier 参数。[Pascadi v3, Theorems A/J](https://arxiv.org/html/2404.04239v3)。

原稿已有独立的 paper-level 推导 `../chen-imbalanced-semiprimes/proof-library/source/spectral-regular-polynomial-derivation-20261010.txt`：保留两 cusp density、level Cauchy 仅 sqrt(Z)、regular dyadic shell 和 exceptional packet power，再推出 Eq24。它的边界明示 classical trace、oldform/continuous fiber 与 smooth separation 输入。本任务精确复用该推导，不再抄一份以相同输入为前提的 Lean consumer。`fixed-d-abl-packet-input-audit-20261010.txt:114–157` 已有正确的逐 dilation 范数论证；新代码只补其实际 source K=1 资格。

## 为什么现有 completedEnergy 不够

`ImbalancedChen/Part3ActualCommonHeightKFactorizationFullGram.lean:47–50` 的 `completedPacketSum` 是共同 m weight 和 signed arithmetic coefficient 的有限和。M `Part3ActualExceptionalJAllScaleBudget:202–203` 的 `completedEnergy` 对其模平方加权求和。二者没有 `(z,j)` 谱态索引，没有 `R_j,infty(m)`、`R_j,1(n)`，没有连续谱测度。

K `Part3ActualExceptionalJPacketAdapter:64–77` 用 `withPositiveKernel` 将 `P.kernel` **替换**为 Bessel-J/q。若后来把真实 Fourier 产品填入旧 kernel，此替换仍会消去它。因而 M/O 的完整 28eta 和小 Y 对数证明即使保持原样，也只估计它们实际定义的 Bessel/coefficient 对象。既无等式也无合格比较把它升级为 Eq24 的谱二次型。

真实边界至少需要原始 arithmetic Kloosterman 源与 `sum_j H(t_j) conj(M_j) N_j`、正规/holomorphic 部分及全 cusp continuous 积分的同一化。其中 `M_j` 必须含 infinity Fourier 系数，`N_j` 必须含相同 z/符号的 cusp-one Fourier 系数；ABL 换基后算术系数才是 P 的 beta/phase。当前候选没有假定这条同一化，没有空谱结构、零 Fourier 构造、`hEnergy` 或目标等价 premise。

## 尾项与总预算不误报

除 P 已登记的单频 hard-tail theorem 外，hidden `20261028-Medium-Polynomial-Sol6/Part3ActualSixKernelCommonHardTail.lean:33` 已有 `sixKernel_common_hard_tail`，production `Part3ActualCompletedHardTailMass:84,111` 已有 `source_common_hard_tail` 与 `rawLabelBudget`。这些是真六核/源质量结果，不能说“只剩单频 tail 供应”。其 window 是 `Icc ±ceil(10*C*R/B)`；用 `R=x^(eta/2)/10` 可对齐 O 的 J，随后仍须实际绑定 OriginalData 六片、source masses、充分固定导数阶与原参数顺序。Q20 未重复或完成这条不同任务链。

P 的 q=14 只覆盖 cutoff 2eta 与 W0 12eta，order-four 28eta 仍独立保留；不能把未列出的 endpoint/class/divisor 目录视为免费。zero-y、m=0、所有原始分支及 pre-N 共同阈值仍须在同一源族上接入。原稿一次 5kappa、一个 D、`kappa<=sigma/200` 和先固定 moment/导数阶均保持不变。

## 分类、验证和剩余义务

新增 prime-support/K、A/J 真实端点资格是 **class 2：可填补的省略**。源码未 elaboration，import/namespace/API 仍有 **class 1** 风险；hash、声明、JSON 和禁止语法扫描只是静态元数据检查。

真实 normalized trace、actual cuspidal/oldform/continuous 全谱 Fourier realization、gap 与 A/J/cumulative 的实际实例化仍是 **class 3：可能实质省略的来源义务**。缺口比一个 Lean 名称更深；但当前源码模型缺对象不自动构成原稿反例，且已核一手数学输入确实存在。本任务没有发现可以无条件安装并直接关闭它们的可靠现成形式化供应。

实际消除：原始 primary 行的 `(n,|a|nu)=1`、`(|a|nu,z)=1`、所有 dilation K=1；真实非零 row 到既有长度端点；A X0 的原始 level 比较；J 两个半开边界及可比阈值。**消除的谱能量前提为零**。

仍须：真实谱 realization/trace；原始 signed source 到全谱 products；oldclass/continuous 变换及成本；actual A/J/regular/gap；零项/尾项与完整费用；Eq24 的真正能量返回和后续 Eq25/medium 总装；安装及最终用户许可下的 elaboration/kernel 验证。Q29 已给两候选限定静审 PASS，并独立复核本清单 57 条文件记录的 hash/bytes 零不符；其范围仅为真实 primary 算术与 A/J 支持资格，真实 spectral energy 仍 HOLD。独立复核由 Q29 另写，不能由本作者报告替代。
