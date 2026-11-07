# R23 — actual_spectral_energy / D21

结论：**PARTIAL：补出原始行的 native signed Fourier 来源转换；真实 A/J、regular cumulative、ABL 范数及 Kim–Sarnak 谱输入仍 HOLD。** `Eq.(24)`、完整 `Eq.(25)` 谱返回和统一 `7/32` 未闭合。真实谱能量前提消除数为 **0**。

`compiled=false; kernel_verified=false; formal_credit=0`。未运行 Lean/Lake/编译器、guard、CI、数值 replay、Git 或子代理；所有有限体保持 `UNEVALUATED`。只写本目录。恢复后核对 BRIEF/DISPATCH 和已有文件，未将中断前未落盘内容当成交付。

## 精确任务与原稿判断

依照 `Q/q03_original_gap_triage/NEXT_DIRECT_PROOF_REVIEW.md:229–237` 的 D21，目标仍是 **D19/D20 同一真实全谱**上的 fixed-level A、common-phase/interval J、regular/holomorphic/full-continuous cumulative bounds 和实际 cuspidal gap。所读基线为 Q20 REPORT/REGISTRY、Q29 独审、Q30 最终节点表，以及：

- `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:238–254`；
- 同目录 `modules/distribution-medium-completion-20261010.txt:360–388,463–483`；
- `modules/final-classical-input-correspondence-20261010.txt:29–137`；
- `../chen-imbalanced-semiprimes/proof-library/source/spectral-regular-polynomial-derivation-20261010.txt` 和 `fixed-d-abl-packet-input-audit-20261010.txt`。

原稿确实调用经典数学定理，并没有把 coefficient/Bessel energy 当作谱定理。原正负频接口省略可以在实际 Fourier 积分层补齐，本轮给出该层的证明；A/J/ABL/regular/gap 本身依赖真实谱对象和深层经典结果，不能仅靠这些积分定义推出。所核引用及参数未显露原稿反例；当前 **缺少正式供应不等于已经发现论文数学错误**。但在本工程要求不加公理、不能把目标放回前提的范围内，核心仍属 class III，而非换一个 Lean 名字即可消除的 class I。

## 新数学源码及严格范围

`Part3OriginalSignedNativeCuspFourier.lean`，拟模块 `ImbalancedChen.Part3OriginalSignedNativeCuspFourier`。217 行，13 个 theorem、1 个 definition；raw SHA256 `766d00b552b66d4467d857e9e02553fc9431410d9028276fdd491f45ec747336`，10472 bytes。

本文件使用已有 `oldSection/newSection`、`oldFourierCoeff/newFourierCoeff`。它们是实际 `Gamma0 N` 不变函数 `f : ℍ → ℂ` 在指定 old/new cusp-one scaling 上、固定正高度 `y` 的 normalized-Haar Fourier 积分。没有新建任意 `rho`、零谱、`PacketData` 或抽象能量结构。

1. `conjugateForm:43` 是实际函数逐点共轭；`:45,50,56` 直接证明其 involution、连续性与同 level 的 trivial-character Gamma0 不变性。
2. `circleFourierCoeff_conjugate:66` 从 Fourier 定义、字符共轭和 Bochner `integral_conj` 得到

   `C_(conj f)(n;y) = conj(C_f(-n;y))`。

   `oldSection_conjugate:75`、`newSection_conjugate:86` 直接下沉到已有 quotient sections；`:99,108` 给两原 chart 的 Fourier 恒等式。没有假设 `f` 或其 Fourier 系数为实数。
3. `cuspPhase_cancels_actual_section_signed:119` 补全实际两符号：正频使用 `e(-n/N)`，负频使用 `e(+n/N)`，相应 Fourier index 保留 `n` 或 `-n`。负频证明实际调用原 `oldFourierCoeff_phase`，使用相反字符相乘为一。
4. `original_signed_row_native_term:138` 和 `original_signed_row_native_sum:154` 消费 P 的 `rowCoefficient_eq`，得到**原始** `rowPacket D r k z`、`nCarrier D k z.val` 与 `blockBeta D r k (decode k z.val n)` 的配对等式。原源重数、非单位删除与已占用 level 均由该原对象保留，未重新假设算术资格。
5. `original_negative_row_native_conjugate:174` 把该实际负行化为正 index 的共轭形式：**beta 和函数同时共轭**；`:198` 是此实际有限行 functional 的精确 norm equality，没有不等式估计前提。

若用 `B(n)` 简记这个原始 `blockBeta`，负行结论是

`sum_n c_-(n) C_old^f(-n;y) = conj(sum_n conj(B(n)) C_new^(conj f)(n;y))`，

两边都在同一个实际 `nCarrier` 上。证明中的 `hfΓ` 是原函数的 Gamma0 不变性，`hy` 是实际 chart 的正高度，`hnegative` 是原行 sign flag；它们均不编码谱估计。

**范围不能扩大：**固定高度的 Fourier integral 还含其 Maass/Eisenstein Whittaker 高度因子，未被识别为 `R(n)=sqrt(|n|)rho_ABL(n)`。已有 full-cusp operator HilbertBasis 及其 smooth Gamma-invariant eigenprofile 源码，见下方精确复用定位；本文件没有把它们关联到 classical Whittaker-normalized Fourier 系数、同 eigenvalue 的谱共轭实现或完整 Kuznetsov 求和。此定理也不把 weight-k holomorphic forms 当作 weight-zero Gamma0 不变函数。全 trace 的 index 还要结合原 `a`、Poisson m 与 y 的符号；本文件末尾 row wrapper 只写其现有 `k.2.2`，通用 native signed lemma 保留独立 Bool，未声称完成 R21 的整条符号字典。

## 锁定 Mathlib 后发现的必要来源修复

`lake-manifest.json` 固定 mathlib 为 `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。本地对应 package 不存在，故实际下载该 revision 的两份原始源到 `primary/`，未调用工具链。

该 pin 的 `Mathlib/Analysis/Fourier/AddCircle.lean` 在 `:101` 已结束 `namespace AddCircle`，根命名空间声明 `fourier:123`、`fourier_neg:160`、`fourierCoeff:298`；只有所用 Haar measure 继续名为 `AddCircle.haarAddCircle`。`Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:173` 给无 integrability 前提的 `integral_conj`。[锁定 Fourier 源](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Analysis/Fourier/AddCircle.lean)、[锁定积分源](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean)。

受查生产及 source-only/ignored drafts 未找到使旧 `AddCircle.fourier*` 成立的兼容 alias。本目录 `repairs/` 保存两份最小修复副本，逐字替换规则仅为 `AddCircle.fourier` → `_root_.fourier`，覆盖相同前缀的定义/定理名；数学体、假设、命名空间与其他 imports 不变。**这是旧来源修复/复用，不是新增数学定理。**

| 原拟安装模块 | 原生产 raw SHA256 | 本目录替换副本 raw SHA256 |
|---|---|---|
| `ImbalancedChen.Part3CuspTranslationFourierPhase` | `f008945e597a8dfbc0fdeb424d593a8abbd43e28f1da07f100b08b9fee4171cf` | `5aa2566f75a7ff66b58ee848f9ecad3384a7498f85af6f4970f32d9de1b85756` |
| `ImbalancedChen.Part3ActualCuspFourierSection` | `62d42386ad27c056371ffbb4164aea62b8980e875cb97be42ae5f5483453fcd1` | `7cc15af0858e3df58f09c0b94463ed2475629119a291c1045a37067036ebe36a` |

将来 staging 须先按上述模块映射采用修复副本，再安装 P 的 `Part3OriginalPrimaryPacketRows` 及其既有 source-only 依赖，再装新文件。当前工作树旧文件未动；本轮不声称整个 import closure 已可 elaboration。两个 Mathlib 原始副本仅作证据，不拟当作新的项目模块。

## D21 经典源的实查结果

实际重新打开了 [Pascadi arXiv:2404.04239v3](https://arxiv.org/html/2404.04239v3)、[Drappeau arXiv:1504.05549v4](https://arxiv.org/pdf/1504.05549v4)、[ABL arXiv:2005.13915v1](https://arxiv.org/pdf/2005.13915v1) 和 [Young arXiv:1710.03624v2](https://arxiv.org/pdf/1710.03624v2)，并读取已有 primary 提取。没有把浏览所得定理转成 Lean axiom。

| 输入 | 已核实际适用边界 | 本轮未供应的部分 |
|---|---|---|
| Pascadi A | 固定 level z、density `1/z`、任意复 n 序列；实际长度与许可 X 范围沿用 Q20。 | 同一真实 cusp basis 上的估计。新共轭式只处理 native Fourier 积分。 |
| Pascadi J | infinity scaling 为 Id，单个共同 phase，长度和 level scale 至少 1/2；共同 interval completion 须在同一 `(z,j)` 范数。 | 该真实范数的 J 估计及其共同区间 completion；旧 coefficient packet completion 不能替代。 |
| Drappeau 4.7 / Pascadi H | regular、holomorphic、全部 singular-cusp continuous 三种 cumulative forms，匹配归一化。 | 真正 cumulative norm supplier；t=0 limiting transform、holomorphic height k−1 的实际接入。 |
| Kim–Sarnak，经 Pascadi C 明列 | cuspidal parameter 为 `7/64`，本稿用双倍参数 `7/32`。 | 实际 Gamma0 cuspidal eigenvalues 的 gap。标量零谱必须保留；不能对整个 quotient spectral measure 宣称同一 gap。 |
| ABL 3.1/3.2、(3.3)–(3.8) | `(q,r,s,Q)=(1,z,1,z)`；逐 dilation multiplier 允许不同；Maass squared cost `(abs(a)*nu)^(7/32)`。holomorphic/continuous Ramanujan 幂为零。 | 实际 oldclass/Hecke identity、归一化 dilation 与其真实范数；Q20 的 K=1 不提供这些。 |
| Young 8.2 | 临界线全 character-pair formal Plancherel fiber 换基，形式范数分母不能省；不需挪用其后 squarefree-newform 限制。 | 全 cusp 临界线 Fourier 实现和实际 fiber norm identity。 |

本轮曾尝试打开 Kim–Sarnak 原 JAMS PDF，AMS 返回 403；未将其标为已读。gap 版本核对依赖实际读到的 Pascadi v3 Theorem C 及其明确引用。没有在未读原文上声称独立核完 symmetric-fourth 证明。

Q20 的 `M_class=V-1/2` 与两个 `Q_class`、阈值常数四和实际相位分母 `64V` 完全复用，未重新计进展。Q20 的 actual-row coprime/K=1 也未重证。原稿已有 regular shell polynomial 推导，J/K 的 conditional shell/exhaustion 已存在，故本轮未再写 `hCumA/hCumB/hEnergy` 消费者。

## 检索范围、前提影响与余项

检索显式覆盖生产 `ImbalancedChen`、全部 `docs/source-only` 和 `--hidden` 的 `.lake/proof-continuation/source-reviews/drafts`；内容查询核查 Pascadi、ABL/Assing/Blomer、Kim–Sarnak、cumulative、975/4096、native Fourier conjugation 及 namespace aliases，重复 publisher/frozen 副本按原来源去重。未发现可以直接关闭 D21 的已安装或 source-only 经典全谱供应。这个否定仅限受查范围，不声称全世界没有相关形式化。

关键复用边界继续成立：`Part3ActualCommonHeightKFactorizationFullGram.completedPacketSum` 无 Fourier 谱态因子；M 的 `completedEnergy` 仍是该系数和的加权模平方；K 的 `withPositiveKernel` 会覆盖 kernel。K `Part3OriginalContinuousPacketExhaustion:287–312` 仍要求 raw rho、局部 L2 与两条 cumulative norm。hidden 真 Gamma0 scalar measure 保留可能零谱；hidden fixed-slice ABL norm 是算术计数范数。均未被提升为自守能量。

**补充复用纠偏，已直接读取原体。** R21 定位、R30 独核的 hidden `20261026b-GammaCompactness/Part3ActualFullCuspEigenbasis.lean:94` 已构造整个 `ActualFullCuspL2` 的 `actualCuspHilbertBasis`，并有真实原 resolvent eigenvector 身份；不是有限 slice，也不输入 `hBasis/hComplete`。其 raw SHA256 为 `d1e28c1a6b3a3ec757f63aca24c2004f8a1285827ba2f7c41c09a020e07756d7`。另 `20261026b-AffineRellich/Part3ActualFullCuspLambdaSquaredDomain.lean:47,63,118` 已给 native graph、domain 的 lambda-squared coefficient 刻画和 operator Parseval，raw SHA256 为 `ed78ad4385cbfee447be03696f88b63775069eda174b0afb9970601ae2bbbf89`。R21 随后定位的 `20261026b-ZeroModeHardy/phase16-spectral-kernel/Part3ActualCuspSmoothEigenprofileFamily.lean:42,50,66,106` 亦已直接读：同一原 Hilbert 基有 smooth Gamma-invariant eigenprofiles、native PDE、原 carrier 的 L2 mass one 和先于 basis index 选取的 compact jet 常数。以上路径均位于 `.lake/proof-continuation/source-reviews/drafts/`；精确 imports、声明与 hashes 均加入 REGISTRY。其 headers 的 immutable `be3646/0f1f`、eigen-regularity transitive API HOLD 照留；这些既有证明不重写、不新计数学信用、不升级为 kernel 验证。

因此缺口应精确表述为：**该已有 full-cusp operator basis/光滑本征函数到 classical Whittaker-normalized Fourier realization 的关联，full continuous spectrum、归一化 trace 及所需经典估计尚未供应**，不能泛称“完整 cuspidal 基或光滑本征函数存在性尚缺”。native operator Parseval 本身亦不等同于所需 Fourier-coefficient A/J quadratic forms。

本轮实际新增的是原始行的 signed native Fourier 配对、共轭与有限 functional norm identity；实际消除的 **A、J、regular cumulative、ABL realnorm、cuspidal gap 或 Eq24 能量前提全部为 0**。新代码没有 goal-equivalent inequality premise。class II：上述必要来源转换已给完整 source body；class I：两处确定 namespace 修复已归档，整个依赖安装/验证仍未执行；class III：已有 operator 谱基/光滑 profiles 到 classical Whittaker-normalized Fourier/full-continuous/trace 的关联、经典谱估计和 ABL/continuous 真范数仍缺。

完整残余：D19 既有 actual full-cusp operator basis/光滑 profiles 的 classical Whittaker-normalized Fourier realization、full-continuous realization 与 actual normalized trace；D20 actual oldclass/full-fiber identity 及实范数；D21 A/J/regular/gap 真供应和 signed native coefficient 到 normalized R 的转换；D22 原全源 Eq24、零项/尾项、全部费用与共同 pre-N 阈值。保留 all cusps、`1/(4*pi)`、`dt/cosh(pi*t)`、t=0、k−1、level Cauchy 的 `sqrt(Z)`、一个 D、一次 `5*kappa`。P3.5.uniform_spectral 及 hLower/hUpper 等父目标均不能据此关闭。

元数据、源码声明、imports、原/修复映射与所有所列 raw hashes 在 `REGISTRY.json`。进行了源码静态 forbidden-token 检查与确定替换规则核对；这些不算 elaboration/kernel 检验。独审由 R30 另行记录，本报告不替代其裁定。
