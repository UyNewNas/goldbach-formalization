# P2 原生 Wu 移动盒：共同前缀平滑预算

## 状态与范围

这是 2026-11-24 的三份独立源码，当前目录版本为 v5。Profile v4（SHA-256 `d35578d7a68d244cc2b2a9f04974716c2bb6b10de93a4986d541e102fd89c569`）与 DerivativeBudget v3（`168ee5b4a9f06906bb22bc54783d0017191ed249228377f73c467c209c3f5d7a`）现已通过私有环境的严格编译、独立内核重放和完整 owned 声明审计，两份 Lean 字节冻结。Profile 的严格编译任务为 `3bbe3efd1ebf4bbeb55d0a414556d5b7`（3.866 秒）；Budget 严格编译及五个轻模块的 replay/audit 任务为 `8eae22d6f9f4499f836f015b157af926`（Budget 编译 9.856 秒；整个任务 52.327 秒，报告峰值内存 2.24 GB，exit 0）。结果由根代理返回，完整证据由根代理另行导出。第三份 Theta 的 v1 字节保持不变，仍依赖原 W1 的较大 source-only 图，暂未安排编译。源码中的初稿状态注释随已接受字节保留；当前验证状态以本记录和精确收据为准。`SOURCE_MANIFEST.json` 记录逐源状态、精确哈希、版本变更、旧源位置、公开声明、固定手稿与上游版本，以及第三份文件所需的 P2 依赖主链。

本次五模块 replay 与完整声明审计结果：

| 模块 | owned 声明 | 状态 |
| --- | ---: | --- |
| `P4BSmoothGateUpperStep` | 18 | 通过 |
| `P4BSmoothStepDerivativeBudget` | 8 | 通过 |
| `P2WuJointWindowProfile` | 16 | 通过 |
| `P2WuPrefixLogProfile` | 24 | 通过 |
| `P2WuPrefixLogDerivativeBudget` | 22 | 通过 |
| **合计** | **88** | **通过** |

v2 仅修正表达：为比较符添加标准空格，打开 Profile 的 `ContDiff` 作用域，在乘积和光滑性步骤显式展开相应 profile 定义，并用自然数 cast 非负性推出 `2≤N+2`。所有定理签名和函数定义在忽略空白后与 v1 相同；没有增加假设、修改目标或调整常数。这批错误归类为形式化表达问题，未发现数学证明缺口。 v2 的实际任务 `b6e380…` 将 Profile 的剩余诊断缩小到两处加法顺序：目标为 `1+A≤1+B`，原项却生成 `A+1≤B+1`。v3 将这两处明确写成 `add_le_add le_rfl`；Budget 在该任务中仍未执行，其 v2 字节不变。 v3 私有任务 `3a63…` 仅剩两条 tactic lint：一处 `field_simp` 已关闭目标后的多余 `ring`，以及另一处单目标上的 `<;>`。v4 删除前者、将后者改为顺序执行 `field_simp` 和 `ring`，保持所有 lint 启用。

Budget v3 根据首次真实编译逐项修复：在固定 Mathlib `e4c91783…` 核对 `ContinuousLinearMap.iteratedFDeriv_comp_right` 与 `norm_iteratedFDeriv_mul_le` 的阶数条件后，显式使用 `WithTop.coe_le_coe.mpr le_top`；在目标里展开 `unitWindow`、`unitProfile` 再应用原乘积预算；采用当前 `neg_apply`、`smul_apply` 名称；删去编译器实际指出的两个未使用 simp 参数和一个多余 `ring`。Profile 与 Theta 均未修改，Budget 的定义、定理签名、常数与量词顺序保持不变，未关闭任何 lint。

这一步给真实移动前缀窗补上自给的定量平滑证明，并把该窗接回原 W1 计数及其自身 Θ 误差尺度。没有把 `testedFibreBalance` 改成假设，没有更换 K、Q、卷积重数、原素数槽位或加性素数检验。最终 P2 的 `testedFibreBalance ≤ ε Θ` 供应仍未闭合。

## 固定依据

手稿仓库 `UyNewNas/chen-imbalanced-semiprimes` 固定提交为 `a988cba584d803ae2856a0de50efb582f4f3dd6a`，采用 `paper/release-20261106/en/`。

- `argument.tex` 第 97–114 行的 `eq:current-PP`：原素数标签上的光滑几何权重、固定 polylog mixed Euler 预算、同一实际 ρ 的计数与精确互素均值。
- `argument.tex` 第 343–408 行：固定有限查询族取共同细化和有限个阈值最大值；`prop:current-positive-product` 的结论以 H_N 归一化，固定几何外逼近先取 N 极限。
- `coefficient-appendix.tex` 第 323–331、492–502、551–561 行：原始 PP 的任意对数精度、固定几何权重要求及完整 Fourier 范数预算。
- `sieve-appendix.tex` 第 763–792、1090–1101 行：坏 Γ5 与原长词的正乘积应用，以及固定正质量父节点下的有限查询和 Θ 归一化。

Wu 原生包固定为 `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`，目录为 `research/wu2008/src/MathlibNt/Wu2008DoubleSieve/`。核对了 `ImprovementFamilies.lean`、`BoxMassTheta.lean`、`BoxMassUpper.lean`、`BoxMassConvolution.lean`、`ReboxingParameterSource.lean`、`Gamma5GainGrid.lean`、`SecondFunctionalReciprocalGrid.lean` 和 `ConvolutionBV.lean` 的实际定义或结论。

## 原量词与已有可复用估计

`wuSourceBox k δ N i Δ V` 的实际条件是

\[
i\le k,\quad 1+\log^{-4}N\le\Delta<1+2\log^{-4}N,\quad
V\text{ 逆序},\quad N^{\delta^{k+1}}\le V_j,\quad
\Bigl(\prod_{\ell<j}V_\ell\Bigr)V_j^2\le N^{1/2-\delta}.
\]

实际第 j 个窗为 `[V_j/Δ,V_j)` 中的素数，并保留与 N 互素条件。原素数指数下界随固定 k、δ 变化，不能替换成所有盒子共享的数值 `1/90`。`BoxMassUpper.wu_primeWindow_reciprocal_mass_bounds` 给每窗一致的 `log(N)^(-5)` 量级上下界；`BoxMassTheta.wu_boxTheta_lower` 给

\[
\exists c>0\;\exists N_0\;\forall N\ge N_0\;\forall(i,\Delta,V)\text{ 合法},
\qquad \Theta_{N,Q}(W)\ge cN/\log(N)^{5k+2}.
\]

因此不存在本审查已证明的“大 N 空窗/Θ 太小”反例。原有 `P2WuProductInnerThetaPayment.uniform_collar_scale` 和 `P2WuJointWindowTheta.uniform_joint_prefix_error` 已用 `B=5*k+3`、`w=(log 2/log(N+2))^B` 将完整乘积截断及全部前缀上下端面支付到本盒 Θ。这里直接复用这些结果，不重做整数计数或 PNT。

源网格不能独自补 PP 量词：`Gamma5Gain_grid_sum` 是随 N、Δ 变化的微窗精确分拆；`reboxing_source_parameters` 给统一几何参数；`SecondFunctionalReciprocalGrid` 是固定连续积分网格。它们均未供应同 ρ 的 signed prime-product discrepancy。普通 `convolution_bombieri_vinogradov` 也不等于稿中该物理系数的增强分布估计。

## 三份新增源码实际做了什么

### `P2WuPrefixLogProfile`

定义 `s=w/(1+w)`，用两道真正的 `Real.smoothTransition` 对数门构造每个原窗的非负外逼近：

\[
G_s(\log x-\log L)\,G_s(\log V-\log x).
\]

`physicalProfile_one` 在原闭下端、严格上端窗内等于 1；`physicalProfile_le_original` 在正素数坐标上逐点不超过旧 `P2WuJointWindowProfile.profile`。因此这个对数窗位于已经计价的物理外领口内，既不扩张原来承担的误差，也不丢失原窗上的标签。

### `P2WuPrefixLogDerivativeBudget`

从现存 `P4BSmoothStepDerivativeBudget` 的真标量导数预算、Mathlib 的仿射链规则和有限乘积 Leibniz 界推出全 mixed logarithmic-chart tensor 界。

`profileFromLogs_tensor_budget` 的常数在所有端点和 `0<w≤1` 之前，损失为 `C/w^q`。`moving_physical_log_chart_budget` 进一步直接给原正素数乘法坐标图 `p_l exp(y_l)` 上的结论：

\[
\exists C\ge0\;\forall N,L,V,p>0,z,
\left\|D^q_y\Bigl[P_{L,V,w_N}(p\exp y)\Bigr]_{y=z}\right\|
\le C\log(N+2)^{Bq}.
\]

固定参数是前缀数、完整秩、槽位映射、B 和 q。C 不依赖 N、Δ、V 或素数基点。原生调用中 `i≤k`、`r≤R` 仅有有限多个秩与前缀包含映射，取有限最大值即可统一；本模块没有把这一步误写成对任意无界秩有一个常数。

这里的结论是真正全导数张量的范数，不是把所需预算重新声明为假设。没有宣称已完成旧 `Family.eulerWord` 语法字典，也没有宣称整个带 sharp carrier 的权重已获得 PP 许可。

### `P2WuPrefixLogTheta`

`jointLogWeight` 将上述剖面放在旧 W1 `(3,16/5)` 的同一完整标签载体上。`log_prefix_error_le_original` 按是否属于原 `indexedFamily` 分两种情况逐点比较 L1 误差：原族内两个剖面均为 1；原族外两个权重均非负，新权重不超过旧权重。

`uniform_log_prefix_error` 因此继承已有 `ε Θ` 付款，阈值位于所有合法盒子之前。`original_count_with_log_prefix_windows` 同时接回 W1 原加性素数计数与该 L1 比较。原计数和卷积标签的重数均未更换。

## 本地静态复核

- **不等号方向：** 新对数门必须不超过旧物理门，同时在原窗上等于 1。下端由 `log(x/L)≤x/L-1` 得到；上端分别处理 `x≤V`、`V<x≤V(1+w)`、`x>V(1+w)`。第三种情况新门为零。
- **重数与槽位：** 所有乘积仍逐 `Fin i` 槽位计算；没有按素数值去重。导数模块甚至不假设 slot 单射，实际 W1 采用旧的 `Fin.castLE` 前缀包含。相同素数值出现在不同槽位时仍是不同标签。
- **宽度：** 使用的 `w_N` 与旧 `P5Z.ActualSingletonLogCollarFamily.logWidth` 的定义逐字相同；`s^{-1}=(1+w)/w≤2/w` 给共同阶数预算。
- **量词：** 源码先选择 C，再变化 N、端点、基点与图坐标；宽度在更早的 `C/w^q` 结论中也可自由变化。Θ 模块的 T 在全部 BoxIndex 之前。
- **计数：** 计数恢复依靠原族上的精确值 1 及同一载体上的非负加权包含，不从“旧计数上界较大”错误推导较小上界。
- **未混淆许可：** 正坐标图的导数结论不等于全实域光滑延拓，prefix 因子的导数结论不等于 `jointLogWeight` 中全部 sharp carrier 的光滑性。
- **状态：** Profile v4 与 Budget v3 已通过严格编译、独立内核重放和完整 owned 声明审计；Theta 未编译，未获得内核重放信用。本目录没有 `sorry`、`native_decide`、新增公理或假定的 PP 实例。

## 仍需供应的精确解析结论

原终点仍是 `P2OriginalSeedPositiveBalances.testedFibreBalance` 在所有原生合法盒子上 `≤ε*boxTheta`，其中 Q 固定为 `N^(1/2-δ)`、σ 是实际 `convolutionCoeff`、K 固定为 `681/100`，包括坏 Γ5 和 Γ9…21 的原始列表出现次数及可能末尾单位。

更底层缺少的是：对该完整 seed 家族的真实、已许可平滑完整原素数权重及同一实际 ρ，证明 `Part3.UniformPrimeProductTarget` 的实际实例，即

\[
\forall A>0\;\exists C>0\;\exists N_0\;\forall N\ge N_0,\ 2\mid N\;
\forall b\text{ 合法},\qquad
|\operatorname{primeProductSignedError}_{\rho_N}(W_{N,b})|
\le C N/\log(N)^A.
\]

`W_{N,b}` 这里指待完成许可的**实际**全词权重，不是新增的自由权重参数或可任意假定的实例。当前 W1 的原 `carrier` 仍含其余 sharp 几何门与 prime/coprime mask；完整 seed 的所有词、坏 Γ5、单位面和同 ρ 密度/互素修正也尚未由本目录处理。

原 `H430ClassicalSmoothNativeFamily.family` 已为 Γ9…21 固定钳位单前缀族写出 `Family 200`，应复用其 Gate/Euler/occurrence 会计，但它固定 `aStar=1/90` 和外部单素数区间 `[clampStart,1/3)`，不能直接替代任意 k、δ、多素数前缀的 Wu 全盒。

一旦获得实际权重序列的原稿 raw PP 及其余原误差付款，取 `A>5k+2`，除以已有 Θ 下界即可使 signed PP/Θ 一致趋零。若原稿只给每个允许的 N-依赖序列一个常数，可对违反统一盒阈值的盒子作对角选择；这要求先证明任意所选盒子序列都在同一个共同 seminorm 包络下被允许。固定有限父节点的 limsup/H_N 本身没有提供这条事实。

分类：前缀移动端点和 logarithmic 宽度预算是本目录已补齐并经严格编译、独立内核重放及声明审计的稿内省略推导；完整实际权重的许可与同 ρ 分布供应仍是实质未完成输入。没有证明原生目标为假，也没有给出或暗示一个已成立的反例。

## 依赖恢复边界

前两份只需 main 中既有的 `P4BSmoothGateUpperStep`、`P2WuJointWindowProfile`、`P4BSmoothStepDerivativeBudget` 及 Mathlib。第三份的 P2 主链见 manifest。其两件 `P2WuOriginalWindowUpper*` 必须选 y03 的 `selected-api` 字节：它们只将三个已有 helper 公开，原 resume 字节仍是 private，不能混用。

该大图继续进入旧 P5 链。已登记但尚未定位的 `P5AllWordAmbientOccurrenceBound` 原 SHA-256 是 `62e92b727855055890fa2bf7953fb490b6b589fe0abe168bb59c26ccd65577cb`。本地既有 R03 记录以及本次私有 `/workspace` 只读搜索均没有给出原字节。这里不重造这项已有工作，也不把第三份标成依赖齐备。

### 2026-11-24：修正一项既有源码定位

`P5SmoothChartHBDyadicPartition` 的原字节已经在仓库中；早先 Θ 覆盖表将其列为缺失，是选源 locator 遗漏。应直接复用现存文件：

`docs/verification/20261123-blue-compilation/reindex-isolated/postimages/ImbalancedChen/P5SmoothChartHBDyadicPartition.lean`

文件为 **7,137 bytes**，SHA-256 为 `75526601e62d131bf00f850725ee2ad9de2b34a0bd5baa57ab3147893ad69bec`，Git blob 为 `0388da3ca698b8f5057321622c8b0a875ed1c640`。上述路径在提交 `8657cfffef159185f73c6a04ae4d31c846c0d0a9`、`228ee511f27ad2d12450b431ba5a1acdc0b5ac9d` 以及本次核对的 `0f87651d2f27a6de1900b717b8703f2c6cbcb0ae` 中均指向该 blob；原 frozen 路径在 `fa22a56829ee880404516a36d498ce27dcb32f92` 中也保存同一字节。两个 locator 和逐提交核对记录已写入 `THETA_DEPENDENCY_COVERAGE.json` 与 `SOURCE_MANIFEST.json`，没有复制或重写 Lean 文件。

其唯一 import 是 `ImbalancedChen.P5ActualHBMediumBranchPartition`，该依赖已在覆盖表中，故本次只将一个模块从 missing 移到 selected：**project sources 154 → 155，missing 5 → 4，未包含在原 owner census 的 selected sources 85 → 86**。原 native 图、candidate payload 和所有编译/重放信用保持原值。这里仅取得精确源码；这次定位核对没有编译或重放该模块，Θ 仍未依赖齐备、未编译、未获内核信用。

其余三件精确登记源码的新增检索结果如下；所列 SHA 是历史登记值，未取得对应原字节。

| 模块 | 原 SHA-256 | 本次结果 |
| --- | --- | --- |
| `P5ActualFourNativeBoxFullNorm` | `14a9460c6293c36f2d440ba40ff77270c054a82866c79621cf3d0783c2c2ea26` | 未取得原源码 |
| `P5OriginalFourSelectedSmoothWBindingGap` | `1c01707b23972d7d414b1fa7cc48789b9322745082ccb29f10e6d9e065170ed6` | 未取得原源码 |
| `P5PositiveFourProfileLocalZeroSmooth` | `2f7a00ab145de53b4d17353e93089c906170adc6374b1b364b5bdc8e941630cb` | 未取得原源码 |

新增远端范围固定为 `codex/p1-final-acceptance-20261124` 的 `29611f07998553148f245986d35c96d6f2ad8a31` 和 `codex/p3-continuation-20261124` 的 `ef1479c272bdd6b24800fa10409d793f0a2fe95c`。分别读取三件 active 路径和四个原登记 archive 路径，共 14 次精确路径请求均返回 404。对应 compare 返回的 300 / 219 个文件中未见这三件文件名；P1 的 300 个返回项存在截断风险，不能据此声称全分支所有路径均不存在。完整固定路径清单、历史 registry 和限制见 manifest 的 `theta_dependency_source_recovery`。

现有本地精确文件名清单及可用的六个提交历史也未给出另外三件原字节；没有扩展为完整远端历史扫描。手稿仓库所见 `master` / `release/20261106-aixiv` 仍是既有版本，未发现新的手稿归档分支供增量检索。本轮没有重复搜索 `P5AllWordAmbientOccurrenceBound`，没有为四项未取得的源码重造证明，也不把来源缺失判定为数学反例或已证明的实质缺口。
