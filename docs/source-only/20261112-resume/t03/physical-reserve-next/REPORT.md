# Y07 原 87 域、单素数 receiver 与最终矩形储备

**源码已把原 87 域的数值节省、实际前沿漏词权、编译费和正计数放在同一次选参上。物理带符号误差还剩可指认的两个算术和。** 第一个是最终矩形系数在完整模数区间 `⌊N^(9/20)⌋ < d < N^(599/1000)` 上的单素数误差。第二个是原双素数计数在同一系数上的高粗秩有限频带。前者是带中心删除的单素数 receiver，后者的外层质量是平滑双素数积。两者都保留真实的符号。五份 Lean 与两份原库安装补丁已冻结，等待同源远端内核检查。[原稿的带符号 PP 断言与系数条件](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-prime-product-insertion-assembly-20261009.txt#L15)

## 原始 receiver 的付款

对真实模数集 `Q` 和系数 `c`，`literal N Q c` 在原 `chenPrimeReceiverSource N` 的每个整数 `x` 上累加全部 `d ∈ Q, d ∣ x` 的 `c(d)`。先在同一完整模数重心化，得到原包含端点的 `π(N)·D(Q,c)`、`π(N;d,N)−π(N)/φ(d)` 和负号的中心素数项。对中心素数 `p∣N`，其每个取值来自真实非零整数 `N−p` 的约数。四以上的偶整数保证 `p<N`。原 `centreCoprimeDivisorBudget N / frozenHN N → 0` 支付这一项。生产库的 `singularSeries N = liuSingularSeries N` 给出 `singularNormalization N = frozenHN N = C_N N/log² N` 的精确等式。[生产库奇异级数等式](https://github.com/UyNewNas/goldbach-formalization/blob/3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9/ImbalancedChen/CurrentChenInitialSource.lean#L54) [原中心素数预算](https://github.com/UyNewNas/goldbach-formalization/blob/a023ae055d3d90738f6965a2848266aa13089faf/docs/source-only/20261111-full87-centre-frozen-hn/P4AOriginalFull87CentreFrozenHN.lean)

对 `d≤⌊N^(9/20)⌋` 的实际系数，原素数 Bombieri–Vinogradov 定理给出精确互素均值的绝对误差和。这里只用其固定三次对数节省，实际模数全部无平方因子、与 `N` 互素，且 `|c(d)|≤1`。从精确互素均值改为包含端点的 `π(N)/φ(d)`，原模数素因子的平方对数预算足以支付。指定任意 `u>0`，中心、低模数误差与均值修正合计至多 `u H_N`。对两个政策的差，各给 `u/2`，保留两个大模数带符号和之差后才取绝对值。这些结论对足够大的每个偶 `N` 成立。[原素数 BV 的固定 9/20 版本](https://github.com/UyNewNas/goldbach-formalization/blob/3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9/docs/source-only/20261102-resume-30k/upper_low_bv/P4BPositiveUpperPrimeBV.lean#L131) [原完整模数素因子修正](https://github.com/UyNewNas/goldbach-formalization/blob/3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9/ImbalancedChen/P5PrimeDivisorMeanCorrection.lean)

`exists_original_reserves` 在原档案历史上分别给出两个具体界。

- 原 raw 与 licensed 的差使用原 `eventPolicy true/false`。第五层单侧停止的每个活跃小筛因子满足完整模数界。第六层两个偶门均通过，真正的单侧子树为空。已审的两树在 `d≥N^.599` 的系数相等。结合低段与中心付款，余项是 `comparisonMiddle`。
- 档案的六层到八层节省使用 `sixthPolicy` 与 `policy (width r)`，并按原 87 个 `ownedSource` occurrence list 求和。对同一个已收状态，六层一侧 `beforeLeaves` 的真父级是 `actualParent`。八层一侧 `afterLeaves` 由该状态本身的 `retainedOwner` 和 `selectedCap` 读出原 `finiteCap`。各自每个完整叶的粗积小于 `N^(299/500)`。其符号所选的真实非零 `β±(a)` 给出 `a<N^ℓ`，`ℓ≤1/1000`。新 `same_coefficient_above` 直接对单点试验得出该增益系数在 `d≥N^.599` 为零，再由原带符号有限和付掉上段。剩余 `savingMiddle` 中仍是 `full87PhysicalRhoChange(d)` 的原符号。[原同一状态的两组真实叶](https://github.com/UyNewNas/goldbach-formalization/blob/a023ae055d3d90738f6965a2848266aa13089faf/docs/source-only/20261111-full87-owned-primitive-ledger/P4AOriginalFull87OwnedPrimitiveLedger.lean#L45) [原单侧提前停止及 .599 账](https://github.com/UyNewNas/goldbach-formalization/blob/5d1786aa/docs/source-only/20261112-resume/t03/p1-fixed599/P4AOriginalFull87Fixed599PhysicalRho.lean)

此历史终端直接消费原 `FilteredSourceSupply` 的已证存在式，依原次序固定 `s,r,e0`，再取 `e,q,om,n,m`。原三个几何漏量预算分别保留。其本身不识别两树在单个高模数上的公共系数值。最终矩形使用下节的独立选参，并直接在该矩形的原 `Q,ρ` 上重新应用同一已证的算术估计。

## 最终 B、扩大第五库与同一组 87 个数值

`original_archive_and_physical_reserves` 使用有限上区 bank、扩大第五库、完整有序第三根与原 R17 的四处比较。上下区树的共同第八次更新在高首坐标上逐词相同，所以同一上区 bank 在真实六层前驱和最终八层差中消去。原 `original_ordinary_source` 给出这个差的下界 `∑cellIntegral − η`。写入密度时用的是已认证的原 15–22 项

`G87 = (3111307568597708509491143 + 77410436074156865471 + 481322793305152847935)/2^96`。

其中 winner9 同域两次加量各出现一次。D8 连续积分保留八个坐标因子，实际算术前沿上的词权是 `∏ᵢ 1/(pᵢ−1)`。对全源逐词检查“进入实际最终前沿，并由其原 owner 接收”。检查失败时，既有定义在该词的素数权上乘 `1+profile`。原普通 `w=0` 和正预筛 `w=N^ω` 两个载体的真实漏量都在 `[0,η H_N)`，各自前沿 ramp 的原权重和都超过 `G87−η`。这笔漏量在数值下界和计数式中只作一次原源近似。[原 D8、三至七层因果承接与 87 个域](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-current-upper-density-assembly-20261009.txt#L204) [原数值及两次替换](https://github.com/UyNewNas/goldbach-formalization/blob/3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9/docs/source-only/20261110-yellow-closure-10t/t03_saved87_actual_gain/P4AOriginalFull87SavedGain.lean#L40) [最终前沿真实素数权](https://github.com/UyNewNas/goldbach-formalization/blob/1c0d8d194157d87a3e7e8ad0ca6a8ec87c9df6c2/docs/source-only/20261112-resume/t03/final-frontier-next/P1OriginalFinalEighthWeightedFrontier.lean#L132)

对 `1/2<b<1`，先在给定 `κ>0` 和上界下选 `κ₀>0`。给定 `K≥2`、三个各自正的精度，再依次取共同 `r,n,e,q,a` 与原 bank index `m`。在 `a` 之后，原 FinePPSchedule 一次选择 `β,k`，满足 `ω=νβ²<a`、`νβ<1/1000`、细网宽度及真实粗秩预算。所有来源的整数阈值取最大值，之后对每个足够大偶 `N` 成立。设 `S_N=C_N/log N`，`U=sixthRoot−G87·S_N−corrEight+(η+u_c)·S_N`。定理共同输出

- `(N/log N)·compilerExpense < u_c H_N`，`D(Q,ρ)<U`，以及同一矩形系数的真实非零支撑 `d<N^.599`。
- 在同一 `Q,ρ` 上，原单素数 receiver、`π(N)D(Q,ρ)` 与有符号中段的差的绝对值至多 `ηSharp H_N`。
- 对同一 `κ₀,K,N,ρ` 和每个 `ζ`，`RealB ≤ X_s·D(Q,ρ) + Re band(wholeHigh,ρ) + ηCount H_N`，也可把第一项的密度换为 `U`。真实外层质量 `X_s≥0` 且 `|X_s/(N/log N)−log(1/b)|<ηCount`。计数只使用一次 T05 已付的频尾与退化乘积成本。[原固定密度与编译两项储备](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-current-upper-density-assembly-20261009.txt#L373) [真实双素数剩余带](https://github.com/UyNewNas/goldbach-formalization/blob/3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9/docs/source-only/20261112-resume/t05/postmod-next/P4BOriginalHighRankPostModulusCount.lean)

## 剩余职责

原稿对 (PP) 要求同一真实 `ρ` 在每个充分大偶目标上有任意对数节省。当前单素数部分还需要对上列具体 `middle` 给出 `o(H_N)` 或更强的原 PP 估计。历史比较需要各自的 `comparisonMiddle` 与 `savingMiddle`。固定完整模数 9/20 是这次使用的已发表素数 BV 接口范围。最终正双素数计数仍需要同一 `ρ` 的高粗秩实部上界。T05 已付粗秩至二、全部完整模数小于 `N^(2/5)` 的部分和完整模数求和之后的 Fourier 尾，在保留带中继续承担 medium/no-medium 的分布估计。原稿把整个粗因子盒共同三分组、squarefree 碰撞及谱估计列入该解析输入；这次消零、普通素数 BV 和几何漏词权只能支付上文明确列出的部分。P1.4、Y07 的全部有符号 PP 和 Y08 远端 kernel 仍须分别验收。[原稿的高秩完整盒条件与近线性余类](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-current-upper-density-assembly-20261009.txt#L253) [PP 插入保留的解析前提](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/distribution-prime-product-completion-20261010.txt#L23)

T05 后续 `collision-next` 已在源码层把同一矩形的高粗秩频带化为三个独立的一界卷积，含实际小筛 `β`，并给出碰撞、中心与均值的任意正储备。该加强另行独审。它保留的算术频带与上文的单素数中段仍是两个不同估计。[T05 碰撞分解登记](../../t05/collision-next/REGISTRY.json)

## 安装选择

`ORIGINAL_APIS.patch` 逐一公开三个原证明。每项只删除七个 ASCII 字母 `private` 和一个空格。`ORIGINAL_MU_SCOPE.patch` 在本包实际调用的六个旧模块各加一行 `open VariableEnvelope (mu)`，使其中 `N^mu≤z` 的实指数固定为原 `25/128`。六者中的 `FrontierLeafCharge` 和 `FrontierInvoicesZero` 先取既有 `FIXED599_API.patch` 的后像。新 `OwnedGainSharpSupport` 也采用这个显式作用域。其余四份新数学源、旧补丁、原核算输入及原策略的字节不变。每个安装前像、后像及依赖关系均在登记中列出。[原 μ 的定义](https://github.com/UyNewNas/goldbach-formalization/blob/3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9/ImbalancedChen/VariableEnvelope.lean#L25)

T05 的双素数原接收链使用已发表 `postmod_stage/P4BOriginalHighRankPostModulusRow.lean`，SHA256 为 `ee04658e23badc8f9c6183b6a1a8936ed382f879dfddbf519caf3ec1a93961ab`。它只与本包调用的已选 `PostModulusCount` 及其既有依赖一起安装。本报告和登记记录逐字节来源及静态数学范围，整个依赖图的远端 elaboration、类型及公理审计仍待执行。[T05 的具体安装选择](https://github.com/UyNewNas/goldbach-formalization/blob/3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9/docs/source-only/20261112-resume/t05/postmod_stage/SELECTION.json)
