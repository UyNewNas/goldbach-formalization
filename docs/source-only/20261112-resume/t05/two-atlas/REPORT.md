# 原两张 HB 分支表在小模数上的实付估计

五份 Lean 源候选，源级静态核对。数值输入为零。原 11 月 10 日光滑计数、11 月 12 日乘积截断及真幂包均沿用冻结字节。真幂直接依赖选用 T09 审过的 `proper_stage/P4BOriginalFiniteProperPayment.lean`。

## 物理结论

令 $Q_0=\{d\in Q:d\le N^{1/5}\}$，$Q_1=Q\setminus Q_0$。这里 Q 是最终有限高区回退、完整有序第三层、旧加新第五层的原矩形模数集，`coefficient m r n e q a omega k N level` 是同一矩形上的实际带符号系数。令 $D(S)$ 为同余项减原互素均值的 `Part3.primeProductSignedError`，测试取原两素数权 $V_s=\eta(p_1p_2/N^{1-\kappa_0})W_s$。令 $H(S)$ 为在 S 和这一系数上把原 `mediumAtlas + noMediumAtlas` 对所有 `chartBank N 2` 标签求和。两项共用物理矩形、每个 HB 行和每个原标签。选择支撑的操作只发生在最外层模数求和。

`P4BOriginalTwoAtlasSmallPayment.eventually_two_atlas_small_and_remainder` 给出任意自然数 A、任意 `delta>0` 的两个同时结论。

```text
‖H(Q₀)‖           ≤ delta N / log(N)^A
‖D(Q) − H(Q₁)‖    ≤ delta N / log(N)^A.
```

取固定 `K≥2,b>0,κ>0` 后，N 阈值先于每个合法外宽 `0<s, 2s≤baseline b κ−19/96`、全套粗政策、β 和对齐细宽。输入的唯一物理范围是实际 `ρ(d)≠0 ⇒ d<N^(599/1000)`。T01 的 `exists_fine_same_rho_hdensity` 与 T02 的单 β/k 调度已经同见证地提供该式，故不需为本估计重新选择 `omega=nu*beta², level=N^(nu*beta)` 或 k。第二式是供原物理计数使用的余项界。第一式独立说明已经支付的小模数分支和，连接计数时只用第二式。

`actual_small_prime_sum` 给 $D(Q_0)$ 本身任意对数精度，甚至只要求 `0<s≤1`，无需全支撑指数。`rank_zero_one_in_small` 从实际正负 β 的同一非零分解推出所有粗秩 0、1 模数都在 $Q_0$。严格指数余量来自 `ell<1/1000` 和粗素数小于 $N^{19/96}$。其他秩在此按完整自然模数的大小入选。

## 算术来源

1. 原两素数有序词按较小素数 p 归属。正向用 $p\le j$，反向用 $p<j$，因此平方与所有重复标签精确计入。固定 p 后的真权由四个原物理仿射门、原完全乘积截断和归属门相乘。每个门在自由坐标上单调或反单调且取值在 [0,1]。乘积离散变差至多 6，末点的 Abel 系数至多 1。有限前缀系数的总绝对值至多 7，此数与 s、p、N 均无关。
2. 原轮廓非零推出 $pj<\exp(s)N$。固定 p 的自由素数前缀取 $X_p=\min(N,\lceil eN/p\rceil)$。原外部载体满足 $p^2\le eN$，故 $X_p\ge\sqrt N$，且 $d\le N^{1/5}\le X_p^{9/20}$。所有 p 的实际长度总和至多 $2eN(1+\log N)$。两方向各自使用原 `P4BPositiveUpperPrimeBV.eventually_profile_log_saving` 在 $X_p$ 的结论，先取精度 A+2，后一次求和。其源调用已钉住的 `Bombieri1965Richert418.standardBombieriVinogradov`。
3. 原 `U9SemiprimeSwitch.product_AP_iff` 及 `residue_coprime` 在 $(p,d)=1$ 时给 $N p^{-1}\bmod d$ 的实际原始剩余类，非单位 p 的同余计数和互素均值均为零。Q 的正性、平方自由、与 N 互素以及 $|\rho|\le1$ 由实际矩形附件直接提供。
4. 已有真幂总估计只在完整 Q 上陈述。限制签名和的子集时，子集的绝对值可能增加。`eventually_subset_proper` 直接使用已付 `exists_row_costs` 的子集统一界、`eventually_active_count` 及原 `fullCollisionWords_card_le`。原 $x=N$ 位置仍以真实非零模数数目和 $\tau(N)^2$ 支付，其他位置用原非零距离除数界。两个原 atlas、互素均值及真幂负号在 `eventually_subset_atlases` 恢复。原未展开源对 $Q_0,Q_1$ 逐项相加恰为 $D(Q)$，从而第二个物理结论只用一个 `delta`。

## §§2–4 的源码接口和余下的数学

手稿固定为 `chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`。补篇 §2 运行两个独立原 dyadic 素数标签和每组的 order-three HB，§3 处理在同一粗词上分组三个归一卷积、正负小素数 β、原全局粗平方自由和恢复标量，§4 按原长度窗选择第一个 medium slot，并在所有原标签后支付 Fourier 截断。原码 `mediumValue` 在 `firstMedium ... = none` 时为零，`typeIValue` 在这一情形恰取原行。二者是同一 `atlasEval` 的互补选择。上面的小模数界支付它们的**带符号和**。并无对两个分支各自绝对值的估计。

- **余下低粗秩的导子估计已有真供应。** 原补篇 §10 和 `low-rank-convolution-bv-20261010.txt` 给出正长度两因子、双侧诱导字符互素掩码及大、小导子分解。实际 `P2GammaPrimeLocalConductorSaving.exists_actual_prime_local_conductor_saving` 已提供这一局部估计。它接受真实单素数区间、可微复值头轮廓及其 Abel 范数、互补行的 L¹、两行 L²、`M*N=x`、双正幂长度和 `Q≤x^(1/2−epsilon)`；其阈值先于全部实际行。自然同余减精确互素均值到字符矩形的字典在 `P2GammaSmallConductorIntervalBridge.naturalRectangleDiscrepancy_eq_character`。目标素因子删除是头轮廓内部的显式参数。该估计允许任意 `z : (q : ℕ) → ZMod q`，因此在原两素数并未删除 N 的素因子时，可取删除参数 1、真实余类仍取 `(N:ZMod q)⁻¹`。实际剩余粗秩 2 模数由 T02 控制在 $N^{2/5}$ 内。下一步是把此 $V_s$ 展为符合导子定理的具体可分离素数矩形，核定它们的占用尺度、真实 L²/L¹/Abel 范数、端点和总恢复费用，再以更强精度求和。两素数局部导子定理本身可直接复用。
- **现成 Γ 终端的具体范围。** 分支 `chatgpt/p3-retained-same-rho-20261103@0632f2e1839bbdba1604c546bbc3be46b7536d47` 在真实 mother 非空词、`headCarrier × rootComplementLabels` 和旧 `rankRho ... 2` 上消费上述导子供应，保留空词及外层 `selectorMass`。这些标签和系数与当前 $V_s,Q,\rho$ 分别定义。`Wu2008DoubleSieve.convolution_bombieri_vinogradov` 中卷积出现于模数权，算术源仍为一素数的 `primeAPError`。
- **medium。** 原 §1 的 M 接受一个含真实粗糙筛和扭曲的单个 HB 槽、固定除子幂界的互补序列以及三个各自一有界的粗卷积。T01/T02 的 `HighAtoms` 已在真实代表的最大粗坐标 $>\mu$ 时给出同一完整标签词、whole-box 分组和四个 M 尺度不等式。T04 的低首坐标端另有选中前缀、实际祖先、末奇秩和平方门。还需把所有未付的矩形词及低首坐标各赢家的标量、重复标签阶乘、小因子 β 和粗平方校正接到真实 M 原子总和。`Part3OriginalS123CombinedArithmeticPayment` 的 S1、S2 和 S3 有具体原核支付，末端仍有物理留存 Poisson 模式、其他余项及原谱返回。原稿另文 `distribution-medium-completion-20261010.txt` 的 E2 谱段需要实际原规范、物理包和绝对谱估计。它们是独立形式数学供应。
- **no medium。** 在有效双原组的正支撑上，§4 给每组至少一长槽，且整个乘积至多容许两长槽；因此在原尺度和 ζ 裕量核定后，该秩二情形为两长槽。`Part3.TwoLongHBMellinBrunProfiles.finite_sameRho_mellinBrun` 已处理三种真实 Brun Mellin 光滑核及同一个 Q/ρ。它的结论仍带 `pairCost × ∑‖c_d‖‖alpha_d‖ × ∑‖rho_q‖ modulusBudget(q)`，前提 `CompositeWeilInput` 是原 Kloosterman 和的合数 Weil 平方根界。原总计内还要绑定这些核到实际 HB 行、补齐尖端与互素精确均值、原粗糙剩余和全部标量。已检查的 `eventually_actual_lower_core_paid` 使用另一条 lower 系数。原 `kloosterman_norm_le_totient` 的平凡界未供 Weil 平方根尺度。
- **几何和恢复费用。** 当前秩二上界的 `P4BArbitraryWidthUpperPairProfile.licence`、`mixed_width_budget` 及 T06 的 `exists_refinedUpper_fourier_width_budget` 确有具体 $W_s$ 和至多 12 个 HB 变量，每图的 $D\le C/s^{24}$，总积分 Fourier 范数至多 $C/(2^j s^{24})$。原 `P4BOriginalUpperFourierTailPaid.sourceScalarMass_le` 给出两组标签及 HB 标量总和 `49*dyadicConstant^14*logScale(countingScale N)^14`。该源的最终模数后截尾命题固定旧 `attachedUpperCoefficient`。T01 的 grouped 检查已核 ψ 原分组全阶、复化和 RefinedChart 消费。T06 的 `exists_chosen_actual_amplitude_mass` 在另六个 U7/8/9 来源及其已截断外频率上给出实际振幅界。带真实祖先和外层积分的其他调用须满足各自 `Family.ambient/support/finitePrimeSupport/mixedEuler` 或相应单源接口。尚须在剩余 $Q_1$ 的同一 ρ 下把全部实际恢复标量、频率积分、细分数与原算术截尾相乘并付清。若 s 随 N 变化，还须保留 $s^{-24}$ 与实际分辨率的增长关系。本包内的小模数估计对每个合法 s 一致。

最小未付总命题是上述真实 $H(Q_1)$ 在选定的固定参数、合法外宽及实际同一矩形上对每个 A 为 $O_A(N/\log^A N)$，阈值适用于之后所有足够大偶数 N。若用于变宽族，须保留相应可核的增长预算。精确字典、Abel 局部化和子集真幂属于稿内可补的连接。剩余卷积的主要算术能够复用，真实行、源和总量的绑定仍需证明。一般 medium 谱返回与两长分支的真实整账各有上述实质形式义务。现有调查没有发现这两处原稿的数学反例。完整 PP 和最终 K/RealB 计数依然等待这些项及全链核验。

本轮只读取原文、数学源码和固定 Git 对象并核对源字节。未执行 Lean、Lake、LSP、guard、CI 或数值证明。
