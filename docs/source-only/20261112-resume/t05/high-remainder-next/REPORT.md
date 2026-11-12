# 同一物理系数的全秩小模数、全母傅里叶恢复和高中首坐标

十个选定模块含一个同名 API 替换。它们是静态源码候选，尚待 Lean 内核验收。原有九源包 78ae6ad1 和 71b47b30 的物理系数继续作为依赖。新增数值档案为零。

## 原两表的带符号余项

用 D(S) 表示原两个标记素数在 S 上的真实同余算子减精确互素均值，权重含四个物理门和原额外整乘积截断。H(S) 是原 chartBank N 2 上所有 mediumAtlas 与 noMediumAtlas 的带符号联合和。S 始终是原 Q 的子集，c 始终是同一有限高区回退、完整有序第三层和新旧第五层并集的矩形系数，ω=νβ²、ell=νβ，τ 用共同 k 对齐。

* `eventually_remove_bounded` 对任意 U⊆Q、U 中所有 d<N^(2/5)，在同一原 Q,c 上给 ‖D(Q)−H(Q∖U)‖≤δN/log(N)^A。每个 d 的正性与目标互素从整个原 Q 的 squarefree/coprime 投影取得，绝对系数界逐 d 来自 rho_abs_le_one。原导子定理、真实五门变差和正包络的绝对 φ 费用沿用 78ae6ad1。
* `eventually_height_and_wholeHigh` 给上述尖锐高度余集以及 Q∖activeLow 上的同一结论，并将两组 H 直接相减付至 δN/log(N)^A。高度余集每个非零真实小/粗分解同时满足 d_total≥N^(.4) 和粗秩≥3。进入原三个卷积分组时采用 wholeHigh。乘积的硬高度测试已在差额中支付。
* 原 medium/no-medium 的恢复使用同一原系数的 .599 支撑、同一互素均值和已付真幂。所有这些余式都对 A 和 δ 先取共同 N 阈值，再给任意合法 s。分开两张表取绝对值的估计仍待证明。

## 真实母项与直接正计数

`eventually_atlas_eq_modes` 对全部实际 js 与两个原 HB 组给 H(S)=完整频率积分。它直接使用原独立原组对数、光滑 η、ψ、每个有序整数 HB 坐标、原 HB 标量、全同余和互素算子。源接口先在真实头部支撑许可下恢复单个原 js，再求原 chartBank 全和。

`exists_mother_mass` 对全部合法 s 给真实原母 Fourier 振幅的总 L¹ 上界 C·logScale(countingScale N)^14/s^24。14 来自两个原组尺度及最多十二个原 HB 坐标，24 来自原物理门、η、两组 ψ 和平台的混合导数。这些步骤复用 Nov10 T06 的原母/精细子图和 T01 的 15 源 owner-fibre 审查所对应的既有微分与傅里叶原件。共同预定 m(N)=⌊log N⌋，实际 s(N)=1/(m(N)+1) 后，`exists_scheduled_mass` 的母振幅总支出至多 C(log N)^38。

`eventually_RealB_le_high_modes` 对充分大偶数 N 给真正 RealB≤X_s·physicalDensitySum(Q,c)+Re(modes(wholeHigh,c))+ηH_N，且 X_s≥0、X_s/(N/log N) 距 log(1/b) 小于 η。目标的原 signed kernel、原 β,k 和支撑都保留；同系数的 hdensity/K 与 .599 指数可由已发布 FineDensity 输入。此端点直接在单一预定宽度律上工作。Part3 UniformPrimeProductTarget 的全族指标在 N 后：当指标是 Unit 时可固定预定权函数，若包含所有任意快的分辨率，单一 m(N) 的 38 次幂账不能供给那个加强前提。原 RealUpperCountingAssembly 则要求每个正精度之后充分大偶 N。这里提供直接同系数正计数，让剩余频率和显式出现。

## 原 medium 整盒的实际尺度

原稿 completion §2 的局部 x 是选中的 HB 槽长度乘全部互补整数的区间长度。原 (S) 的 beforeHBCutoff 在 HB 前从两母尺度构造；原 §4 的 firstMedium 在看整数、模数或误差前从整个块向量的原顺序选择。

* `live_geometry` 由真实非零 integerProfile、整乘积 η 和两原 ψ 逐项推出 N^(1−κ₀)/4≤x≤exp(1)N，原母尺度积 X≤16x 且 x≤4X。Half-open 的单位块和值相等的不同 HB 位置全保留。
* `eventually_live_medium` 接原 firstMedium 的真实窗 X^(3ζ)≤U≤X^(1/3+ζ/4)，统一推出 x^(2ζ)≤U≤x^(1/3+ζ/2)、f(x)≤Zchart≤x^(2/(loglog x)^3)、x^(1−ζ)≤N≤x^(1+κ)。原 lower moving residue 常数 exp(−1) 由上面的 x≤exp(1)N 给出。需要 κ₀<κ/(4(1+κ))，0<ζ≤1/400。对于 71b 的四数字 M 条件用 0<κ≤ζ/10000。
* `partition` 先用原 HB 矩形和自然数上界 ⌊countingScale N⌋ 的 dyadic bank，将全部互补整数积按唯一右闭 dyadic 标签分开。它对任意原矩形上的复值逐项成立。互补整数积等于删除选中坐标的实际整数连乘，从而该标签独立于被选头坐标。在固定整块和互补标签后，所有点有同一 x；整母的一个非零物理整数点给整母全部点的计数上界。所有频率和同一 Q,c 复用这份划分。在使用这一额外划分的估计中，`exists_scheduled_split_mass` 计入最多一个额外对数，给 C(log N)^39。
* `active_word` 用真实 attached 乘积分解、原小/粗支持、两符号 β 和原细标签的 canonical pick，证明 wholeHigh 上每个真实非零系数的代表至少有三个粗素数。原 raw 代表、ALL/ANY 细标签以及原模数 d 的算子各自保留。`eventually_high_heads` 在代表首粗素数对数 > μ 的原子上，把上面的实际 x,U,N 投入 71b 的真三个 endpoints，推出四条 (M) 数值不等式，第三条保留真实目标 N^(7/32)。这个数值界与分析的绝对 7/32 谱估计属不同命题。

每个互补标签须独立处理。`fibre_integral` 对原模数和与精确互素均值先做有限 Fubini，再对每个实际整数应用原母的 Fourier 反演。`dead_fibre_integral` 给整纤维无真实非零源点时的完整频率积分为零。`eventually_fixed_live_window` 从已占用纤维的一个真实整数给该固定 U、互补标签和 x 的 (S)；同一纤维里原权为零的其余整数也使用相同尺度。单个频率在空源纤维上仍可有带符号贡献。

## 准确的实付边界

1. 在同一 wholeHigh 的原物理代表首粗坐标≤μ 情况，仍须把真实 lower 分支每个细原子的选槽、剩余槽平方门及原幅度恢复费接入 (T)/(M)。71b 的低粗秩 0、1、2 已在 BV 用过。T03 fecfaff4 的原 87 域第六 winner/完整第八覆写给相应实际 reads，未给所有低首任意粗秩原子的统一余槽平方许可。
2. 在两类首坐标，仍要对真实原矩形系数给全体分组标量及绝对总恢复，实施同一 γ₁*γ₂*γ₃ 的 (T)、一有界 β 及全局碰撞 (C)，包括整乘积=N。要为原 medium 用原粗 1/μ/log 角色、区间与固定频段接 §5 auxiliary SW 和真正 uniform signed local M；noMedium 的真一/两长槽 Brun、删去模数素因子的损失和精确互素均值仍要接此同一 c。局部完整支撑的实际 .599 和 moving-residue 指数还需按参数按组落实。T04 的 zero-Gram 子项没有供全绝对 7/32。
3. 已列的 38、39 是真实全振幅的费用。依赖的旧完整模数截频 `exists_actual_upper_postmodulus_tail` 的签名固定的是旧 attachedUpperCoefficient。它的通用 `actual_hb_mass_polylog`、`discrepancy_tail_le` 和 `exists_uniform_exact_product_payment` 可接矩形 c 的 .599、平方自由、逐模 abs≤1；本包的 Fourier/RealB 等式使用完整积分，没有用旧 attached 的截频结论当作新 c 的实付。完整 PP 及最终 1+1.7482 仍待真剩余算术。
4. 稿 §1–5、§10 的原数学路线提供了上述完整源、尺度与原 W 的来源。新的全秩小模数重用属于确切的证明提出/接线。尚余的低首许可、完成全模数的有限截频及原子卷积接线是形式化的具体缺项；已检查的原稿与当前 Lean 读数没有证明该解析主命题错误。

## 安装

安装时选择 api/P4BOriginalRankTwoGlobalPayment.lean 的新 SHA；同目录的 unified diff 为可逆核对资料。三个旧 public theorem 的完整命题逐字一致；两个旧结论作为有界类别新 API 的实际细分支继续可用。现有 HigherRemainder 以及同名实例的所有下游需在同一选择上重新 elaboration。原 78ae6ad1 的九源封件可原样重现。

登记表列出真实源码、选版、直接导入和原稿的 SHA256。所做核验为静态阅读、源文件哈希及 public 声明文本比对；未执行 Lean、Lake、LSP、guard、当地运行或 CI。
