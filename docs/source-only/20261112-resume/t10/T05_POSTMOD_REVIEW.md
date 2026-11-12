# T05 完整模数和后的 Fourier 截频独审

审查结论为五个数学模块的限定源码通过。原稿依据为 9731290e 的 distribution-prime-product-completion §§1–5、§10，特别是第165–175行要求先形成原完整模数和、单独处理积等于目标的纤维、共同选取对数频带，再选原 medium 坐标。这里的通过仅覆盖这一截频费用及下述局部指数转换。尚无本组选本的 Lean 编译、kernel replay 或全声明公理收据。

## 原对象与量词

1. 原系数是有限回退策略的真实矩形系数 c，同一个 N、m,r,n,e,q,a、β、k、ω=νβ²、ℓ=νβ 贯穿物理密度和剩余高模数项。对任意 S⊆Q，每个 retained 子项都把同一个 S 与同一个 c 送进 exactDiscrepancy。终端只把 S 具体化为原 wholeHigh，高低分割在旧版的完整 Q 里进行。全组支撑 d<N^(599/1000) 仍作为逐 c 的显式前件；Fine 的存在性调用须选同一 β,k。
2. 真实整数轮廓的一点非零足以约束该互补格的 x=U·lower(C)。由 exp(−1)x≤N≤x^(1+κ)，在 0<ζ≤1/400、0<κ≤ζ/10000 和 κ₀<κ/[4(1+κ)] 下有 d<x^(1199/2000)。两个严格的 Type I 指数是 20ζ+1199/2000<1 和 40ζ+3(1199/2000)/2<1。该数值转换适用任意选定坐标的占用互补格；无 medium 的计数终端仍保留完整母格，后续实作须给具体一长或两长分派。给定 1/2<b<1、κ>0 和余量上限，可在 N 之前选固定正 κ₀，同时满足上述裕量及 19/96<baseline(b,κ₀)。纯计数终端允许每个 ζ，使用局部许可时须另满足已述范围。
3. 正规物理输入是 completeProduct 对 N 的同余项和原精确的互素均值。零系数过滤同时作用两项。q=1 的原核恒零。generic fullTailMass 分别计算非零差乘积矩、积恰为 N 的整纤维与原均值质量。在 D=⌊N^0.599⌋、h=u+v≤12 时，旧 actual_hb_mass_polylog 给出的中心项是 Dτ(N)^h。与 kStar=2、θ=0.599 的已证明 exists_uniform_exact_product_payment 相接后为 O(N)，避免了 τ(0)。这里全额保存了同一积的多重整数表示。该费用只用于 Fourier 尾，跨组相同素数的 (C) 仍是另外的算术账。
4. 预定 m(N)=⌊log N⌋、s(N)=1/(m(N)+1)，令 L=logScale(countingScale N)、F=paymentExponent 12 0。所有标签、模数、HB 阶、β、k 和整数子行共享 H=L^(A+15+24+F+3)。固定 A 后，当 κ≤1 且 N≤x^(1+κ) 时，保留频率在每个坐标都满足 |ξᵢ|≤(log x)^(bandwidthOrder(A)+1)，大 N 阈值位于实际 x、维数及频率之前。Gaussian 或离散频率采样均未进入原公式，保留项是有界连续立方体上的 Lebesgue 积分。
5. 真实混合导数的 s^−24 与完整模数矩先给单行误差 C N/L^(A+15+3)。对 medium 纤维，先用原 firstMedium 选第一合法坐标，再用完整互补整数积所属的右闭 dyadic 块分割；首个坐标存在时其下标严格小于行长。非零性只对频率变换前的原整数几何权判定。死纤维原整数和严格为零，其 Fourier 积分的值可由全域反演读回；单个频率没有被断言为零。无 medium 的母格直接采用同一 H。补格数付一对数幂，两原群的 chartBank、HB 阶、真实标量和有序块付十四幂，恢复整体 C N/L^(A+3)。这一步未积算频带的体积。
6. 终端选择 A=0，对充分大偶数 N 给出 RealB≤X_s·physicalDensitySum(Q,c)+Re(band(wholeHigh,c))+ηH_N，且 X_s≥0，X_s/(N/log N) 距 log(1/b) 小于 η。仍欠对该真实有限带的绝对算术估计，包括低首槽、辅助 SW、分组碰撞与阶乘、medium 的完整绝对谱 7/32，以及无 medium 的一长/两长与精确均值。完整 PP、原 hUpper 和最终主定理均保留原状态。

## 形式接口及发表选择

原始 Row 的 truncated_eq_band 内点等式（第115行）处理 ℝ 标量作用于 ℂ。在当行 simp only 中显式采用 Complex.real_smul，随后可将同一相位和归一化作为复乘表达式重排。已独立确认 stage 源相对于原始源只有这一次 18 字节插入，正向和逆向均逐字吻合，声明、原频带、幅度、相位、积分及 1/(2π)^h 全部相同。此项是静态可见的 elaboration 风险修正；没有实际编译失败或成功结论。未来安装单选所列 postimage，Fibres 和 Count 都依赖这个选择。

原作者 REGISTRY 是 36ef1a41b542359b891c31cf942ea3b02a68347c022b0e3b8ef54b7bfe734558。REPORT 是 cf12f9d701037b3818547e02d2eb9694c3589e40778a21267c72d6238bf05ea5。选源表是 5a6a9880980d852b132363dc29695d89048046c3dce8ec07c9ee0e07c7b255c6，原 Row 为 d0d4f557bf4eddf7b0b17c770a00e44038dd653203d284c862ecbbe3f71c7154，stage Row 为 ee04658e23badc8f9c6183b6a1a8936ed382f879dfddbf519caf3ec1a93961ab，补丁为 ac1252a2f26e71e4f6caa9acd3a31971946558bbe6d7f8196e12b186dae6e8a4。

逐一回读作者登记的 27 个不同路径，校验全部五原源的直接 import 次序及两项外部入口在 1c0d8d194157d87a3e7e8ad0ca6a8ec87c9df6c2 的已有 Git blob。T05_POSTMOD_ALLOWLIST.json 的 SHA256 为 55c780e9c5f9b9b7782fb431c2ae63b120f1839f12515a3ce484601ae840b74a，十个原始发表文件共 66,843 字节，内容包括五个原稿模块、作者报告与注册表，以及独立目录内的三项 stage 文件。此核查只读取源码、元数据与 Git 对象身份。
