# 原生零模 Eisenstein Gram 的第二独审

第 T04 包注册表 SHA-256 为 `648fa27836a6873e5529d86cd981b8e27059d472111162b0b3ecdcc86792c408`。本次补充审查核对新水平边增长界的实际供应对象，与 T06 对积分换序、复共轭及轮廓方向的审核互补。

固定 Mathlib 的 `completedRiemannZeta₀(w)` 等于改正后 theta 核在 `w/2` 处的 Mellin 积分乘以二分之一。原强函数方程对任意复参数给出可积性；在正半轴两端分别用实参数 0 和 2 的绝对可积函数控制整条带。完整 zeta 所加两项的分母在 `|Im w|≥1` 均有模至少 1。原导体一 Eisenstein 的两条波取 `w=2s` 和 `2s−1`，其实际正高度带上的幂有统一界。原非零频 K 级数与正导体带特征的已证 envelope 可复用，随后只在从 completed 变为 ordinary 时用一次 `(Re s−1/2)⁻¹`。 [RiemannZeta](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/NumberTheory/LSeries/RiemannZeta.lean) · [HurwitzZetaEven](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean) · [AbstractFuncEq](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean)

固定实际层数时，Young 原 divisor kernel 的 LDU 分解给出行列式模的正下界，每个 divisor 的每个素因子贡献 `1−1/p`。有限 adjugate、非零 level factor 和原 Cramer 表示给出全带参数一致的 dilation 系数界。实际 `D_as_dilations`、`originalSlot.realized` 和 `inverse_cusp` 把界传给该层所有原生 cusp。在观测帧的规范化高度一闭路径上取平均，减掉真实 incoming delta，即为原 `continuedEntry`。双测试的紧支 log-height Mellin 因子有界，整个旧标量满足 `δ|F|≤C exp(π|t|)`，其中 `δ=Re s−1/2`。常数可依赖于固定层、帧及测试函数。此证明保留复合层及重素因子，无另加抽象散射矩阵范数假设。

在 `t=±T`，角点多项式的模含一因子 δ，高斯提供 `exp(−(π+2)T)`。两条垂直线有旧的真实可积供给，修正标量 `F−r/(s(s−1))` 的有理尾可积。从带阻尼的矩形回到原上下边后，原 `edge` 趋于零。相应终端 `spatial_gram` 的源 SHA 为 `57be686e34516633f1902249fd7d31ae23b09aaf0cefd70a5ab693d6c3d34805`，作用对象是正整数层、任意两 cusp 帧及平滑紧支的零频 Poincaré 生成元，含真实常数投影、全实轴的物理 cusp 配对和单个 `1/(4π)`。向完整商空间延拓及在原非零 M/N 包上的谱坐标识别还需证明。常规／例外绝对大筛、KS 参数、主稿带符号几何 trace 同样各有独立义务。本独审只核对源码与数学输入，未执行 Lean 或核验器。
