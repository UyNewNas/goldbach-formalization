# pp_fourier 源码交付

新增 `P5AllRankCauchyCubeTail.lean`，源码已闭合，未编译、零正式信用。原分配任务整体仍未完成；本次完成其真实下一处义务：原稿 PP section 4 的全 rank product-Cauchy cube-tail union/Fubini 计算。

证明先把遗漏立方体写为有限坐标 slabs 的并，不假设互不相交。每个 slab 是一维遗漏核与其余普通核的乘积；将一维 Cauchy 核除以 π 后，其余坐标通过实际 finite-product Fubini 精确积分成 1。正半轴用 Cauchy≤x⁻² 和原始 improper integral，负半轴用反射，得一维 tail≤2/H。随后恢复 π 的乘积和 `(2π)^m` 归一化，得到全 m（包括 m=0）遗漏质量≤m/H。最后对满足 mixed-IBP pointwise bound 的实际物理频率系数 A，证明 retained-cube synthesis 的误差≤mD/H；相位只需可测、模长≤1，不支付频率立方体体积。

`pointwise_cauchy` 的最新 live 前驱已增加 `PiLp.volume_preserving_toLp/ofLp`；本次未重复它。新的尾积分只导入 `P5AllRankCauchyKernelIntegral`，精确源 hash 和安装对应记录于 `REGISTRY.json`。该前驱及其 compact-mean 前驱也是未编译源码。

剩余：实际 Euclidean Fourier 的 normalized frequency ν 到物理频率 ξ=2πν 的 dilation/Jacobian；真实 all-rank W_N 和 D_T；先做完整模数和之后的尾款（包括 b=T）及实际 exact same-rho discrepancy 插入。未把这些结论当新假设，也不宣称 PP 已完成。

仅源码逻辑审阅与官方 pinned Mathlib API 定向读取，未运行 Lean/lake、数值检查或额度检查。未发现新的原稿数学缺口。
