# pp_twolong 第三批：实际 HB chart、Fourier 系数及平滑条带

交付两份闭合源码：`Part3ActualHBCompactLogChart.lean` 和 `Part3TwoLongActualSmoothStripWitness.lean`。第一、二批 SHA 已核保持冻结。源码未编译，正式信用 0；本轮完整目标及原目标仍开放。

第一份从原始 `Family`、完整乘积 `eta`、每个原群 `psi=chi(t)-chi(2t)`、实际 `groupedProducts` 和 HB `Block/Owns` 显式构造 compact log-chart。每个出现坐标按 `lower(block)*exp(z)` 回到原始变量，固定 occurrence cutoff 在整个 `[1,2]` 归一化 dyadic rectangle 上等 1；代码证明所有有限 rank 的光滑性与对数紧支集。其 actual Fourier 系数由 EuclideanSpace 上的 Schwartz Fourier 变换构造，L1 与 inverse 均从 Mathlib 导出，没有 `hRepresentation` 前提。

频率类型与归一化直接记录：定义 `xi=2*pi*nu` 的可测等价，`physicalFrequencyMeasure` 是 native Euclidean volume 的推前；`physicalCoefficient` 是原 Fourier 系数复合逆等价。代码证明 exact inverse 和 L1 不变。**这里积分用的是推前测度，不能再向 coefficient 乘一次 `(2*pi)^(-r)`。** 若后来改用普通 xi-Lebesgue，须先证明测度密度并只计一次该因子。

实际 `Owns` tuple 上，compact chart 回到原始 `rawHB` 几何系数。`owned_reconstructedProfile_identity` 把同一 tuple 的两个 Brun 长变量接入第二批 `reconstructedProfile`。随后证明短 amplitude 对长坐标更新不变、完整 HB product 确实等于 `shortProduct*d1*d2*u*v`，并得 `ownedGeometricCore_eq_integral`：原始 owned 几何 count 与 exact coprime mean 使用同一 coefficient 的实际模态积分。原始 dyadic indicator 仍显式保留，未把它冒充光滑完整矩形。

第二份给真实 Mathlib C∞ bump 构造的 interval upper 与左右 endpoint strips，保持 `(a,b]` 的严格左端点；`upper_sharp_error` 和 `rectangle_error` 给出原上核/两 gap 核所需点态夹逼。`delta<=1/4` 时归一化 profile 支持 `[1/2,5/2]`；还证明 endpoint-strip 总积分 `<=8*delta` 及 C2 紧支集/N2 可积性。由这些真实见证接成原三份 smooth Brun 核身份仍须下一步，不能靠命名或函数定义宣称已完成。

剩余工作：具体全局实际 Family/slot allocation 实例、该 compact extension 的固定 polylog Fourier 质量、完整模数尾处理、smooth upper/gap 三核身份、条带统一 `N1=O(1)` 与 `N2=O(delta^-2)`、实际短角色/Mobius/log 权重以及 P1/P2/full E4。未发现新的原稿数学缺口；实现与量化义务均如实保留。精确路径、SHA、导入和边界见 `REGISTRY.json`。
