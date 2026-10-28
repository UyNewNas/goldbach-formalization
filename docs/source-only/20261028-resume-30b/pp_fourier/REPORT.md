# 第二批 pp_fourier：实际 Euclidean → physical Fourier 连接

源码 `P5ActualEuclideanPhysicalFourier.lean` 完成第二批所分配的分析连接，未编译、零正式信用。第一批文件保持冻结。`local_step_complete=true`、`batch_target_source_complete=true`；原 pp_fourier 的完整算术应用仍开，因此 `task_complete=false`。

使用实际 EuclideanSpace（而非 plain Pi 的 Fourier 实例）定义 `normalizedFrequency ξ=(2π)⁻¹ • toLp ξ`。先复用已形式化的 PiLp Lebesgue measure equivalence 和 Haar scaling，证明物理频率 Jacobian 正好是 `(2π)^m`。通过坐标 inner-product 求和证明 native `exp(-2πi ν·z)` 恰为 `exp(-i ξ·z)`，这不是一个新假设。

对实际 compact smooth Euclidean 函数 f，用 SchwartzMap Fourier 的现有形式化证明得到 native transform 的绝对可积，再从已证 dilation 推得 physical transform 可积。把前驱 mixed-IBP pointwise 真实应用到 ξ/(2π)，得到 literal product Cauchy kernel，并连上精确 physical/native L1 mass 与 D/2^m（每个 m，包含0）。

随后从 native Fourier inversion 和已证 Jacobian/phase 推出 physical inverse representation。把第一批 cube-tail theorem 应用到这个 actual transform，得到实际保留立方体反演的逐点统一误差 `m * mixedD(f) / H`，不需要另给 representation、pointwise 或 tail 结论作为前提。维数0另证明 Jacobian=1、遗漏集合为空、任意cutoff下截断反演精确等于f。

剩余全目标：把原稿实际独立 all-k W_N 的 occurrence chart 及 D_T 混合导数付款绑定到本模块的 compact Euclidean f；retained mode 算术调用以及完整模数求和后的尾款（特别 b=T 和 same-rho exact mean）。本模块不声称完成 PP、hUpper/hLower 或最终定理。未发现新的原稿数学缺口。

只做源码推导和 pinned Mathlib API 定向读取；未运行 Lean/lake、checker、额度检查、Git 或安装。所有依赖及精确 hash 记录于 REGISTRY.json，生产和第一批源码均未修改。
