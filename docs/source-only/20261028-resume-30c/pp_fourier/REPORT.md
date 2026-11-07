# 第三批 pp_fourier：actual all-rank occurrence → Euclidean mixedD / same-rho mean

交付两份新源码，均已闭合、未编译、零正式信用；第一/二批及生产源码未修改。`local_step_complete=true`、`batch_target_source_complete=true`；原大目标 `task_complete=false`。精确原稿、依赖及源码 SHA 均登记在 REGISTRY.json。

`P5OccurrenceEuclideanMixedIntegral.lean` 把真实 Pi occurrence 函数经 EuclideanSpace.equiv 和 Complex.ofReal 提升为 Euclidean 图表。用实际 Frechet chain rule 证明 Euclidean coordDeriv/coordWord 与原 occOne/occWord 一致，保留 repeated labels。再用真实 PiLp measure-preserving 变化证明每个混合导数的 Euclidean L1 等于 occurrence L1。

固定 plateau 的支撑盒为每坐标 [-1,log2+1]。源码构造其真实 interval indicators，以 finite-product Fubini 得到精确固定盒质量；Frechet derivative 支撑包含关系保证所有导数仍在此盒中，因而从逐点 occurrence 预算推得 mixedD 积分预算，而不是把 D_T 当假设。固定有限维数常数 `dimensionBudget(kStar)` 在 T、owner、U/R scales 等参数之前选定，包含m=0。

`P5ActualAllRankOccurrenceFourierBridge.lean` 直接消费 pp_derivatives 第三批已冻结的真实 eta/psi/plateau actualChart 及其已证明 word budget，获得同一个原稿 all-rank Family 的实际 mixedD、实际 Fourier L1 和截断误差预算。原 Family 仍是原稿允许的独立几何测试族及原始 mixedEuler 条件，没有新设 hPP/算术输出前提。

在真实 right-closed (U,2U] HB 整数 atom 上，证明 log(n/U) 的 groupProduct 恰好恢复独立原 group word、plateau=1、完整整数乘积不变；其物理 phase 是每个独立 occurrence 的 tensor。由已证明的 actual physical inversion 构造整数权重的 Fourier 表示，未另给 hrep。最后用实际有限复数 functional 的积分交换，证明同一 rho 的 residue count / exact coprime mean 分离恒等式，并允许任意固定 HB 算术 slot 权重 beta（μ截断、log、rough projector、有限符号和重数）恢复到每个独立 tensor mode。没有把模数中的 marked t 当成独立 u。

剩余完整 PP：真正的原 HB atlas 与 retained branches/有限标量付款；medium/low/one-long/two-long 的实际模式估计；先做完整模数求和之后的尾款，尤其 b=T、square/collision 和 reciprocal-totient 项。实际物理 rho 类、hUpper/hLower、主定理均未闭合。未发现新的原稿数学缺口。

全程仅源码逻辑推导及定向读取；没有 Lean/lake、数值 checker、额度、Git、安装或生产文件操作。
