# transfer_trace 源码交付

新增 `P2CompiledCausalPrimeSourceLower.lean`，284 行，完整局部模块文本；未编译、零正式信用，原分配目标仍部分未完成。

本轮消除一处实际接口遗漏：旧 `CurrentChenOriginalLowerFiniteP5` 处理 raw lower rho；有限格编译器对正负 label fibre 作不同内外舍入，其输出不必是另一棵 retained tree，不能直接用旧 raw theorem 冒充它的 prime-source theorem。本文件直接把 `P2LowerFiniteCellBetaCompiler.rho` 放入真实 `chenPrimeReceiverSource` 的有限 Fubini 和已证明点态 minorant。

证明先给 enlarged rough universe 与 small/rough 输出的 squarefree、target-coprime 支持，再精确分解该同一 rho 的主项、`finitePrimitiveDiscrepancy` 和带符号 `chenInitialPrimitiveCorrection`。后一项保留 centre-prime 与 modulus-prime 两种 correction，使用已证 `|rho|≤1` 付出显式 cost；不假设 rho、beta-minus 或 divisor polynomial 非负。一个前置阈值可对所有后选 plans、meshes 和已给 sublinear physical envelope 支付此 cost。

`exists_compiled_full_policy_original_prime_lower` 继续消费 `P2LowerFiniteCellRawDensityReserve` 的实际 full raw density 下界，并把定义好的 `roundingLoss` 和 beta absolute-density error 保留在原素数计数不等式中。它没有把待证上下界、最终 c 或 signed discrepancy estimate 当作前提。最后 `current_first_row_integer_trace_lower` 用真实 `IntegerRetention.retainEven`，在当前 `417/5000` cutoff 给 `currentChenUpsilon1` 的入口。

这些都是有限 source/mean 衔接；还缺 selected CapPlan 原稿许可、舍入误差趋零、原始 full density 精确评价、同 rho 的 sharp singleton PP 分布、其他 Chen 项和最终 D12 下界。`Upsilon1` 的 source 保留 receiver one；本文件不把它误认为直接的 prime-or-semiprime count。未发现新原稿数学缺口。

依赖和源码 SHA256 详见 `REGISTRY.json`。所有导入均是现有工作树文件；其已编译或已正式验收状态未检查。仅写本任务独占目录，未改生产模块、共享文件、看板或 Git。
