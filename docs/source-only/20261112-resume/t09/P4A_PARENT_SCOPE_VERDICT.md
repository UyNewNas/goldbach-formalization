# P4A 父项的实际物理密度

**建议再将 P4A 父项「同一物理rho的尖锐密度K=6.7617368」由黄改蓝。** 冻结子项裁定的三行保持原样。本次单独核了父项的模数、全物理系数、归一化和数值常数，新增绿色为零。

原稿 `9731290e` 正文第 9–11、41、451–511 行定义 C_N、K、最终有符号系数及其密度。式 `current-upper-density` 要求 Σ_q ρ_N(q)/φ(q) ≤ (K+o(1))C_N/log N。`currentK` 在 `CurrentNumericalTransfer` 内定义为 8452171/1250000，与原稿等号右边 6.7617368 一致。`singularSeries N` 使用原 C₂ 与 N 的奇素因子修正。`physicalDensitySum` 的被加数逐字是 ρ(q)/φ(q)。

`P4AOriginalFiniteAll22FineDensity.exists_fine_same_rho_hdensity` 给出一个 N 前选好的有限策略。对每个充分大偶 N，直接给出 `physicalDensitySum (Q 0 N) (rho 0 N) ≤ currentK*(singularSeries N/Real.log (N:ℝ))`。Q 取实际小素数与粗模数的乘积载体。ρ 取最终派发树 F 的完整矩形附接系数，正粗系数用上 β 多项式，负粗系数用下 β 多项式。其余自然数上的系数为零。因此有限和覆盖原式中的整个支撑。真实策略在高首素处读已冻结的二/三阶 bank，在低区读已修正的有序策略和 R17。后继 PP 误差以及有限 RealB 计数中仍使用同一个 Q、ρ。

该出口未要求调用者先给密度、reserve 不等式或 PP。正的 e 上界允许取足够小的正有理 e，a 可取 (0,1/800]，q 在此后按所需公倍数选取。`CommonGroups.gap_pos` 给可选的正 η_PP。ν、v 正且 νv=19/96，β 上界、额外正余量和任意正的精度函数均为真实可选参数。随后只选一次 β、k，在 N 前固定。δ 不改变系数。原始四正项、22 个 saving 及两笔 reserve 已在三子项的独立裁定中逐项核过。

对 N≥N₀，N≥2、0<β<1/8、β²<v、ν>0 给 1<L=N^(νβ)、w=N^(νβ²)≤L、w≤z=N^(19/96)≤N。正是同一次编译使用的四条门。`P4AUpperTaggedBetaAttachment.rho_majorant` 因而对任意整数（含零）给出原筛示性函数的逐点上界。`rho_abs_le_one`、`support_squarefree`、`support_coprime_target`、`compiled_modulus_dvd` 与终端对非零 q 的严格 N^(599/1000) 界均适用于这个系数。因此父项不需要额外假定任意实数列是“物理系数”。

原《actual-k-positive-assembly》把同一系数的尖锐密度与其独立的 signed-distribution 估计明确列为两个输入。前者在上述真实有限外/内矩形编译上已具完整源码。选择定理并不声称逐格算术 ALL/ANY 与每个连续端点测试的值恒等。以后若换编译系数，不能移用这里的密度。对当前同一 ρ 的完整 PP、RealB 上界及每个解析分支继续留在 P3/P4B。前述源码仍待完整导入、原始有限守卫及 kernel 验收。
