# 最终矩形上原真素数幂的费用

本补充使用 11 月 12 日已经独审的两份乘积截断源码。新增三份 Lean 源码，均未编译。原截断登记、原报告和 T09 的原回执保持原字节。

## 实际有符号端点

令 `W_s` 为原秩二平滑物理轮廓，`V_s = eta(product/N^(1−κ₀)) W_s`。系数取共同有限高区／低区政策的 `P4AOriginalFiniteFallbackPolicy.rho`，模数集取同一 `Q`。对每个自然数 A 和 δ>0，有一个阈值早于全部合法宽度、政策和矩形编号。给定 N 达到阈值、原截断的阶数 K 以及原轮廓参数，`P4BOriginalFiniteProperPayment.eventually_actual_proper` 给出

```text
∑ js∈chartBank(N,2), ‖properPowerReserve(L,K,N,N,κ₀,Q,ρ,js)‖ ≤ δ N/log(N)^A.
```

这里 `L` 是该宽度在原整数坐标上的光滑延拓。每一项内保留当初 ψ 分组确定的粗糙性筛子、归一化 Λ 权、同余指示和带互素指示的 1/φ(q) 均值。非零矩形系数的支撑严格小于 N^(599/1000)，这个点态条件已由实际共同选参端点供应。幅值、正模数和全部计数界均在本文的源码中推出。

`eventually_trimmed_two_atlases` 在 K≥2 时进一步给出

```text
‖PP(V_s) − ∑ js∈chartBank(N,2), (mediumAtlas(js) + noMediumAtlas(js))‖ ≤ δ N/log(N)^A.
```

原 `roughPrimeReserve=0` 已在秩二每个真实标签上证明。本补充消耗原参照恒等式中负号所乘的真幂修正。原物理计数的非负质量仍为 `X_s=∑W_s`，T01 使用的 beta 和 aligned k 直接进入上述同一个 ρ。

## 原稿和各项界

原稿补篇《distribution-prime-product-completion-20261010》§2 用独立整数坐标的二进窗、原群上的 Heath–Brown 展开、粗糙性和真素数幂修正来恢复素数测试。以下三个步骤在这条展开上实施。

1. 原 `chi=1−Real.smoothTransition(t−1)` 单调递减，故每个正整数坐标上 ψ 权非负。逐有序词，原二进标签中所有权的绝对值之和恰为一。只有在保留原粗糙性筛子的确切位置后才对其绝对值用一作上界。两坐标的真实非零轮廓同时给出每个整数大于 N^(19/96)、乘积至多 exp(1)N。原 `properChartWords_spec` 提供真实位置及 pⁱ（i≥2），允许两个位置都是真幂。
2. 原 `properTail_reciprocal_le` 对目标轴给出 (⌊log₂N⌋+1)·logBudget(⌊√N⌋)/√(N^(19/96))。另一个位置贡献原调和和。原有序词有限乘积公式保持两个位置的顺序。由乘积不超过 exp(1)N，全部非零真幂词至多 `8 exp(1) bankLogConstant · N^(1−19/192) log³N`。多个真幂位置只在这个上界中重复计数。
3. 对乘积 x≠N，同余模数整除非零距离，完整支撑上的均值按原倒欧拉函数和估计。对于 x=N，原 `fullCollisionWords_card_le` 给出至多 τ(N)² 个有序词，真实非零模数集至多 N^(599/1000) 个。将两个贡献分开，取 ε=(19/96)/4，非对角幂为 1−19/192+ε，对角幂为 599/1000+2ε，二者均严格小于一。两部分各用 δ/2 对数费用。该证明允许任意奇偶性，尤其适用于原偶数目标。

上述真幂和是稿内可补的初等估计。旧 `P5Z.ActualCommonRefinedPayments.eventually_actual_full_bank_small` 对旧 `actualRetain/attachedUpperCoefficient` 和全秩 Family 记账。此处直接复用正整数位置的倒数尾、退化词重数及距离除数界，把它们接入当前秩二有符号行。源码没有新数值输入。

## 同调度状态与欠项

T01 的 `exists_fine_cofinal_same_coefficient_density_and_count` 在同一次见证选择中取得全 22 槽的物理密度、编译支出和所需细矩形预算，SHA256 为 `74f2d4dc15e059f9ab197157ee9172808ddb34d2547dc85733eec878e1fbc3b6`。其所得非零支撑直接满足本补充所用的不等式。后继 `exists_fine_same_rho_hdensity` 把该密度整理成逐 δ>0 的预期形式，保留同一 ρ。其作者候选 SHA256 为 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`。这些后出的源更新了先前冻结 REPORT 对共同选参的时间性说明。本补充的三份数学源码均未导入 T01 的后继模块。

剩余分布目标是对真实同余核及完整还原标量证明所有 `mediumAtlas + noMediumAtlas` 的有符号和为 O_A(N/log^A N)。其中包括经典低秩卷积、实际中段估计、一长及两长分支，以及相应的 Fourier 还原和模数整组条件。真 PRIME 轮廓上的 BV 估计和 11 月 5 日的分组 Leibniz 导数候选没有给出这个总和的付款。此处仍不能给出完整 PP 或最终 K 的计数结论。

本补充按源码和原稿核对。完整导入安装、Lean 展开、核验和 CI 状态另行登记。
