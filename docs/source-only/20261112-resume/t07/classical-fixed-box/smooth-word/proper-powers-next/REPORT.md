# 原经典 U3 夹持族的真素数与粗 Λ/log 误差

七份 Lean 候选源把原 Γ9–21 的全部 20 个非单位原词出现、全部可用有序尾长、实际阶数 4 至 200 的未截真素数 PP 送到同一组选中 Fine 系数的粗 Λ/log HB 和。源代码状态为未编译，独立审读由 T09 记录。登记针对本次工作目录的源码字节。

## 原始依据与复用

在手稿 ba6ec11d 的 `proof-library/source/distribution-prime-product-completion-20261010.txt` 第 23–46、66–97 行，误差先按同一完全乘积取剩余类计数并减去真互素中心，再乘原有符号 ρ。原始窗口使用非负 dyadic 分割。每个图先固定其粗筛截止，再展开各自的 Heath–Brown 组。第 66–86 行对完整乘积的光滑截去、小素数及真素数幂给出分工。该处的有限有序重数和固定低幂余量可以从已有源导出。

* T05 的 `P4BOriginalFiniteProperArithmetic.exists_row_costs` 提供对完整核的两种界。其证明先剔除 ρ 为零的模数，再利用非零整数差的除数界与互素中心的倒欧拉函数和。非零模数小于 N^(599/1000)。原完整 Q 的基数可远大于这个幂。
* `Part3AllKFamilyProperPowerSaving.family_all_k_power_saving` 与 `P5ActualDyadicRankPolynomial.sum_powerBudgets_le_rank_polynomial` 保留原有序整数词、每个实际图的物理下尺度，以及全部图。历史 `P5ActualCommonRefinedPayments.eventually_actual_full_bank_small` 使用 policy8 和独立于图的核。本包直接对 Fine ρ 和各图自身 roughWord 使用已有底层界。T05 对 rank-two 自身的付款和 postmod 对模数大因子碰撞的付款不覆盖此实际载体。
* 旧 `P5ProperPowerSignedMeanHBTransport` 给出同一完整乘积的 signedRow、对角真中心以及有标记坏位的 HB 恒等。全族实际使用旧 `original_prime_allGroup_discrepancy`，其中 `properChartWords` 已把多个坏位并成单个有序词。重复原素数标签保留。取绝对值以后可用各坏位的并界。
* 原 `P5IndependentTestPrimeChartUniformCutoff` 采用 T05 发表的修订字节。`P4BActualUpperTrimPayment.exists_lowPrimeWords_card_budget` 允许独立指定 tuple cap、低乘积界、固定正阶数。原 `originalLowerCut` 的最终严格界独立于标签与模数。旧 HB 六源与手稿、所用定本、各模块和声明见 REGISTRY.json。

## 三项实际费用

1. 每个原词位置的正实权属于 [0,1]。聚合同阶整数权最多为全部原标签及合法尾长的有限个数。该数独立于 N。阶数小于四时的整数权都为零。保留 `Occurrence` 的重复列表位置，完整活动乘积 M≤2N，每个原坐标至少 (1/2)N^(1/90)。`all_prime_cutoffs` 将旧 cutoff 定理应用于独立坐标上限 2N 与指数 1/192。对 N≥2 有 (2N)^(1/192)≤N^(1/96)，旧 transition_floor 把后者置于物理素数底下。由原图内 ψ 非零直接得到所需窗口。每个原真素数的 rough 修正最终逐图等于零。
2. `proper_paid` 估计所有原图上 proper 修正范数的和。非对角在 M<N 和 M>N 共用真正的有符号模数行，其计数部分只含整除 |M−N| 的模数，互素中心保留。取固定 s=1/720，全族非对角费用至多常数乘 N^(1−1/180+s) log(N)^201。对角同余命中对每个模数成立，仍需减去 1_((N,d)=1)/φ(d)，d=1 的净项为零。每阶有序真幂整数词的完整乘积纤维最多 τ(N)^k；同一旧 `tau_word_rank_subpower 200` 对所有 k≤200 供界。其费用至多常数乘 N^(599/1000+2s) log(N)^200。截完整整数词集合时不把重复坏位或 HB 因子阶数当成原词阶数。
3. 固定 0<κ₀<1 后，`trim_paid` 只在 M≤ceil(2N^(1−κ₀)) 的原素数词上使用模数行。该上限最终严格小于 N。取 s=κ₀/4，各阶低词数与行误差各用一次 N^s，全阶代价为 O(N^(1−κ₀/2))。有限个 N₀ 可共同选择。独立坐标上限仍为 2N，各同余查询的目标仍为 N。

上述费用先相对于 `singularNormalization N` 支付。非退化固定区间 [833/2500,1/3] 的原积分给出 `(I/2)*singularNormalization N ≤ clampMass N root t₀`。这一步针对整个经典夹持族，覆盖所有合法 root,t₀。没有逐细格相对误差结论。半份 ε 用于原正计数成本，另一半用于本次真素数与粗 Λ/log 的差。

## 末端

`Part5OriginalH430ClassicalFineRoughAtlas.selected_rough_atlas` 保留旧 Fine 全部量词、原高阶原子、编译开支、实际非零支撑和同系数密度。对固定 κ₀∈(0,1)、合法原夹持参数和正 ε，原 ε-选择的见证在取 N 前选定，最终每个充分大的偶 N 都满足

    count true 1 N μ κ ≤ switchCost·Θ_clamp + ε·Θ_clamp + Re(roughAtlas Family200 N κ₀ D R).

这里 D 与 R 分别为原 modulusFamily 和 coefficientFamily 在同一 ν,β,k、同一 N 的值，μ 为原 clampLevel。最后的复和保留 200 为预先固定的最大秩、2N 为独立 tuple cap、N 为真移位、原 chartBank 和每组 HB 截止。`remaining_branches` 中的 medium 与 no-medium 两分支以原窗口和同一复数核相加。欠项是对该带符号 HB 和的实际解析上界，包括原 same-ρ 原子在局部尺度的许可、(M) 与适用的非 medium 分支估计。其他种子责任、前代计数/反馈、430+11、row12 与根 7/2 的作用位置保持原有证明条件。没有为这些条件取得新的 kernel 或 CI 回执。

此目录仅建立来源及证明候选，未执行本地 Lean、Lake、LSP、guard、producer、数值证明、安装选本或 CI。

