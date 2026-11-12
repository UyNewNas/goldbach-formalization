# P4A.4、全部真实端点子项与 P4A.5 的完整源码裁定

**裁定三项黄转蓝，新增绿色为零。** 本次对照的是主表原文、原始 22 项次序、真实最终策略、两笔独立 reserve 以及实际计数装配器。蓝色表示完整的证明源码已经给出。安装叠层、原始有限守卫、传递公理及远程 kernel 回执尚待核验。

| 主表行（登记快照） | 被裁定的完整职责 | 选定源码 |
|---|---|---|
| 187 | P4A.4 实例化全部真实4正项−22saving并支付reserve | 四正项真实 root、19 项有向 telescoping、低区 3 项与同一最终 F 的两笔 reserve 已合流。 |
| 205 | 全部真实四正项、22 saving 数据端点与同策略 reserve 实例 | 原始逐项端点与方向由各 supplier 给出。R17 的 87 个原始格和末两次增量在最终真实策略上各出现一次。 |
| 206 | P4A.5 对实际同一rho导出hdensity ≤ (K+δ)C_N/logN | 新终端 `exists_fine_same_rho_hdensity` 在同一预选 Q、ρ 上直接导出原消费者的完整前提。 |

## 同一实际策略和数据端点

1. `P4AOriginalFourPositiveEndpoints.actual_positive_entry_le_original` 将普通根 4/Θ、完整第一积分、紧第三积分和原第三尾积分接到四个实际数据端点。后两者经真实区域分割汇回同一第三泛函。`P4AOrderedThirdPositiveRoot.original_four_positive` 用真正因果第三表的算术极限、紧部比较及小尾控制这个根。此处的紧第三上界依赖被冻结的 2,000,000 次分裂闭守卫以及整个 2,000,021 个叶项的求和。该守卫尚未执行。此次恢复的 P2 integer-mass 单叶接口是另一条工作线，这一整账的源码使用已有的完整 compact endpoint。
2. 以 0 为首索引，实际第六层组负责原槽 3、6、7–13（共九项），包括两次 G13 有向补差。原二/三 fallback 负责 4、5。R17 修正的第八层负责 14–17 及 finalFour 的四项，末两次 seed 修正是增量。共十九项。原低区 0、1、2 对应旧第四、旧第五、新第五及其实际重量化误差。`nineteen_slots_dictionary` 与 `exists_final_raw_upper_with_early_defect` 接上同一棵最终派发树，真实低区付款 `cofinal_actual_early_defect` 消掉右侧最后三项的缺额。共同历史包括真实 parent、精度上限、a 后的一个 256 倍数 q 和 N 前的单 β,k。它没有把历史 d₊ 的 14 项自动移植到新策略。
3. 既有普通连接 `3e4ef38c…` 已给全 22 项的实际密度上界。精细连接 `74f2d4dc…` 从实际 raw 十九项重新调用原低区和一次真实 compiler，并保留对 PP 所需的宽度约束。早三项误差 η/2 与十九项误差 η/2 在单一目标 N 合并，得到 normalized raw < quotedAll22Raw+η。`reserve_raw_is_actual_final` 识别最后 F 的 raw 账，编译费按原 u_c 一次支付。原预算 `quotedAll22Raw + u_d + u_c + exactSlack = currentK` 给出密度 < (K−u_d−exactSlack+η)S−corr，S=C_N/log N。选 η=u_d/2 支付真实近似总误差，仍余 u_d/2 与 exactSlack。旧局部 u_d/4、存档 reserve64 及已付尾项没有作为新的额外总费用。

## 同一 ρ 的尖锐密度

在上述同一次精细选择上，ν>0、β²<v、νv=19/96 给出实际 ω=νβ²≤19/96。N≥2 时 w=N^ω≤z。已发布的 `p4aActualPresieveCorrection_nonneg` 对任意 retain 在这一前提下给出非负号，故原来的负修正项保持有利。新源码 `1942060c…` 的 `upper_lt_currentK` 在 S>0 下得到严格 K·S 上界。真实的 `modulusFamily` 与 `coefficientFamily` 对 δ 不再选择策略，N₀ 也先于任意 δ。终端给出的 `∀ δ>0, ∀ᶠ N in atTop, Even N → physicalDensitySum (Q δ N) (rho δ N) ≤ (currentK+δ)·S` 与 `RealUpperCountingAssembly` 的 hdensity 参数一致。正的 PP gap 在 e>0 时有原 positivity supplier，故不存在借空条件制造密度的方法。五个精度约束、支持、支出及保留全 signed error 的 RealB 有限上界仍在同一终端。

## 后续边界

`HighAtoms` 只在其高首素、阶数和局部 x/U/κ 前提下供应几何。完整同 ρ 的 hUniformPP、实际 signed distribution 以及 hUpper 仍需付款。P4B.4 的两个必要输入中已有完整 hdensity，hUniformPP 仍待供应，整项保持黄。本次状态裁定严格限于表中三行。其余层级可由根按各自原文字另审。实际安装要保留 R17 的选择、历史 FullPolicy 与 List 叠层和完整 high-helper 依赖。原始几何、数值档案、quotient 与有限检查的内核状态不会由此变为绿色。
