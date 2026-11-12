# 最终有限策略在原 87 域的八层成员

对每个原始域、整数目标和八个不整除目标的素数，本包给出最终策略八层前沿中原状态的精确成员判据。在稿件要求的共同历史保留域内，该状态实际出现。在整个原域上，未同时入树并取得原第八层更新的素数词，其非负权重总和可压到任意给定的正误差。四份 Lean 源已静态核读，远端内核验收待办。

## 一个实际素数词

`P1OriginalFinalEighthFrontier.rule` 逐字取原有限 fallback bank B、扩大后的第五层数据 d⁺、全有序第三层和 R17 第六层。其偶门总为真，`rule_is_physical` 给出它与原物理系数使用的奇门投影的函数相等。对任意原严格域的词，`actual_source_iff` 将 `canonicalState ∈ firstExitDepthFrontier 8` 精确化为第 1、3、5、7 个实际奇前缀的四个门。相等墙及缺少历史 owner 的输入均适用。第八层更新另有原 action trim。`received_source_iff` 在整个原域上同时判定是否入树、是否由本域接收更新。

原八个素数按降序输入，状态的 selectedPrefix 是原列表所用的逆序。正号为 true，质量是八个实际局部权重的乘积，剩余素数是同一 roughPrimeUniverse，以第八个素数为严格上限、以原 w 为下限，并删除 N 的素因子。一般实函数 g 可用于逐词成员与质量结论。原素数和使用 g(p)=1/(p−1)。`canonical_iff_admitted` 从原 occurrence 排列恢复同一个四字段状态。后续求和也沿用同一列表的重数。[原前沿排列与带历史权的等式](https://github.com/UyNewNas/goldbach-formalization/blob/fecfaff4fe34657cbb1e70a24c6fbb53b0d27d54/ImbalancedChen/FirstExitAdmittedFrontierTuples.lean#L127)

## 共同历史和实际 parent

`P1OriginalFinalEighthMemberSupply.cofinal_history` 复用原共同历史定理，在每个 Source 与同一 core 的交上给出原 first stop、原第三层支持和真正的四个奇门历史不等式。对同一八元词的每个非空祖先，首坐标小于 μ，使最外层调度逐字落在原低区。前两层保留共同初始规则，从第三层起，在自身的祖先上由旧 owner 接回完整有序根。`ThirdOwner` 给出 j 属于真实第三层历史网格、前三个素数坐标处在该标签的半开盒、实际第六祖先所读的 scalar 等于该盒带原缓冲的 levelExponent，并且 lower 成立。

`supply_of_history` 同时给出本词真实第六 parent 等于其 d⁺ 上的 actualParent，以及 λ₃ ≤ λ₆ᶜᵘʳ ≤ R₆。这里 λ₃ 从同一个词的真实第三祖先继承。它与原历史供给第七奇门，随后第八偶态出现在最终前沿。每个后继沿同一八层祖先查询原 c 的 selectedCap。在该 c 的 action trim 内得到自身 finiteCap，trim 外继承。一个 core 上的词可以已入树而没有第八次更新。[共同第三层、实际第六层及第七门，原稿第 49–101 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/eighth-unequal-parent-interface-20261009.tex#L49) · [原 87 域、实际历史与第八层符号，第 173–241 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-current-upper-density-assembly-20261009.txt#L173)

## 有限 N 的实际遗漏

对源上没有同时满足成员与原更新的算术元组，`missed` 计入 ∏ᵢ(1/(pᵢ−1)) × (1+profile)。原 profile 在源上等于 4/(R₆−S₈)−4/(M−S₈)，乘以八个坐标倒数恰为原 kernel。这一收费同时控制漏词本身的倒素数权和原 profile 权。源外为零。原严格行的外侧指示函数以及内侧连续 ramp 均在真实目标删素后的素数盒上取和。对于线性部分为零的行，若域非空，用其中一点证该常数处处通过；若域为空则两个极限均为零。其余原行直接用非零线性部的原多面体素数极限定理。由内侧在每个严格源点最终为一及原可积支配，先取共同 r，再取整数目标阈值，得到全 87 个非负遗漏之和小于 ε。[原目标删素多面体素数和，第 127 行](https://github.com/UyNewNas/goldbach-formalization/blob/fecfaff4fe34657cbb1e70a24c6fbb53b0d27d54/ImbalancedChen/ActualPrimePolyhedralTestFunctions.lean#L127)

`frontier_test_eq` 在每个域上将该域 owner 的实际八层 occurrence list 按自身质量与原 profile-ramp 求和，逐项等于该域的原 testSum。反向包含用的是本词在实际最终树的成员。同一次选参给出 0 ≤ ∑ missed < ε，同时原 87 个源 kernel 积分之和减 ε 严格小于 ∑ frontierTest。

`cofinal_final_membership` 先给 ε，再取共同 r₀，对每个 r≥r₀ 取 n₀，对每个 n≥n₀ 有 4 width(n)<width(r)。依次取正小有理 e、足够大 q、a≤1/100、共同 N₀≥2。之后对所有有限 B、ω≤a、N≥N₀ 成立。一般载体保留 w≤N^(53/13824)、N^μ≤z≤cap。`cofinal_original_carriers` 在同一选择中取 cap=N、z=N^(19/96)，对原编译器晚取的 ω=νβ²≤a 同时允许普通 w=0 和正预筛 w=N^ω。保留 ν>0、0<β<1/8、νβ<1/1000。[稿件中不同的边界与编译误差预算，第 158–171 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-current-upper-density-assembly-20261009.txt#L158)

## 源码裁定

原稿给出了同源紧集上的共同祖先、实际第七门和 source kernel。旧历史树的 canonicalState 与前沿连接、最终完整策略的布尔读数及原素数和极限均已有。新增部分把这三者接到最终有限策略的单树实际列表，并在严格原域上控制真实算术遗漏。原 87 个数值 floor 的认证和原 R17 的 signed gain 复用此前冻结记录。当前终端只对原 87 个源的上述算术测试付款。P1.4 的其他 signed 物理 reserve、低模数 PP 与同源闭包的远端内核验收各有独立责任。Y05 下可单独登记实际成员与漏词权的源码覆盖，父级职责另按原清单裁定。
