# P2.9 原 H247 与吴函数的 29 个端点

29 项 `H247[i]/2^80 ≤ wuImprovementLimit true δ sᵢ` 都仍待证。`sᵢ = 1+(i+1)/50` 是该闭格的右端点。`ENDPOINTS_29.md`、`ENDPOINTS_29.json` 逐项给出原始有理数串、同格上下两个历史快照的整数、在该格结束的全部原 W1／W2 行及相应的吴表下界。

## 第 247 代的确切对象

目标分子是 `P2HistoricalLowerBankAncestry.iterate designatedW1 designatedW2 247 true i`。第 247 代读取第 246 代，使用保留 `K = 67633/10000` 的 70 条 W1、`K = 67619/10000` 的原 3 条修订 W2 与新增 33 条 W2。整个末段以第 184 代开始。原 `expanded-w2-midpoint-table248-v1.json/history[62]` 的本段代号为 63，保存整表哈希 `e60c3af003222a0c8e760cea006ff108449cf88c3ec2359a5195a12c2766e268`、控制组哈希、36 个 W2 备选和最大变化量。上下两侧的 400 个末代整数另存于顶层。此代号下没有 400 个第 247 代分子。原 30m 的 `sourceIterate_eq` 指明第 247 代的对象，`stage184_guard` 与 `stage248_guard` 指向相邻完整快照。30m 检查中间代号的顺序，没有定理将 `history[62].all_W2_candidates` 的每一个字面整数与实际更新逐项绑定。该数组也不含 W1、Buchstab 和沿用旧值的竞争项。

`P2Historical247CheckpointBrackets.historical_247_bracket` 由原迭代的逐代保留，给出全部 200 个格子、两个方向的同格夹界。`historical_upper_247_real_bracket` 取上侧并除以正的原 `tableQ`。此文件只导入 `P2Historical248Authentication`，复用其两个已有快照声明，未添加表值比较或原表估值。原第 248 代的最后一次下侧 Buchstab 读取的正是第 247 代上侧。在 30m 的 `designated_h248_eq_last_H247_suffix` 与前序包的 `original_bank_from_edges` 中可对照此方向。

## 两次原吴函数不等式

`P2WuUpperBuchstabEndpointBounds.lean` 独立导入原生吴函数和 Mathlib 积分源码。它对固定 `0 < δ ≤ 1/10`、`1 ≤ s ≤ 3` 给出

\[
H_\delta(s)\ \ge\ H_\delta(9/2)+\tfrac37 h_\delta(7/2)+\tfrac9{70}H_\delta(5/2).
\]

先对 `2 ≤ v ≤ 7/2` 使用下侧 Buchstab，从 `v` 比较到 `7/2`。积分变量满足 `v−1 ≤ u ≤ 5/2`，故 `Hδ(u)/u ≥ (2/5) Hδ(5/2)`。再对 `s=3` 使用上侧 Buchstab，从 `3` 比较到 `9/2`。此段 `2 ≤ v ≤ 7/2` 上有 `1/v ≥ 2/7`，而 `∫₂^{7/2}(7/2−v)dv = 9/8`。两次比较保留两端的实际增益。原 `Hδ` 的反单调性把结果推广到所有 29 个参数。全 `0 < δ ≤ 1/10` 的已证 W1 锚点在 `s=5/2` 至少给 `1/5000`，从而在 `s=3` 得 `9/350000`。原工程先前在 `3` 给 `9/420500`。对于其余 28 个 `s ≤ 29/10` 的端点，仍可直接取原 `1/5000`。

在 `0 < δ ≤ 1/100` 可作第二个严格比较。原生 `SecondFunctionalStrictMargins` 在 `δ=0` 与 `δ=1/100` 分别给出第四行标量 `D>1/50` 与 `D>1/60`。`SecondFunctionalSignedCore.D` 中只有 `2/(1−2δ)` 乘同一原 switched cost 随 δ 变化。该因子随 δ 增大，对 cost 的两种符号分别使用相应端点即可得全区间 `D>1/60`。原生 `actual_core_lower` 的 `D/5` 随即给出 `Hδ(5/2)>1/300`。这一步未假设不同 δ 的真实 `Hδ` 本身具有单调性。已有 `SecondFunctionalSmallDelta` 给出通过 `δ=1/1000` 的同值下界。

代入前式得这整个 δ 区间上 `Hδ(s)>3/7000`，`1 ≤ s ≤ 3`。`small_delta_native_box_counts` 利用 `s=3` 的严格余量进入每一固定深度的实际 admissible improvements，再利用 `wuUpperCoefficient(s)=1` 向左平移同一个阈值。故对每个固定深度存在一个 `T`，可同时用于所有准入的 `N,i,Δ,V` 和全部 `1≤s≤3`，实际未加额外筛选的 `wuBoxPhi` 至多为 `(1−3/7000)·boxTheta`。物理 `Q=N^(1/2−δ)`、实际 `P(dN)` 与原卷积窗口均保留。零侧或空源也只通过原有的比较。两个 Lean 文件都只经过按源码的核对，尚待核编译和验公理。

## 已发表吴表与历史数组

吴 2004 §3 定义固定充分小的正 `δ`、深度、物理 `Q=N^(1/2−δ)` 和逐层取极限的原始母盒。§7 表 1 给 `Ψ₁,Ψ₂` 的参数和原普通四行 W2、五行 W1 相关矩阵，解九维线性不等式后给九个 `H` 下界。Wu 2008 §3 表 1 重新列出这九个上侧值并延伸到较大参数。两篇论文讨论的原哥德巴赫母序列与孪生素数一支各自有单独的换元和分布水平。本清单只取哥德巴赫的上侧 `H` 项。[Wu 2004, §§3, 7](https://arxiv.org/pdf/0705.1652#page=29) [Wu 2008, §3 and Table 1](https://arxiv.org/pdf/0709.3764#page=8)

每项取其右侧第一个已列出的 `H` 参数，依原函数反单调性向左使用。例如 `s=101/50` 使用 `H(2.2)≥0.0223939`，原第 184 代同格分子已经是 `36351464408527643182652`。`s=3` 的原表给 `H(3)≥0.0072943`，第 184 代同格分子是 `11269966386557634053989`。分母同为 `1208925819614629174706176`。29 行中每个这样的纸面下界都小于相应的第 184 代快照。即使另行处理充分小 `δ` 的范围，这些显式下界本身仍然不足。原生四行 `ActualMatrixInverseConsumer.actual_lower_with_tail` 给 `Q.mulVec(literalSource δ + literalTail δ) ≤ actualVector δ`，其中 `Q` 是该四行的逆矩阵。左端既未估到本历史金额，也未包含全部原 106 行的新基项。两项新的显式有理下界同样低于相应的第 184 代值。有关严格大小的描述来自抄录的有理数，当前工作没有执行算术核验或运行逐格判定。

## 原稿要求的解析输入

原稿第 795–817 行规定加权平均的 `Θ_Q`、不变的物理 `Q`、全部与已选平方条件、真实 `α` 和后继上限。第 819–858 行将 `1/50` 起点、四次种子反馈和各同族带权作用写入有限递推。第 859–877 行区分仅用于 `U₃,U₄` 的新 430 代与仍用于其他位置的 248 代。`finite-step-typed-closure-audit.tex` 开头明确引用带符号前缀、正换权和四轮种子作为外部输入；`expanded248-remaining-integrals-independent-proof.tex` 开头明确其独立核验只处理数值积分。实际证明链还要在相同正源和归一化下取得 `1/50`、同样 4 轮至 `2327/100000` 的正增益、70 个 W1 的 `KI/8`、3+33 个 W2 的 ordinary／正换权基项，逐项支付原 singleton／pair 与单位面的代际读价，保持选择和继承的原限制。仅就原历史而言，W1 保留 `67633/10000` 而 W2 使用 `67619/10000`。原稿源的总均值对象若用于 Lean 的 `wuImprovementLimit`，仍须在每个固定深度、同一个物理 `Q` 和阈值量词下覆盖所有 `wuSourceBox`。增强支的 `Q=N^ν`、ν>1/2 与原吴母盒的 `Q` 各有来源，经典分支仍可独立证明。[原稿固定版本](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/manuscript-body.tex#L795) [有限作用的原审稿段](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/finite-step-typed-closure-audit.tex) [扩展 248 积分原独立核验说明](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/expanded248-remaining-integrals-independent-proof.tex)

吴 2004 §7 的九个已发表表值和原生四行矩阵提供各自明确的同族解析输入。第 247 代历史 W2 的 36 个候选仍是有限递推中的备选数。原作者在专项独立复核中报告核对过每代全部 400 个整数与 36 个 W2 候选；其陈述的数值作用域不供给真实数论分布或全部带标记计数。两文件新源码没有增加端点许可前提，也没有对 17,572 行、P2.4 的同名历史整数或 430 代程序作任何新的计算。本包给原 29 个比较保留 `OPEN`。
