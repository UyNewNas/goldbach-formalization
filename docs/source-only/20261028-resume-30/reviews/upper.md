# Upper 四项独立源码验收

结论：四项均为 **SOURCE_REVIEW_PASS**，限于各自局部源码命题。`compiled=false`、`kernel_verified=false`、`formal_credit=0`、`task_complete=false`；整个 upper 与主定理仍为 OPEN。

已读每项完整 Lean、REGISTRY、REPORT，以及必要的前驱定义和原稿相关段落；未仅采信作者报告。已重算四份候选源码及登记中可解析的本地 path/hash（包括 manifest 和 Jensen 的哈希映射），全部一致。逐项哈希证据见 `upper.json`。没有调用 Lean/lake/编译器/检查器、修编译、数值重放或额度检查；哈希不代表传递依赖/API/内核闭包已验收。

| 项目 | 结论 | 实际通过范围 |
|---|---|---|
| upper_chronology | SOURCE_REVIEW_PASS | literal cell0 的96行导出语义守卫、H3 排斥及有真实祖先前提的 slot16 绑定 |
| upper_fifth | SOURCE_REVIEW_PASS | 两个显式 named parent 的完整 gate、局部原选集恒等及实际积分分解 |
| upper_mesh | SOURCE_REVIEW_PASS | 固定有限 raw bank 下先选有理 e、再选 q 的统一网格调度 |
| upper_jensen | SOURCE_REVIEW_PASS | firstF 的凹性/单调性及 Q 的局部凸性/单调性，消去 hconc |

## upper_chronology

`literalRows_old_planes`（60行）正确处理62个严格旧平面行及 mask6 的精确等式：mask1..5 对应34..38行，mask7..63 对应39..95行。已比对旧 mask 的 A/C 选择约定与系数。`literalRows_cellGuard`（122行）的完整平方索引 `[18,19,21,23,25,27,29,31]` 与选中补集平方行 `18+2j` 对应实际定义，其他行保留 eta 平移、两端残量及 R<M。

H3 排斥使用 cell0 的 H3<R=D23 与前驱动作的 D23<H3，方向正确。`retainedLiteralCell0_slot16`（224行）保留真正的 firstStop、长度8与实际继承 CurrentParentGuard，没有把实际第六父 cap 等同于 raw envelope R，也没有从静态行推出实际 admission。没有发现目标结论被循环作为前提。

尚缺 N 依赖半开实际 carrier、等式墙归属、真实十一祖先 guard/firstStop 绑定、其余 cell 和17/18/19槽、full58/full87 与同 rho 物理系数/K；报告如实保留这些缺口。

## upper_fifth

两父均为 grid400、mask28={2,3,4}。独立有理核查给出 selected cap lower=1/2，qVLo 分别为939/1600、933/1600；e=3/51200 时两者均满足1/2+2e<qVLo。损失单调引理方向正确，向所有 e<=3/51200 延伸。原选择 membership 来自实际 held owner 证明；局部 namedJ5 没有被偷换成全部历史 J5。

两 geometry key 的第0坐标31与30不同，确立真正半开 raw box 的互斥。`actual_selected_integral_eq_two_named_parents`（169行）沿用同一个可变第四父 cap、两个严格 own-cube 条件，rawOwnerDomain 仍是 rawBox 与 actual fullCell 的交集；未用整个 raw box 取代实际积分域，未冻结成常量父 cap。

尚缺存档字节到全部选行的绑定、全历史 J5/all-row 验证、两 raw-owner 积分数值下界及当前 K。现有前提为网格/粗糙参数和真实变量父政策，不是目标积分恒等式本身。

## upper_mesh

rowEnvelope 的尺度为 `modulus(i,e)/400^5 + massBound(i)*(428/75)*e/400^4`，与前驱 B13 一致。固定有限和在0连续且取0，故先取有理 `0<e<min(3/51200,delta)` 使 bank envelope<eta，再由真实 complete-cover 定理取 q。所得 step<=e/20=chi<e/10 且 step<=omega/2，并覆盖每个 grid400、非负 mask raw row 的实际 Ico box；量词顺序正确，无 q 依赖的 child 数量乘子。

`abs_sum_le_bankEnvelope`（127行）仍明确要求逐行误差控制。标量连续性本身不需 massBound 非负；实际应用必须提供适当质量界、真实 kernel 模量与截面控制。该文件没有把调度引理冒充实际积分误差证明。

尚缺正确可变旧父 kernel 的紧集连续模量、selected/firstStop 截面 <=(428/75)e 与 B13 实际逐行积分误差、全行判定或 omitted-child trim、完整87域和 K reserves。报告范围准确。

## upper_jensen

已核 `firstF(s)=log(s-1)/s` 的两阶导数。二阶分子为 `2(s-1)^2 log(s-1)-2s(s-1)-s^2`，分母 `s^3(s-1)^2>0`。在[2,4]，`log(s-1)<=s-2<=2`，因此分子 <=`s^2-6s+4=(s-2)(s-4)-4<=-4`，凹性推导成立。

单调性独立使用 `G(x)=(x-1/x)/2-log(x)`，G(1)=0 且 `G'(x)=(x-1)^2/(2x^2)>=0`。代 x=s-1∈[1,3] 后 firstSlope 非负，方向及端点正确。`Q(b,u)=firstF(b)-firstF(b-u)` 在确切区间 `0<=u<=b-2`、`2<=b<=4` 上凸且递增，由 Q(b,0)=0 得非负。局部 pointwise corollary 真正消去了 hconc，保留正坐标与真实新残量比等几何前提；声明名称也匹配 held ChildQJensen 的需求。

尚缺具体 parent/child 数据、cover 与 clipping loss、实际积分下界、rational log floor 及 K；相关 held 链和 ChildQJensen 仍待独立编译。此处没有内核/API 接受信用。

没有在这四份局部源码中发现需要上报的原稿数学反例、循环前提或隐藏的全任务完成宣称。四项通过均不消除上述全局欠项。
