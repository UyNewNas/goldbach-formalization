# U3、U4 原计数与实际 Fin 的交叉核对

本报告对应三份 Lean 源码。它们把原始两个带标签的整数商接收集接到同一冻结水平的闭格，给出普通筛的带符号精确等式，并确定稿内 β 预筛时 P5 的四类账目究竟落在哪里。三源的 Git 对象、SHA-256、完整声明及直接前驱见 [RESUMED_ROOT_REGISTRY.json](RESUMED_ROOT_REGISTRY.json)。后续经典尾段的 BV 估计单独登记。

## 原稿中被分组的对象

固定原稿提交为 `ba6ec11d800eccc54406490631895e174de85766`。原 U3 的指定素数带是 ([N^a,N^{1/3}))，U4 是 ([N^a,N^{59/250}))，其中 (a=417/5000)。固定 (p) 后，整数商 (q=(N-\ell)/p) 来自原加法素数 (\ell)，满足 (p\mid N-\ell)、(\ell\nmid N) 及商的粗糙条件。除法在此原素数集合上单射。U4 带落在 U3 的增强段内，所以同一 ((p,q)) 在二者有两个标签、同一个真实冻结 (Q)，两个标签的陈氏系数均为 (-1/4)。U3 在 (t=57/224) 起转入单独的经典段。原稿给出的 (H) 估计对完整、非负的标记素数盒平均，指定 (p) 的 (\Theta) 在各标签内取一次。见 `own-chen-table-insertion-chain-20261009.tex` 129–175、222–244、364–398，以及 P5 的 `original_u4_overlap_real_Q_equal`。

在稿内的因果 Rosser 树上，首次排除将**平方自由模数除子**按照有序素因子前缀划分。此前的立方准入结论在子节点原样保留。选定子积的旧槽保持原来的编号，检查每个旧剩余槽，将新槽的选中后余部平方条件化到同一个全平方条件；继承的 cap 等于旧 cap。末端带符号 Euler 项带有全部剩余小素数的乘积。另外，β 小素数在门槛以下，粗素因子盒在门槛以上；固定粗盒以后仍须按原符号接上 β，再作整个标记系数族的分布估计。见 `actual-k-compilation-joint-audit.tex` 13–42、49–109、111–131，`own-lower-compiler-chain-audit-20261009.tex` 45–120、145–179，`finite-step-typed-closure-audit.tex` 32–92、94–132，`current-eighth-distribution-interface-audit-20261009.tex` 300–321、342–367。后者明确允许对事先固定的有限盒总和作绝对 (o(\mathcal H_N)) 估计；逐盒质量可以任意小。

## 与 P5 逐项对应

| 原责任 | 已有固定源 | 本轮核对 |
| --- | --- | --- |
| 实际 ((p,q,\mathrm{tag})) 到真实 Fin | `FourLaneFullTaggedFin` 129–195、`OriginalTagSeparatedFinSource`、`U4ActualFinDoubleTag` 74–171 | 保留项推到 ((Q,p,r)) 所对应的实际 Fin。若一个原 U4 对真的被保留，该位置的单位权重为 (2+R)，带符号值为 (-1/2-R/4)，其中 (R) 是同一槽剩余的真实收据数。四类外部收据也有精确等式。其假设中的 retained 必须逐案满足。 |
| 稿内 β 门槛 | `OriginalRootCutoffObstruction` 42–99、`OriginalSelectedRootFibres` 219–248、`RequestedOriginalRowFreeze` 85–124、`PhysicalSlotListPositions` 34–42 | P5 的第一层候选确实只含 (p<z_0)。若 (z_0) 位于任一活跃冻结 U3/U4 根的实际 cutoff 以下，后者等于 (N^{\min(a,L/2)}\le N^a)；两原带都满足 (p\ge N^a)。故每个实际 Fin 上的原权重为零，所有原标签落到第三类“根的严格 cutoff 阻挡”。策略阻挡类以及先保留根后再失败的两类为空。没有活跃根时原收据集为空。此结论涵盖端点等号，仍允许 P5 在大于 (N^a) 的另一参数下有非空条件例。见 [实际预筛上的四类收据](Part5OriginalH430PresieveOutsideFin.lean)。 |
| 全平方、选中与继承 | `RootSourceDictionary`、`RootGateObstruction`、`RequestedAdmission`、`RequestedHistory`、`ClosedOwner` | 增强段有旧平方准入及同层下降；经典段用完整模数低于半水平。把经典尾段也强制套入带原指定槽的 enhanced full-square 谓词，会在非空开区间失败。首个外部指定素数和后续余筛素因子分开后，原稿所需的是对完整带标记系数族的普通筛、对子和切换估计。原始 Euler 唯一性没有把一个 (q) 变为一个独立的被许可收益。 |
| 带标签的实际普通计数范数 | `OwnedRootCounts.owned_root_marked_count_exact`、`owned_root_theta_floor_exact`、`P5OriginalU5FrozenSource.frozenRemainder_eq_actual_signed_AP`、`SameQCanonicalMains.physical_main_sides` | 对一个完整根盒的所有素数标签给出下面的原除数盈余恒等式和普通上界。每个完整模数的真实中心和有限互素均值均保留；原来小于 (N^a) 的比较切口留下非负最小素数壳。 |
| (7/2)、12、430+11 | `PhysicalRoots.actual_root_coefficient_norm`、`actual_transition_norms`、`RenewalFiniteErrorPropagationP5` 235–254、257–332 | (7/2=\sum_{i=1}^{11}|c_i|) 作用于十一项的定向误差。12 约束真实 106 个动作、两向 Buchstab 及保留行的非负反馈质量。共同逐层局部误差 (\delta) 经过 441 层才得到 (\delta(12^{441}-1)/11)，再乘 (7/2)。这些界各自保留完整的原前提。 |

## 整个商纤维的普通筛盈余

在一个原标签的固定根盒 (B) 上，(s) 是该闭格内共用的单侧查询，(Q) 是同一冻结水平，(z_p=(Q/p)^{1/s})。令 (P_p) 为屏蔽 (pN) 的严格小素数积，(D_p=\lfloor Q/p\rfloor+1)，(g=\gcd(P_p,N-\ell))。新等式中的有限盈余为

\[
 E_p=\sum_{\ell\ {m original},\,p\mid N-\ell}
 \left(\sum_{r\mid g}\lambda^+_{D_p,z_p}(r)-\mathbf 1_{g=1}\right)\ge0 .
\]

每一真实存活的原商都能找回原 (\ell)，其 (g=1)，这个 (\ell) 的盈余为零。(E_p) 的正贡献只能来自其他被筛掉的标签。完整聚合既保留这些实际见证，也保留原 (q=1)、重复因子和冻结 cutoffs 的开闭约定。[真实素数标签和除数盈余](Part5OriginalH430RootRosserSurplus.lean)

设 (C_p=\#R_N(p))，(S_p) 为从原 cutoff 降到 (z_p) 所得的最小素数壳，(M_p) 为同一上 Rosser 多项式的主项，(D^{AP}_p) 为同一整套系数作用于完整模数 (pr) 的带符号余项。总和同时保留原素数集合中每个模数素因子的真实删除及 (\operatorname{li}(N)) 平移。精确等式是

\[
 \sum_{p\in B}(C_p+S_p+E_p)=\sum_{p\in B}(M_p+D^{AP}_p).
\]

写 (H_B) 为此盒在原参数处的第 430 代选中闭格值，(\theta_p=4\operatorname{li}(N)\mathcal C(pN)/(\varphi(p)\log(Q/p)))。相对于原上界的精确差是

\[
 \sum_{p\in B}C_p-(A(s)-H_B)\Theta_B
 =\sum_{p\in B}\bigl(M_p-A(s)\theta_p+D^{AP}_p-E_p-S_p\bigr)
     +\sum_{p\in B}\theta_p H_{430}(s_p).
\]

最后一项取每个原查询 (s_p) 的实际分子；共有端点取既有相邻最小值，结构性 (s_p=2) 不丢弃，支持外值为零。上式不要求在共同右端点重新选择时获得同一赢家。统一的普通主项估计给出 (M_p\le(A(s)+\varepsilon)\theta_p)，阈值先于标签、冻结精度和目标。两带原总数的上界见 `original_U34_at_signed_root_AP`。[闭格精确差及两个原计数](Part5OriginalH430OwnedRootRosserBalance.lean)

## 剩余数学责任

1. 在原稿事先确定的许可素数盒上，要定量证明带符号算术误差、真实盈余、最小素数壳与 (H_B\Theta_B) 的合计能按原方向支付。平方条件、因子分组、单个 Euler 后缀非负或者单个 Fin 槽有两个标签，均未给出这个估计。当前证据排除了用“每个存活 (q) 自己产生 ordinary Rosser 盈余”直接付款的解释；它没有给出原 (H_{430}) 不等式的反例。
2. 旧 5 源 `pair_rosser` 保留 36 行的四个正对子和余款，旧 8 源 `seed_pair_closure` 保留原 20 个有色词、坏 Γ5、真实单元 (m=1)、严格整数斜边、原四轮的七个反馈和同 (\rho) 的 prime-product 调用。两包已由 T09 独立作限定源码审查。一般增强区完整标记普通 AP、同 (\rho) 切换分布、原种子和前代付款仍各自需要来源。已有普通尾段的真实模数 BV 来源另见独立尾段登记。
3. 仍须以同一事先固定的有限嵌套细化、旧表 (Q80) 系数、完整 `Member` 准入、原 `base/switched/seed/floor` 进入 430 个同步动作层和另外 11 层，再作根端点归一化。冻结参数 (c=49044063/25000000)、(K=8452171/1250000) 沿用原值。

此三源属于 SOURCE_ONLY。没有运行本地编译、守卫、数值复算或远程构建。编译、传递公理与 kernel 回执、整项 h34 验证均待核。
