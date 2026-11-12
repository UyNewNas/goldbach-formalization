# T19 · W1/W2 原始窗口、严格子节点与原根收据

状态为冻结源码候选，局部计数桥已写出，Y26 全分析终端仍黄。三个 Lean 文件均未编译，kernel 与传递公理未验，formal credit 为 0。本文用原稿 9731290e 的同一正标记族、共同 Q 和真残差。形式化的具体实例是有理网格冻结后的 U3/U4 真实选中请求。完整导入身份与源文件 SHA 见 REGISTRY.json。

## 最强终端

`Part5OriginalH430FreshReceiptCounts.owned_fibre_bank_receipt_budget` 对每个原 `RootKey n m`、每个 U3 或 U4 标签，在同一 `cellQ N n c.1` 下加总所有属于该 fibre 的素数和 106 行实际选中的历史位置。门槛由 ε 决定，先于 N、网格、标签、根素数和前代 g。前提为偶数 N 足够大、0≤τ≤1/12、1/(n+1)≤11/384。g 遍历 Fin 430。遇到重叠 U3/U4 根仍按各自原标签计数。

左侧按原物理父查询分为原收据、父拒收壳、canonical upper 减所选改进量的母 Θ 项，并保留 `selectedBankRoundingLoss`。右侧为同位置上 `levelMark × receiptDebt` 之和，加 ε 倍这些位置的 `actualBankTheta` 总和。空 fibre 与零质量没有除法。它保留固定项误差、应付的正乘积费用和前代计数差。

## 端点与旧前缀

1. 原 S17 的三个有限分割在 `goldbach-formalization@3d15576a…:docs/source-only/20261102-resume-30s/s17_causal_bank_licences/` 可直接定位。新源码直接调用这三个等式。T11 盘点中 S17 public identity 未定位的注记由当前 SHA 树补足。
2. `selected_geometry` 从 `selectedLevel` 的实际 owner、`requested_bank_tests` 和 `rootHistory_support` 得出请求参数 ≤ 所选 target、L/target ≤ χ 和 `parentWindow`。从 `history_integer_roughness` 与 cutoff 单调性得 `ChenPrimeRough (cutoff Q d target) d`。
3. 冻结根满足某组整数 u,v 的 Q^v=N^u，且 v>0。若窗内素数 q 的相对对数是正有理数，就得到某个 Q 的整数幂是含 q 的整数，和 q∤N 矛盾。原 `prime_coordinate_ne_rat` 和 `actual_half_iff_open` 已证这一步。W1/W2 单子用原 `leftQ` 接到各自 anchor，四个 pair 的全部常数下墙用原 `pairLowerWall`。这一消零有具体算术证明。一般实数原 Q 的端点和结构性 clamp 等式仍须按各自来源处理。
4. W2 母窗的素数严格低于 target cutoff，若它整除 d，则与第 2 项的真实粗糙性冲突。对 pair 的两个坐标由 `pairHalf_below_target` 分别得此结论。故每个 repeat fibre 为空，包括“在下墙且重复”的情形。原 native `fourthRowMotherBadPrime` 是在该 repeat fibre 上求和的原 sourceSieveCount，三个恢复项分别为零。W1 的原窗从一开始使用 dN。
5. `singleton_W1`、`singleton_W2`、`pair_W2` 对每个 signed 被积项分别给出原窗和等于实际严格 child 和，保留三个 singleton、四个好 pair、p<q、两条新方测试、Q 与完整历史标签。`selected_child_gates` 对原 enhanced 根已有的 full/selected tests 沿实际历史与新 child 传播；经典 BV 分枝单独处理。原稿中 lower x 与 large y 的 pair 以 [y,x] 追加，D5+/D6 在旧 anchor 停止，D7/D8 在较小的 x 停止。

## 碰撞与原 base

长度二时，`SelectedCollision` 的取前 length−2 个字母的列表为空，因而 `collisionCarrier N d [q,r]` 为空。在较长的原有序颜色词中，collision 还要求有被选择的素数整除末余商并位于倒数第二个素数以下。`collision_word_no_old_repeat` 在同一个原词和同一个接收素数上检查两种事件的交集。所有字母都属于顶端小于 target 的原窗，故一个旧前缀 repeat 都不可能发生。余商中仍可以出现同一被选择的素数。

`all36_collision_on_history` 在每个实际历史上用已发表的任意窗口 `collisionSwitched_le`。取 η=frozenResidualFloor/6>0。旧素因子由历史的同一正下界控制。2≤s≤…≤s0≤5 及冻结残差保证实际下界 A≥N^η，实际最大上窗 Z≤N。对原有序词保留 22(1+log N)^6 的原计数上界，经原 `collision_coefficient_le` 与幂对数界得每个 collision≤ε·thetaAtom。母 Θ 的下界使用同一 Q、d、li(N)、奇异因子、φ(d) 与 log(Q/d)。固定 227/50 种子专用的 relative-collision 定理未被套用到其他 35 行。

`selected_debt_exact` 将旧 106 行 terminal 的 `finalDebt` 逐行化为 strictDebt。W1 的窗口费为 0；W2 中剩余差额精确是 literal collision/5。此式中三个恢复项已经逐项消零。加权后把碰撞一次性移入 ε·actualBankTheta，并复用 original W1 first-square/prime restriction 已经完成的付款。原尺度的 W1 的 1/2 与 W2 的 1/5 各出现一次。没有将其他正项与这笔付款合并。

## 原始 full / inherited / rejected 计数

与 T17 共用 `rootMasked_count`、`inheritedChild`、`rejectedChild`、`member_product`，其冻结源码 SHA256 为 172f06c06ccd609e6293abdff07c7401c81b5dc51ae734ccd48ac4273c013119。设根素数为 p，父乘积 d=pD。一个 child 的 B、追加后尾乘积 D'、实际截止 z 如下。

| 严格 child | B | D' | z |
|---|---|---|---|
| W1/W2 单子 q | d q | D q | (Q/d)^(1/anchor) |
| W2 好 pair x<y | d x y | D y x | D5+/D6 用 (Q/d)^(1/s0)，D7/D8 用 x |

从整数 child 几何得 z 不超过新的最小素数，且新字母低于旧 ceiling。原 `history_ceiling_le_letter` 因而给每个旧素因子 ≥z。新源码推出 `ChenPrimeRough z B` 与 B=pD'，直接释放 T17 原收据回拉和原非掩码 quotient 计数的两个输入。用原加法素数 ℓ 计数时，原根收据测试的是 (N−ℓ)/p=D'·x'，x' 是新余商。该测试等价于 D' 与 x' 同时在 N^a 处粗糙。因此

    raw child = root-masked child + #rejectedChild
    root-masked child = #inheritedChild.

这是对每个真实窗口 child 的计数恒等式。`receiptSingle` 内的 full 下界差 = model − inherited − rejected；`receiptPair` 内的 full 上界差 = inherited + rejected − model。原父对应的是 originalReceiptLane + rejectedChild。完整收据账保持这三个符号。若 D' 含低于 N^a 的素因子，原收据交集整体为空，完整 child 仍可能有正计数。该条件本身没有确定拒收项在带符号总和中的净费用。

## 原稿分界与验证

- **可由前置引理补足的省略**：每个被选位置的父条件、冻结网格端点、旧整除重复、同一原词碰撞交集和 all36 碰撞的 Θ 付款，以及上述严格子节点的三类实际计数与共同 Q 汇总，均已写入三份源码。原稿依赖见 `manuscript-body.tex:795–817,823–855` 与 `own-chen-table-insertion-chain-20261009.tex:129–175,253–355,388–403`。
- **仍待分析**：W1 的正素数限制 `cleanDebt`、W2 rejected pairs 与 higherPaidSwitched 在同一 ρ 下的正乘积费用减原 base reserve、固定读点与严格子节点上的有符号前代差、以及原收据拒收壳的兼容/抵消。单子拒收对当前上界是有利项，pair 拒收对上界是不利项。本文未输出这些项的统一小量界。未把 rootMask 后的 W2 母不等式当作输入。adopted seed、全 Member 与 430+11 共同 refinement 属其他责任，Y29 不由此推出。
- **形式化验证**：仅核冻结源码、定义、声明、比较方向、导入身份与文件散列。供应者未执行 Lean/Lake/LSP、stage、guard、producer、数值证书、CI，未改 continuation 或 main。REGISTRY 给出源码安装顺序与依赖。提交 T20 独审，核验后另行登记。
