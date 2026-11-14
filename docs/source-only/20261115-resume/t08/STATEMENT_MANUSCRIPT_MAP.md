# T08：真实反馈 Member 的原根收据在首次附素数处退出

两份新 Lean 候选源给出原 U3/U4 的一个完整有限计数结论：在实际 `rootHistory` 的任意位置 `o`，原根收据与该位置普通源的交集满足

\[
\operatorname{originalReceiptLane}(N,p,D_o,z_o)
=\begin{cases}
\operatorname{originalReceiver}(N,p),&o.\mathrm{current.old}=[p],\\
\varnothing,&o.\mathrm{current.old}\ne[p].
\end{cases}
\]

这严格是 `if old=[p] then originalReceiver else ∅` 的分段恒等式，未假设也未证明 `originalReceiver` 非空。若原 receiver 为空，两支都为空；因此不能改写成 `(lane=receiver) ↔ old=[p]` 或 `(lane≠∅) ↔ old=[p]`。

这里 `D_o = old.tail.prod`，`z_o` 是该位置自己的物理 cutoff，`Q` 是原 RootKey 的 `cellQ`。第二支的普通源没有消失：其计数**恰好等于**此前 T17 定义的 `rejectedChild` 基数。

这是 root-mask 继承路线的精确对象识别，不是 `h34`、全 Member 解析许可或 430+11 realization 的闭合。源码未运行 Lean/Lake/LSP，formal credit 为 0，尚无独立源码审查。未改旧 packet、原稿、Git 引用或远端；没有运行 helper、guard、fixture、候选证明或数值 producer。

## 原稿和既有后续

原稿固定 commit `9731290e8f53cffda44129906cde6a965eaa869b`：

| 原稿位置 | 本次对应 |
|---|---|
| `paper/source/manuscript-body.tex` 795–817 | 原正标记族、同一 Q、真实 alpha 与完整/selected square 均沿用；本包不把任意 rootMask 子族直接授予同一 Theta 估计。 |
| 同文件 819–855 | 70 W1、36 W2 的固定项与附素数反馈必须区分；逐项实际 LocalDomain 用于首次退出证明。 |
| 同文件 857–877 | `children` 只展开当代实际赢家，`ChosenPath` 使用递减 fuel；本包对每个固定 generation 分别给等式。441 层误差传播及共同光滑细化未供给。 |
| 同文件 887–892；`own-chen-table-insertion-chain-20261009.tex` 388–403 | 根的 `max(2,L/a)` 给 `L ≤ a*s`。`a=417/5000` 保持原常数，结构 clamp 不删除。 |
| insertion-chain 129–175、222–244 | 保留正标记、同 Q、原完整/selected 过滤和真实 ancestry；没有替换 Member family。 |
| insertion-chain 253–355 | 原 BH、W1、W2 的窗和物理 ceiling 保证首次附加素数不超过 N^a。 |
| `1_+_1.748_lean_proofs/main.md` 484–602 | 对“完整原始 U3/U4 selected-count 历史绑定到 Member”新增此有限 count 分类；全 native proper/equality/inherit 质量、relative own-Theta、430/441 与 h34 继续黄。 |

已核对的后续包括：本地镜像 `chatgpt/p5-h34-full-tagged-actual-fin-20261112` 的固定 head `001d139e667eb5cb42f1e9ca8f02de221b00db5c`，其中 `547e997645225e528d8d34a75cb5305ecee87c9b` 的 `U4ActualFinDoubleTag` 已给真 Fin 双标签权重，明确未安装完整/selected/inherited filter。本包不重复该结果。T17 五源及 successor、T19 真实窗和净账、T23 all-ell 适用性补件也已核查。20261113 本地 publication-index snapshot 保留这些包；本任务未刷新远端分支，因此不声称穷尽此后未同步的源。

## 推导

1. 根 `old=[p]` 且 `s=max(2,L/a)`，所以 `s≥2`、`L≤a*s`。在首次附素数前，retained 不改变物理 query；W1/W2 fixed 使用不小于实际 target 的 anchor，故保留这个不等式。此处使用原 actual request，不以任意 Member 假设代替。
2. 对首次 BH，原闭域给 `s−1 ≤ L/x−1`，于是 `s*x≤L≤a*s`，即 `x≤a`。对首次 W1/W2 singleton，原开窗给 `x/L < 1/target`，并有 `s≤target`，同样得 `x<a`。W2 pair 用原四域的较小坐标，`pairHalf_below_target` 来源是原 36 行的 `s≤phi3`，不能仅靠弱 `W2Geometry` 的 `1/2` 上界。
3. 每条实际边的素数 q 与 N 互素。若 `log_N q=a=417/5000`，则 `q^5000=N^417`，所以 `q|N`，矛盾。因此连 BH 的闭端也满足 `q<N^a`。这是精确算术排除，不是零测度删点。
4. 首次附加后，该 q 永久留在原有序 old 的尾词中。每一步只追加真实整数词，pair 仍按 `[large,small]` 追加。任何原 root receipt 需要 `N^a`-rough，故与包含 q 的前缀不相容。后续任何 full/selected inherited 筛选只能继续限制这个已空交集。
5. 未附素数的路径可以有正深度（fixed 或 retained），所以不能用 `path.length=0` 替代 `old=[p]`。对这些位置，真实 `Q=B*N^L` 和上述 cutoff 不等式给 `z≤N^a`，尾乘积为 1，故 lane 恰为整个原根 receiver。

## 新声明与范围

| 新声明 | 结论 |
|---|---|
| `prime_lt_original_cutoff` | 实际互素素数不可能落在原 rational root cutoff 的闭端。 |
| `child_first_receipt_exit` | 每个当代实际选中边：保持空尾和 cutoff 上界，或追加严格小于 N^a 的真实素因子；涵盖 BH/70 W1/36 W2。 |
| `actual_history_receipt_state` | 该二分在两个原根的全部真实 430 历史位置成立。 |
| `actual_member_lane` / `actual_member_masked_count` | 原根 lane 与相应 frozenCount 的精确 if/empty 分类。 |
| `appended_member_ordinary_is_rejected` | 每个已附素数位置的普通源等于整笔 rejectedChild，而非已付小误差。 |
| `masked_position_sum` | 对同一代实际位置任意子集 S，原 masked count 等于原 receiver 基数乘 S 中 `old=[p]` 位置的原正 mark 总和。 |
| `complete_level_masked_count` | 对每代 G=0,…,430、每个原 root key，完整位置有限和的同一等式。 |
| `selected_box_masked_count` | 对实际 `selectedLevel` 与原 owner/path/box 过滤后的同一等式。 |

`rankOneWeight` 不设为 1，也不合并重复位置。U3/U4 标签各自取自己的 Q、history、owner 和 mark；重叠标签仍分别应用并相加。无额外渐近阈值：有限等式对全部 `N≥2`、`0≤tau≤1/12`、`1/(n+1)≤11/384` 同时有效。这里的“已附素数”不是 native 几何的 proper/equality 分类。

## 直接影响和仍欠内容

把 T17 的 rootMask 在每一代原样传播，然后对 masked 负子项直接使用普通前代 h 下界，不能得到稿中的反馈归纳。在所有真实已附素数位置，该 masked 项实际上为零，普通项则是整笔补集。若符号为负，则将 `−masked` 改为 `−ordinary` 必须加回整个普通补集；它没有被本包估成小量。正 Theta 与正 mark 依旧属于普通族，不因 root-mask 交集为空而归零。

这没有否定原稿采用的另一条路线：只在正根处比较到较低 cutoff，然后在整套普通接收者内保留全部有向母式、解析 seed/base、同 rho 分布及原完整/selected 支持，完成实际前代归纳。上述普通族的完整算术许可和跨图 winner/owner 对应仍需供给。没有引入 `h34` 或期望 count inequality 作为假设，也没有用 toy family 规避该缺口。

本包不依赖新增 half/J6 包；不提供 7/32、signed moving-residue、medium/no-medium 分布、全 PP、relative own-Theta 或 430+11 realization。所有这些状态保持开放。
