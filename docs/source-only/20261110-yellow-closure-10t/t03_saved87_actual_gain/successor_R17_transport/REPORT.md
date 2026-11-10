# 原始 87 个第八层单元在 R17 修正及完整第三层策略下的带符号增益

四个原第六层 nonsingleton 动作的旧比较是 `R17=57/64−3(t₁+t₅)/2`。同一批动作保存的第三层历史比较是 `R0=(1+t₁)/2`。原第八层每个单元的包络已经包含 mask 17，故可以保留原 87 个核及原八个账目值。这里给出完整第三层树上同一原模数的第六层系数减第八层系数的精确等式，以及普通密度和正预筛的推论。四份新 Lean 源均待远端核查。

## 逐族原对象

取 `A(s)=(1+s)/2`、`D(s)=57/64−3s/2`、`v=min(A,D)`、`W=153/256−3t₃/8` 和 `η=10⁻⁶`。表中坐标从 1 开始，原 source 索引从 0 开始。各行旧比较 `R` 上界覆盖 `W` 和全部 63 个非空前六坐标子集帐篷。索引 7 的径向分解以及索引 41 的两次逐单纯形增量保留各自原单元。

| 原 source 索引 | 原族 | 原第八层旧比较 R | 原新端点 M+η |
| --- | --- | --- | --- |
| 0–14 | 第一个 ascending 半面及 seed 7 | D(t₂+t₃) | A(t₁+t₈) |
| 15–29 | descending 半面 | D(t₂+t₃) | D(t₁+t₈) |
| 30–42 | 9A，含 seed 41 | A(t₁+t₄) | A(t₂+t₄+t₈) |
| 43 | 50A | A(t₂+t₅+t₆) | A(t₄+t₅+t₆+t₈) |
| 44 | 50D | D(t₂+t₅+t₆) | D(t₂+t₃+t₈) |
| 45–57 | ascending pair 的 13 个原单元 | A(t₁+t₄) | A(t₂+t₄+t₈) |
| 58–69、70–76、77–86 | H3、H5、H7 的 12、7、10 个原单元 | A(t₁+t₄) | A(t₂+t₄+t₈) |

每个单元均独立在原 `left_masks/right_masks` 或命名原仿射行中找到 mask 17。`REGISTRY.json` 列出 87 个具体索引、字节指纹、字段及其来自原发布件的路径。58 项与已发布 ZIP 的成员逐字节同哈希。其余 29 份导航文件由该 ZIP 对应的原 `cell.json` 中的 `bindings_sha256` 绑定。这里核查的是原字段与原字节来源。实数全集上的不等式来自 `P4AOriginalFull87SourceDictionary.source_all_old_tents` 的原仿射行证明以及每一家族的坐标同一性。

原稿依据为 `eighth-prefix-family-20261009.tex` 第 6–40、106–118 行，`eighth-unequal-analytic-union-review-20261009.tex` 第 17–39、89–119 行，`eighth-third-minorant-analytic-review-20261009.tex` 第 44–72 行及 `eighth-history-first-failure-analytic-review-20261009.tex` 第 19–43、64–89 行。其中 unequal union 第 94–99 行明确要求可能重叠的四个 nonsingleton 动作留在原第六层树上。所查原始 Python 生成和独立复核文件名、哈希均在清单。

## 四个 R17 动作与真实父层

`sixth-nonsingleton-independent-20261009.tex` 第 12–27、54–89 行分别给出原旧包络、历史下界、原前驱和有符号积分。`sixth-nonsingleton-freecap-20261009.witness.json` 的四个原记录采用 pattern 1355、1867 和 mask 33 的两个新面。每个记录都包含 `winner17 descending`、`R17 above R0`、`M above old R17` 三个命名原行。原行 3 给出 `t₁+t₅>25/128`。因此在该动作与原第八 source 的重叠处，`R17=D(t₁+t₅)=v(t₁+t₅)≤R`。新动作自身还满足 `M₆<v(t₁+t₆)≤R`。这两步分别控制旧比较和新端点。`P4AOriginalR17EighthParent.pair17_on_overlap` 明确写出这一区分。

原 saved 六层的 632,104 行、十一组实际 `PhysicalCell` 以及 19 个 later 动作都仍在程序中。原八次 chronological max 用各动作自己的 selected tent 上界，R17 四个动作按修正后真实 gate 进入；含量化的 `cap6` 对每一条真正 `accepted` 的动作另有 `rounded+width≤v(selected sum)`。同一第五层 old+new union 的第四、第五候选受各自原子集 tent 控制，继承的第三层受六个原始第三层分支连同 `W` 控制。`compact_parent` 给出未量化完整第六层的上界和实际量化第六层的上下界。

原 trim 的共同第一层和第三层词由 `common_history_on_trim` 给出。原 mesh 已实现 `supported`，且四个奇历史都严格低于其真实第三层 cap。完整第三层策略在这个旧 owner 上有 `capValue=levelExponent`；后取的 `ω≤a` 保持 activation 和精确标量。于是 `root_on_old_owner` 给出包括 lower 模式在内的根相等。它只在已选原词上使用。原第七历史进而给出 `t₈<P−S₈`。原新有限 cap 仍在 `R<Mfinite<S₈+3t₈`。 `compact_kernel` 把原 `4(M−R)/((R−S₈)(M−S₈)∏tᵢ)` 接到实际同一 `P,Mfinite` 的 reciprocal difference 和已有统一取整损失。

## 逐模数等式与最终量词

`P4AOriginalR17EighthSignedTransport.coefficient_difference` 对每个自然数 x、每个 rough carrier 给出原 Möbius 系数差相等。若 x 的第八祖先选中某个原动作，完整素因子词每个长度至少三的前缀都读取同一第三祖先，长度至多二时使用原 first-stop 初始策略。两树在所有后续深度也读取该同一持有值。若第八祖先未选中，则该词后续每个前缀都没有第八动作，各自实际第六层和第八层相消。规范词的逐步布尔读数给出相同保留支集和带符号系数差。`raw_difference` 将该等式在包含全部剩余因子的同一物理模数集合上按 `1/φ(x)` 求和。该论证不需要两个完整第三层程序处处相等。

`P4AOriginalR17Full87SavedEndpoint.original_ordinary_source` 和 `original_ordinary_saved` 分别给出原 87 项真实 source 积分和原槽 15–22 的数值，均在同一 `d⁺`、同一 (N)、同一 `ω≤a` 的完整第六层减原第八层上实现。原 `Scheduled` 顺序为 `r,n,e,q,a,N` 的 cofinal 选择，再对所有 `ω≤a`、`N^μ≤z≤cap` 成立。数值左端为

```text
(3111307568597708509491143 + 77410436074156865471 + 481322793305152847935) / 2^96.
```

两个增量仅作用于已收取的索引 41。原 87 项的每个量纲、单纯形、因子、Q96 floor 和完整积分沿用原已冻结源。`P4AOriginalR17SameCutoffPresieve.original_source` 和 `original_saved` 在给定正 `a≤1/100` 及任意 `βMax>0` 后选单一 `0<β<min(1/8,βMax)`，使 `ω=νβ²<a`。真实第八层系数使用该 `ω`，正预筛使用同一 `w=N^ω, z=N^(19/96), L=N^(νβ)`。投影一次，得到完整新正预筛密度小于完整旧第六层普通密度减原增益加任意 `ε>0`。T05 将原 ordinary 端点用于带自身一次投影支出的同系数 compiler。

## 核验边界

这次发现的是原 S09 的四个第六层比较查表错误以及相应两处语义、仿射程序和后继证明的修正。原第八层所有已查字段与包络均覆盖修正所需的 mask。数值误差项沿用原趋零顺序。T05 的四个同名替换必须成组安装并重新展开依赖。冻结的旧路径及既有运行标识不构成这个新图的远端证据。

原档案 357 个输入和细化种子的绑定已在旧 `FINAL_REGISTRY.json` 归档。新增确证只读原始字节和文本字段。本包没有执行 Lean、Lake、LSP、档案有限核算、原数值程序或 CI。完整依赖图的远端 kernel、声明类型、公理及资源核验仍待执行。G8–14 各自的六层数值和全局计数由其各自账目处理。
