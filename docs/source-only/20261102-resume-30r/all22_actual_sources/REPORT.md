# R06 / D04 — actual archive bank, positive fourteen and original thirteen current source

**结论：已供应原第四 bank 的具体 common-schedule 实例、实际 full-q signed source、原 cutoff 上的 positive-w 十四族密度包络，以及原十三族在十四族之后仍使用真实第六父树的完整 signed continuation。完整 All22 / 全87共同策略、十三族算术端点与最终 hdensity 仍 OPEN。**

新增两份 Lean：`P4AOriginalArchiveFourteenPositivePresieve.lean` 与 `P4AOriginalFourteenThirteenCurrentSource.lean`。`compiled=false`、`kernel_verified=false`、`formal_credit=0`；所有继承有限体保持 **UNEVALUATED**。只写本目录，没有 Lean/Lake/compiler、CI、guard 或数值 producer/replay、Git 操作，也没有子代。

仓库根为 `E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation`。H/I/J/K/M/O/P/Q/R 指该根下 `docs/source-only/20261102-resume-30*`；更早的 E 指 `20261028-resume-30e`。先读 R/BRIEF、DISPATCH、Q08/Q09 REPORT/REGISTRY、Q24/Q30 review；搜索 production、source-only 及显式 ignored `.lake/proof-continuation/source-reviews/drafts` 后才确定下述缺少的转换。

## 原稿核对与实际新内容

原稿 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` SHA256 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。已读 371–509、1327–1369，以及 `modules/global-positive-upper-completion-20261010.txt:55–127,185–281`。

这些段落要求：每次改动以**当前 parent**为基准；一个域上的强估计只替换一次；正 saving 可用合法子域；整个上筛树的 presieve projection 控制同一物理 rho。因而无需重做 Q 的 ordinary14 端点或 M 的原13/28918 integral 实例，也不能对两个 signed 源之差直接应用单树 projection。

| 新声明（统一 namespace `ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve`） | 实际供应 |
|---|---|
| `schedule`, `data`, `data_eq_original_heldData` | 将 Q 的 primitive `rows4/licensed4` 固定为 O 的 `originalRows4/originalAdmission4`；与 O `heldData e q (e/20) omega` 定义相同。原第五 archive、`m=475*q-1` 和祖先规则保留。 |
| `actual_fourth_geometry` | 从实际 `integerGeometryAccept` 的 soundness 消掉 caller `FourthGeometry`。不是把 Geometry 写进新的结构字段。 |
| `fourteenPolicy` | 原 literal14 pattern 在同一 `policy6(data e q omega)` 上的真实 rank-eight splice；不把它等同于 held `policy8` 或全87。 |
| `fourteenSourceChange` / `physical_fourteen_sub_current_eq_source` | 在实际 target-deleted `roughPrimeUniverse N cap w z` 上独立定义 occurrence-list continuation，证明它等于实际新物理 rho 减当前第六 parent。完整模数 test `G`、small beta 的正负选择、incoming sign/mass、remaining carrier 和 List multiplicity 全部保留。可直接取 AP/count/mean/density test。 |
| `original_fourth_fifth_attached_sources` | 对具体原 bank 消去 Geometry，得到第四及第五 `sourceChange` 分别为原第四减原第三、原第五减原第四的 signed source。对任意 presieve 与完整 modulus test 成立；旧 gain 出现一次，未利用 signed coefficient 单调性。 |
| `raw_current_sub_fourteen_eq_original_charge` | 将同一具体 `policy6 − fourteenPolicy` 的 raw density 识别为 J 的独立 original14 charge，方向、父 cap、模式均未改变。 |
| `exists_original_bank_positive_fourteen_schedule` | 无 rows/licence/Geometry、endpoint、beta error 或 density 前提，给一个实际 positive-w 包络，详见下段。 |

终端结论使用原 `z=N^(19/96)`，不是较小 root cutoff。`w=N^(nu*beta^2)>1`、`L=N^(nu*beta)`，以及

```text
normalize(physical fourteenPolicy at w)
  < normalize(raw actual policy6 at w=0)
      - 1222997719565324892497827 / 2^96 + eta.
```

其中 `normalize x = x*log(N)/singularSeries(N)`。完整选择顺序是

`nu, eta, betaMax → beta, n, e0 → e, omega → q, N0 → N, cap`。

同一 `FourteenHistory(schedule e q omega)(width n)` 被保留。Q 的源端点在这个实际 schedule 上花 `eta/2`。生产 `ActualFirstExitDensityProjection.exists_actualSmallRoughRho_density_le_full_reserve` 在 **同一整个新 fourteenPolicy** 上供应另一个 `eta/2`，且其 beta 与阈值对所有后来 retention policies 统一。然后用已证明的 raw current-minus-new 恒等式消去新树 raw density。没有给正 w charge 自身强加不成立的 ordinary 下界，没有删除 beta-width/absolute-mass correction，也没有对旧/新树分别套上界后相减。

这个 beta 半预算是**本局部包络内部的一次支出**。最终 R09/R10 若使用本包络，必须与其全局 beta 选择统一并去重；本任务没有再从 `u_d` 或 `u_c` 认领一笔总支出，也没有宣称编译后的 rho 已获此界。

## 原十三族的真实 current-parent 来源

第二份源码使用 namespace `ImbalancedChen.P4AOriginalFourteenThirteenCurrentSource`。它消费原生产 `OriginalAscendingThirteenCellOwnership.StrictRows` 和 K 已有原 bank；没有再造 M 的原13/28918 endpoint，也没有定义一棵会在十三族域外清除旧十四族的新 policy。

原十三族 `ascendingThird` 给 `t 1+t 2<mu`，十四族 `CellGuard.old_descending` 等价于 `mu<t 1+t 2`。这个严格互斥直接来自原具体条件，故没有 caller 的 separation/cap-equality 前提。

| 新声明 | 实际供应 |
|---|---|
| `original_thirteen_excludes_fourteen`, `fourteen_level_inherits_on_thirteen` | 原十三族上十四族 guard 必为假，literal family cap 真正退回同一 `lambda6(data e q omega)`，经 rank-eight/rank-six ancestor 的嵌套恒等式识别。 |
| `fourteen_decision_eq_current_on_thirteen`, `fourteen_signed_continuation_eq_current_on_thirteen` | 不只根节点：每次后来选素数都保存原 rank-eight ancestor，整条后续 signed recursion 与真实 `policy6` 相等。终端 test、incoming sign/mass、remaining carrier 和任意相同 prime weight 全部保留。 |
| `fourteen_frontier_eight_eq_current`, `original_thirteen_selected_list_preserved` | 原 K/G 的 `selected (.ascending19 i)` occurrence List 精确保持，包括重复次数。此既有载体使用 `h(p)=1/(p-1)`，没有把它当物理 unit-weight 载体。 |
| `original_thirteen_bank_continuation_preserved` | 从该真实 selected List 的 membership 推出 rank=8 和原十三族 StrictRows，再应用完整 continuation 恒等式；incoming mass 与后续 reciprocal weights 成对保留。 |
| `originalThirteenPhysicalList`, `original_physical_list_iff_prime_bank` | 在真实十四族 unit-weight frontier 上按**同一原** `bankRegion` 选择；证明等价于原 half-open `primeBox` 条件。Primality、target deletion 来自实际 frontier，不假设任意 log tuple 是素数源。 |
| `original_thirteen_physical_list_preserved`, `original_thirteen_full_q_continuation_sum_preserved` | 这个物理 List 与真实第六父树上的 List 相等；逐 occurrence 的完整 `attachedLeafTest N cap 1 w L G` continuation 也相等。`w,z,L,G` 任意，small beta 的正负选择及完整模数保留。 |

最后一个等式是原13来源在十四族之后的 **same-current/full-q** 事实。它不提供原13的新树增量下界，不把解析 `selectedSaving` 直接等同于物理密度，也没有声称所有十三族 bank states 已支付 parent-defect 或 residual error。若 R03 的最终原策略继续改动这些 continuation，还须由其实际 chronology 证明相应保留，不能只引用本局部 two-stage 恒等式。

## 原 bank 的准确范围

O `adopted87_policy/P5OriginalFourthFifthSourceInputs.lean` 已有完整 source loader、`originalFourth_parse_exists`、`originalFourth_wire_source`、`originalRows4` 和 `originalAdmission4_geometry`，故没有复制第四 bank。

实际 payload 是 O `provenance/original-fourth/FourthRows17LE.bin`：62,885,159 bytes，SHA256 `561f5dc9ff2f6d64ba739de830511f6f68bf1f7be0c724655a8435c7edb914da`。`originalFourth_wire_source` 的源码结论为 List 长度 3,699,127 以及 encode-back；这不是 `originalRows4` Finset 的无重 cardinality 结论。R06 只读取原字节计算 hash，没有执行解析、长度 guard 或逐行几何测试。

`originalAdmission4` 仍是原 wire row 的具体 `integerGeometryAccept=true` 谓词。它给实际许可证的几何 soundness，却没有证明全部原 wire rows 都通过测试、完整 analytic H/h licence 或 gain1 的保存端点。新实例消去的是 Q 的**任意 primitive 参数与 caller Geometry**，不能据此把完整原第四 numerical saving 或所有旧高秩策略改为已完成。

I `common4_source/P5OriginalCommonFourthSourceLedger.exists_original_fourth_fifth_positive_ledger`、H `P5OriginalArchivePositivePresieveGain` 已有原第四/第五 integral 的 positive-w 供应。它们仍有真实源误差与 laterRawLedger，R06 没有再写同一消费者。需要时可直接把本 `data` 用作其实际参数；这不自动支付第五 old-branch defect 或 actual64 reserve。

## 22 项来源及“一次”规则

`ALL22_SOURCE_MAP.json` 逐项保留原 `global-selected-numeric-completion-20261010.json` 的 22 个 id/source/field/value 字符串、来源文件 raw hash，以及本轮对应范围。它是来源目录，**不是 Lean 实例或数值验收**；没有从这些 JSON 的 PASS 字段推导数学结论，也没有求和、比较或重算数值。

| slot | 原来源作用 | 对共同策略的严格状态 |
|---:|---|---|
| 1 | 原第四完整改进，替换旧 partial/tail | 本轮提供原 admission-filter bank、真实 signed 保留；原保存端点与全部许可仍未供应。 |
| 2–3 | 旧第五 whole-parent subdivision replacement；新第五 disjoint cover | 原 archive 和 Q 完整扣债包络复用；oldBranchDefect / indexedActualReserve64 由 R04/R05 负责，未消费未交结果。 |
| 4 | expanded old sixth replacement | held constructor 的十一 cells 不能代表此项及全部旧第六 schedule。 |
| 5 | above-mu second coarse | Q actual pair bridge 保留实际 coarse/omitted 差项；全域付款归 R07。 |
| 6 | above-mu third | P before-third restoration/current-frontier identity 已写；最终源与误差仍须接同一完整策略。 |
| 7 | 十一 sixth cells 的 final log replacement | 不是在旧同域估计之外再加一个 gain。既有 literal eleven semantics 复用；全旧 sixth chronology 未闭。 |
| 8–10 | descending33、ascending34、descending34 current-parent 改动 | 独立 source/physical 局部稿不构成完整同策略装配。 |
| 11–13 | lower-complement intermediate difference 与 local corrections | 必须是原缺少的中间差；不能加第二个完整差。共同实际 source 仍待总装。 |
| 14 | 四个 nonsingleton sixth cells | 原稿要求只在 eighth-family stage 计一次。 |
| 15 | 原 eighth radial 同域 max replacement | 与旧 seed estimate 互为替换。 |
| 16 | 原十四 ascending cells | Q ordinary endpoint 与 O common history 已存在；本轮新供具体原 bank 的 positive-w local envelope / attached current-parent source。 |
| 17–18 | 十五 descending；十五 unequal final log replacement | 既有局部 source/chronology 复用；没有声明已是同一全87物理树。 |
| 19 | 原十三 ascending-pair minorant final log | M 无参数 `original_endpoint_le_selectedSaving` 已有完整原13/28918实例。本轮用 K 原 bank 证明十四族之后的真实 current6 continuation/List 保持，并另建同原 bank 的 unit-weight full-q 物理 List；同一最终树上的 positive-w arithmetic bound 尚缺，不能重造 M endpoint代替。 |
| 20 | 二十九 first-failure final log replacement | first-failure 是足够 minorant 的失效，不能当真实 upper-tree exit；实际全87 source/history 归 R03。 |
| 21 | 11026 winner9 seed 上 curvature over adopted-log increment | 原 JSON 明确不是新 cap/domain；仅新下界减已采用下界。 |
| 22 | 同一11026 seed 上 mixed over adopted-curvature increment | 原 JSON 明确 curvature/plain 不能另加；不能将它当第二次 cap raising。 |

原十九族和 11026 winner9 seed 不混同。slot19 用原 mask138、A23-low minorant 和原13 selectedSaving；slot21/22 的11026只是 slot18 中原 seed 的估计加强。四正项、third-tail 单次替换和 exact rational slack 的生产模块都已存在，R06 没有再加一个 generic All22 ledger、任意 source 字段或以目标 endpoint 为前提的包装器。

## 尚未消除的真实边界

1. 本轮终端物理树是 `fourteenPolicy`，其 parent 是已有 common constructor 的实际 `policy6`。它没有与 held `policy8`、完整全87或 R08 新有限化树相等。把局部正 saving 用到一个不同最终树，仍须证明真实 chronology/source 保留；数值端点相同无效。
2. 全22对应需要完整旧六阶改动、各 eighth 域的 current-parent 增量与所引用保存端点在**同一**实际 causal policy 上成立。现成 P telescope、有限 signature、生产 scalar ledger 都不供应这个实例。
3. 十三族的 analytic Q96 endpoint 已写。本轮消除了十三族在十四族之后的 source separation、current-parent 与两类 frontier 对应前提；仍缺从该解析 selectedSource 到同一实际普通/正预筛 signed arithmetic **下界**的完整供应，而不是 full polytope coverage 或再构造28918 moments。
4. 完整 buffered approximation、所有 changed/mixed cells、compiler、两笔独立总 reserve、原 rho 的支持/PP 和最终 hdensity 仍开放。本轮未消费任何 R03/R04/R05/R07/R08/R09/R10 新源码。R08 后已通报冻结的两窄供应是 actual original4/5 的 buffered signed gains 及 held compiled support，明确没有全 lambda6/全87 finite caps，不能用来关闭本边界。
5. inherited source-only imports 仍需精确部署。Q 链要求 P 的同名 `P2Winner9ActualEightSimplexMoment` 正向 `integral_const_mul` 最小替换，不能回到旧冻结版本；新 module 不认证递归 import closure 或任何有限 guard。

困难分类：(2) 本次的具体 bank 参数消去、full-q attached source 转换、整树 positive-w 推导及原13/14 current-continuation 对应是可填的遗漏步骤，已给源码；(1) Lean/API、import materialization 和资源仍待正式验收；(3) 尚未发现证明原稿反例的证据，不能将当前模型缺少 all87/All22 实例当作原稿反驳。

## 验证及交付

仅作源码/API阅读、声明/import定位、原字节 SHA256 与 metadata/JSON检查。`collect_source_metadata.py` 只读取字节和文字，复制原来源字段，记录 hashes/行号；它不运行 Lean、proof guards、producer 或任何积分/预算计算。

`REGISTRY.json` 登记两份新 module、直接 import 的精确 source 路径、关键复用/原始输入、声明行号和 raw hashes、实际消去的前提与剩余依赖。它不冒称全传递闭包已核。最终 raw hash 以 registry 为准；本轮新增绿色或 formal-credit 节点数为零。
