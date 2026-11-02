# Q24 — saving16/saving19 几何与实际端点独立复核

**判定：Q08 局部 `SOURCE_REVIEW_PASS`；Q09 精确复用及实际实例化审计 `SOURCE_REVIEW_PASS`；完整传递链、kernel 验收与 P2.5/P2.6 全节点仍 `HOLD / OPEN`。** 未发现必须修改本次作者源码的新缺陷。`compiled=false`，`kernel_verified=false`，`formal_credit=0`；全部有限证明体保持 `UNEVALUATED`，资源可行性未测。这里的 PASS 确认实际源码、前提边界及推导方向，不认证保存整数或有限 guard 的真值。

2026-11-02，审阅者 `/root/q24_review_saving_geometry`。根目录 R 为 `E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation`；下文 J/K/M/O/P/Q 分别为 R 下 `docs/source-only/20261102-resume-30j` 等同名批次。只写本报告；没有修改作者、生产、旧批次或主表，没有 Lean/Lake/compiler、CI、数值重放、有限 guard 求值、producer 执行、Git 操作或子代理。

| 复核项 | 精确结论 | 未被关闭的范围 |
| --- | --- | --- |
| Q08 `saving16_scope` | 原 Q96 下界连接到 O 的同一实际 archive/history schedule；原 histories、第四/第五 signed 恒等式和 trim 结论均保留。 | 原第四完整 bank/licence 实例、完整 buffered/all87 策略、positive-presieve、signed compiler、两笔 reserve 及全局装配。 |
| Q09 `saving19_instance` | M 的原 13/28918 archive → `fullMomentRow` → Q96 → 原 `selectedSaving` 已有具体源码，终端定理无参数；Q 正确选择零新增 Lean。 | 全部 loader/finite/algebra 证明体与传递安装验收；同一实际因果策略和算术编译等全局义务。 |
| full cell/facet/active-eight tracker | **不是这两个正 saving 下界的必要前提；应撤出其必要黄叶或单列为非依赖的较强 producer 认证。** | 不将完整 polytope/active-basis/face-lattice 穷尽本身改蓝，也不放松任何负 cost 的全域覆盖要求。 |
| P 两个最小替换 | 保留既有同名模块选择；逐字节核对成立。 | 修复不是整个依赖链的 kernel 接受，本任务不给重复证明信用。 |

**原稿与 producer 的实际要求。** 已先读 Q/BRIEF，P `saving16_pulling_ownership`、`saving16_weak_face` 的 REPORT/REGISTRY 和 `reviews/t23_review_compact_s16.md`，再读原稿 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:435–449,1354–1369` 及原 producer。原稿 SHA256 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。435–449 保留实际第六 parent ≤ R6、系数 4、全部八个坐标因子、cutoff `53/13824`、所有 full/selected-complement squares，无 Chen quarter 或排序 factorial。1354–1356 明确允许正 saving 使用合法子集；1364–1369 的完整 active bases、boundedness、face lattice 与 pulling 是更强的原计算过程描述。二者并不矛盾。

原 `eighth-prefix-family-20261009-exact.py:39–89` 确实先枚举 selected active-eight 系统、核全部原不等式、构造 facet/face ledger，然后按 `max(face)` 与排序 maximal intersections 的 recursion 写出有序 `vertex_ids` 和逐行 Q96 floor。原 `eighth-prefix-cell-independent-20261009.py:138–150` 的无序 simplex-set 比较不能单独证明保存列表的顺序；作者 producer 的 `enumerate(tri)` 才支持 O 的有序绑定来源。saving19 的 `eighth-unequal-parent-nine-20261009-minorant-exact.py:46–107` 使用相同的原 max-pivot 机制；`eighth-third-minorant-extension-20261009-exact.py` 与 `...-family-exact.py` 选的是 `A23/s23_low`，并使原 cell4 只计一次。原 moment adapter 保留 degree6/Q80、degree3 exponential、`max(old,new)` 的同域替换。上述均作为文本读取，没有执行或解析数值 witness。

**覆盖范围的决定性证据。** 对两组原保存支持 T_r，现有源码构造 U_r，仅删除已证明零测的 source walls/frontier 与同 cell overlaps，得到 U_r 与 T_r 的 AE 相等、U_r 两两不交、并集 U 包含于原合法 source C。原 density 在 C 上非负，且可积。因此所需方向是

`H_Q96 ≤ Σ_r ∫T_r density = ∫U density ≤ ∫C density`。

这里没有一步需要 `C ⊆ U`、`C = candidate-facet polytope` 或 active-eight 穷尽。它仍然需要每个实际顶点的全部原 gate 合法性、实际支持、无重计及每行 floor 的正确绑定；这些真实依赖不能随强覆盖项一起撤去。该合法子集论证也不允许直接删除有限 signed arithmetic 的负补项：saving16 的 O negative-part payment 另行处理它；saving19 本次仅落到解析 `selectedSaving`，没有暗推完整算术 charge。

**saving16 的现成几何与 Q08 新连接。** O `saving16_pulling_ownership/P2OriginalSaving16PullingFaceInduction.lean:36–49` 的 `Shape` 是 primitive 顶点-ID incidence 与 child antichain，不含几何 coverage 或 disjointness。`:91–113` 从原 gate 非负及 facet 零集得到 omitted pivot 严格正；`:120–209` 的 separator 归纳分别用 `g(p)*a-a(p)*g` 与 `h(p)*g-g(p)*h`。非零 witness 与两侧符号均推导出来。

O `P2OriginalSaving16PullingOwnership.lean:99,105,154,206` 将该归纳绑定到 M 原14/39741 saved rows，保持 IDs `0..14 except7`、实际有序 rows/Nodup、96 原 rows 与原 facet incidence。M `saving16_q96_endpoint/P2OriginalSaving16SimplexBinding.lean:26–55` 的 transpose 与 determinant 对应真实物理边矩阵；`:117,126,141` 给原 support inclusion、逐 simplex Q96 与原总端点。M archive 的 `original_counts:317`、各 finite guards 和 aggregate 仍未求值，不能以 hash 代替它们。

O `P2OriginalSaving16OwnedIntegral.lean:96,107,129,140,153` 依次提供 owned supports 的不交、AE 相等、有限积分相加、原 source 积分比较和

`1222997719565324892497827 / 2^96 ≤ ∫ region sourceDensity`。

这些都是已写源码，不是 Q 待重做的证明。O 虽只使用 M19 `OwnedSource` 的中性 evaluator/interpolation/affine-null API，却导入整个模块；其 Original28918、parser 等依赖仍在实际 import 图中，不能按“只用中性定理”删掉 HOLD。

共同 schedule 也已有具体供应：K `saving16_glue/P2OriginalSaving16CommonOldPolicy.lean:177–239` 从实际 historical mesh 和原 constructor 推出 retained14 的 firstStop、第三 support、H1/H3/H5/H7、真实 `H7 < lambda6 ≤ R` 与旧第五 gain；这些不是 caller 提供的 history/current≤R 前提。O `all22_common_history/P4AOriginalCommonArchiveSchedule.lean:68–129` 选择同一 grid400-aligned `m=475*q-1`、`chi=e/20`，调用 O 全 family 下界，并保留原第四/第五 signedTest 差的恒等式。不能再笼统写“十四组共同历史源码不存在”。

Q08 `saving16_scope/P2OriginalFourteenCommonScheduleEndpoint.lean:44–88` 唯一新增的是上述两个现成结果的具体连接。它复用同一 n,e0,q,N0、同一 `s.data` 和原全部结论，最后仅使用

`(sub_le_sub_right historical_endpoint_le_source_integral epsilon).trans_lt hlower`。

完整量词仍是 `rows4/licensed4/Geometry, epsilon → n,e0 → e,omega → q,N0 → N,cap,z`；保留 sufficiently large even N、`N^mu≤z≤cap`、`lambda6 s.data N`、`policy5 s.data N`、`literalPattern`、`log N / singularSeries N`、ordinary `w=0` 及原 `<epsilon/4` trim。没有 caller source-integral、history realization、coverage、补项可忽略或端点假设。新增分析估计为零；消除的是已写原端点到已写实际共同 schedule 的组合缺口。

这一结论仍含原 primitive `rows4`、`licensed4` 和 `∀ r∈rows4, licensed4 r → r.Geometry`。它不是完整原第四 bank 的实际实例化，也没有把 literal14 policy 等同于 held `policy8` 的完整87策略。O weak-face `P2OriginalFourteenWholeFamilyLower.lean:139–215` 只证明实际有害负部可任意小，进而 signed complement > −epsilon，不是其绝对值趋零，也不是每个有限 N 非负。其`:220–252` 与 M 精确 signed partition 合成后，Q 仍只消费 ordinary w=0 结论；positive-w/beta-width/absolute-mass 与 reserve 不随此关闭。

**saving19 已经是实际13/28918 source 实例，不是 caller 证书接口。** J `saving19_floor/P2OriginalSaving19SourceMeasure.lean:222–244` 定义 `selectedSource := ⋃ i : Fin 13, cell i`、`selectedSaving := ∫ selectedSource conservativeDensity` 并证明原13 strict cells 的可加性。生产 `OriginalAscendingThirteenCellOwnership.lean:67,96–108` 的 cell 与 chosen-plane separator 是实际来源。`selectedSaving` 不是任意实数或可替换的集合。

| 所需实例化 | 已核具体源码 |
| --- | --- |
| 原13 geometry 与13 moment 文件、原顺序/ID/行数 | M `saving19_original28918/P2OriginalSaving19Archive.lean:22–52,205–206,230,249,260`；完整文本 loader、total parser、`.getD` 分支有 closed success 身体，原 row index 是 sigma 索引。 |
| 实际物理行与有限字典 | 同目录 `P2OriginalSaving19Original28918.lean:106,153,189–206,222–258`；第一原顶点作 base，其余八条边作 columns，填原 determinant、physical rows、volume、mass、means、tops。 |
| higher moments 的旧解析字段 | M `saving19_higher_moments/P2OriginalSaving19HigherMoments.lean:416–465`；`AlgebraicMomentRow` 只要求实际 rational encoding，由 `higherPowerMoments_of_encoding` 填旧 `MomentRow` 的积分字段。 |
| 实际 `fullMomentRow`，非任意 caller 家族 | M `P2OriginalSaving19Original28918FloorBinding.lean:60–88`；上述所有字段由原 row 填好，`higherMomentEncoding := ... rfl`，再 `.toMomentRow`。 |
| 原 Q80/Q96 与保存总和 | 同文件 `:48,54,90,98,106–135`；使用原 `max(old,new)`，每行与 aggregate 均有 closed finite proof request，没有保存结果作假设。 |
| 原 cell 合法性与无重计 | M `saving19_owned_integral/P2OriginalSaving19OwnedSource.lean:49,139–154`；全部97 proper gates；`P2OriginalSaving19PullingOwnership.lean:91,100,183–221` 从原支持平面多项式/不同顶点集 guards 得出实际 overlap 零测。 |
| 解析积分与最终端点 | M `P2OriginalSaving19OwnedIntegral.lean:94–151`；AE owned union、包含于原 selectedSource、非负单调性，且`:136` 已把 K 的 generic consumer 实参设为实际 `fullMomentRow`。 |

终端 `ImbalancedChen.P2OriginalSaving19OwnedIntegral.original_endpoint_le_selectedSaving:149` **没有参数**，其体直接组成

`283388722705335806564439 / 2^96 ≤ selectedSaving`。

因此“实际28918 family、higher-moment 填充、Q96→selectedSaving 连接还未写”不符合当前源码。Q09 零新增 Lean 是正确复用决定，而非未完成任务。M 的 `original_pulling_checks:59` 是有序 ledger 认证侧支；解析 overlap 证明实际依赖 `original_polynomial_faces:91` 与 `original_vertex_sets_distinct:100`。两类 guards 都必须在未来完整模块验收，但它们不是 caller 的积分/覆盖前提。K `saving19_preservation/P4AOriginalSaving19BankExhaustion.lean:245–255` 的原 strict cells 被半开 bankRegion 穷尽是另外一种 coverage，不能误当或重复要求 simplex 覆盖。

保留 mask138、原 A23-low minorant、实际8维9顶点10因子、`4*(M-R)`、cutoff、c/K、cell4一次与原行 multiplicity。新完整 bound 替换同域旧 bound；不能把两者都加作 saving。M13 的数据/端点没有替换 O14，反向也一样；11026 unequal seed 更不是这里的实例。

**P 两个同名最小修复的选择保留。** canonical-moment 的冻结原路径是 R 下 `docs/source-only/20261028-paper-first/cohort04/certificate/sources/2a511a7246bf9dd54d79649c171c34cf741ca4a0fbd10b2701ba42e6e615239e/P2Winner9ActualEightSimplexMoment.lean`。本次独立读取原字节和 P 字节后确认：

| 同名模块与选用路径 | 精确差异与核对 | 原/新 SHA256 |
| --- | --- | --- |
| `ImbalancedChen.P2Winner9ActualEightSimplexMoment`；选 P `saving16_pulling_ownership/P2Winner9ActualEightSimplexMoment.lean`，目标 `ImbalancedChen/P2Winner9ActualEightSimplexMoment.lean` | 原 cohort04/certificate/sources/`2a511a…` 冻结源 line124 的 `rw [← integral_const_mul]` 仅改正向；7420→7416 bytes；该单次 UTF-8 替换恰得 P 全部字节。实际 Mathlib Basic:288–290 的公式正是积分内常数提到外侧。 | `2a511a7246bf9dd54d79649c171c34cf741ca4a0fbd10b2701ba42e6e615239e` → `6c50d79875f94da6d89d6485fa553647496a2cdaf661ebe138e07fe0782f6834` |
| `ImbalancedChen.Part4ActualThirdOriginalClosedSplitAggregation`；选 P `compact_total_endpoint/Part4ActualThirdOriginalClosedSplitAggregation.lean`，目标同名生产路径 | 原生产8221 bytes→P8639 bytes，只插入418 bytes（注释及透明 `OriginalThirdCompactPartitionSourceOnly.originalCompactThirdCorrection` abbrev），删除0 bytes。保留原 canonical integral，不在本任务重做 compact。 | `27c9daffb5b47294f4f73b954f2512c12a77102655488d6b300726d581749a98` → `0eb47009874916d49c577f3aeacc45c35f603e5480410cbdf078b3653302b30e` |

这是既有模块的源码替换选择，不是另加 wrapper，也没有在本次安装。旧 M/K/P metadata 均未改；保持旧错误 pin 不会因后来引用 P 报告而自动修复。其余 inherited HOLD 全部保留。

**主表精确处理建议。** 读取的 `../1_+_1.748_lean_proofs/main.md` snapshot SHA256 为 `e94c8d7eec066dfd3758ba98a23c096f039aecfafd0d823681022df6f2c7c0e3`，对应42–54行。本报告不改主表。若蓝表示已有源码，建议：

| 当前叶 | 允许的精确修改 |
| --- | --- |
| 44 `黄｜实例化十四组完整cell数据与几何许可` | 改名蓝：`原十四组数据与正saving下界所需几何许可（source-only）`；保留45原39741合法内部归属蓝叶。 |
| 46 `黄｜完整cell/facet/active-eight覆盖及共同策略实例` | 拆开。将 full-cell/facet/active-eight 穷尽撤出本下界必要叶；需要保留时单列“较强producer认证，非本正下界依赖，尚未验收”。不得原名直接改蓝。 |
| 47 `黄｜共同旧策略实现全部历史门限` | 保留完整实际策略黄项，另列蓝：`retained14共同schedule、实际历史与原第四/第五signed保留（原第四primitive Geometry接口）`。实际完整第四bank、buffered fallback、全87/其余共同策略不因此关闭。 |
| 48–49 signed compiler/ordinary 叶 | 总体48仍黄；49既有ordinary负部蓝项保留，新增蓝：`同一原archive schedule的ordinary十四组Q96 charge端点`。不外推w>0或两笔reserve。 |
| 52 `黄｜实例化十三组chosen-plane完整覆盖` | 收窄后蓝：`十三chosen-plane合法内部并集与原selectedSaving源码桥`。不声称所有chosen-plane cell被simplex覆盖。 |
| 53 `黄｜供给28918个simplex证书与覆盖绑定` | 收窄后蓝：`原28918 fullMomentRow、Q80/Q96与selectedSaving实际实例化源码`。保存所有finite/资源验收HOLD，不重复派发实例化。 |
| 42、50 parents；54共同因果历史 | P2.5/P2.6 parents仍黄；54全链共同因果冻结/parent-history仍黄。已有J/K局部bank/history源码不应被否认，但局部解析端点不足以关闭整叶。 |

这些修改区分“已有源码尚未验收”和“真正未写的供应”，不是按未编译自动判代码缺失；本轮没有绿色建议。

**最终 raw pins 与验证范围。** Q08 最终 registry 的32个 path/hash/size条目独立重算：32个不同路径，0错误。Q09 最终 registry 的612个 path/hash/size出现项独立重算：320个不同路径，0错误，包括登记的225 effective project sources、15 core entries 与52 original witness/result文件；重复项没有当成不同证明。所有 fixture 只读原字节作 SHA256，没有数学解析或重放。此结果不等于逐一独立审完225个证明，也不认证完整 Mathlib/stdlib 或编译环境。

| 最终交付 | bytes | SHA256 |
| --- | ---: | --- |
| Q `saving16_scope/P2OriginalFourteenCommonScheduleEndpoint.lean` | 4575 | `3da5fa16636a97b0556284a86a8b694032da63a81a100a43cc45966452dfb82f` |
| Q `saving16_scope/REPORT.md` | 12020 | `ede4ebf7abd94ccef3cdd2cfd33b4a638f41c15168404e30e1e3696ff5e0b5ea` |
| Q `saving16_scope/REGISTRY.json` | 43477 | `16b120c6d45497ec3b9c8a9e010fa36c4561f8f35c58da6cf39010c74d0f4019` |
| Q `saving19_instance/REPORT.md` | 17753 | `d5fd3f0368bc3bca044070c6200b9347f0c7cd2b1e2e7ba1de3a6c88f7f712b7` |
| Q `saving19_instance/REGISTRY.json` | 1093467 | `38622f08617a929d85283ee944331265e5742258ebc7eae5ebac85e64be94d5c` |
| O `saving16_pulling_ownership/P2OriginalSaving16PullingFaceInduction.lean` | 10262 | `8be89f68730007dd2a59f5afde0ed532deeb65f05a9f3115159cf0176b0d26b8` |
| O `saving16_pulling_ownership/P2OriginalSaving16PullingOwnership.lean` | 10085 | `a291896dc3ee13823ae1fe18326dbbe07583aa04e3304dacfc9353c814fa5ecb` |
| O `saving16_pulling_ownership/P2OriginalSaving16OwnedIntegral.lean` | 6452 | `5aa1cfb7b3080e4bc3ff0152901ac234d7451da4788fee364a7d5bcc1aeb8047` |
| O `saving16_weak_face/P2OriginalFourteenWholeFamilyLower.lean` | 13545 | `d030b9ee6c9606d16409708fc029fa16f8ca0f4e6fc995a171e56442ec1da38c` |
| O `all22_common_history/P4AOriginalCommonArchiveSchedule.lean` | 7224 | `686cbb4a435819025bf43446259b695a5ea95fa11485aeb90eefb2ebd8c79024` |
| K `saving16_glue/P2OriginalSaving16CommonOldPolicy.lean` | 16385 | `c5d85dc8422e0193b17f456fe854a9e066174700569bbfdb593c0a07489b268d` |
| M `saving19_original28918/P2OriginalSaving19Archive.lean` | 10836 | `b8821bbc996d6fdbc19fd359b1be9dd4be181064f7fe1b2f36b8b5a27996a9b6` |
| M `saving19_original28918/P2OriginalSaving19Original28918.lean` | 11237 | `ed126d258139d3ee671f164852f816255138657a035f74af67a0f610637c24b4` |
| M `saving19_original28918/P2OriginalSaving19Original28918FloorBinding.lean` | 5800 | `c4f5765cf575b3faacafe0e765c358373e975a960ab8a7c87d742660510e51b1` |
| M `saving19_higher_moments/P2OriginalSaving19HigherMoments.lean` | 20641 | `59ccbb110e9aceac63a5bb7030b49e0f1103993bc6b2f6fb2b49a80391b2d41e` |
| M `saving19_owned_integral/P2OriginalSaving19OwnedSource.lean` | 6423 | `e18f481c54879b7a51346db7f3549c1ac12f393a194b79322a600e7bf89c1c8b` |
| M `saving19_owned_integral/P2OriginalSaving19PullingOwnership.lean` | 10846 | `87fd625fc864128a001ba49deab415fd82eb944ee3c23bda036762c199f94dde` |
| M `saving19_owned_integral/P2OriginalSaving19OwnedIntegral.lean` | 6659 | `ab58f4acc2a2ea93919d0ee37e5c63e1dba1f07fd704833fefc042d0bb61bafc` |

对 Q 新源和所审 O/M geometry 源的文本扫描未见 `sorry`、`admit`、`axiom`、`unsafe`、`native_decide`。实际 Mathlib `MeasureTheory/Integral/Bochner/Set.lean:136–141,740–743` 的 finite-union 与集合单调性签名同用法一致，raw hash `119710a23a0a09d22f770ca36844ddc3ca1d72cb479e231fe9ec06cea20629f9`。明确检查过 production、全部 source-only 和 `.lake/proof-continuation/source-reviews/drafts`，使用 hidden/no-ignore 搜索；没有因安装目标缺席而判历史源码不存在。Q新模块、O两个直接 imports、M19 endpoint及canonical moment 的生产安装目标当前缺席，依赖仍需按有效来源映射安装。

困难分类保持清楚：(1) 确定的继承表达/API缺陷已有 P 最小替换；其余 elaboration 和资源问题未经测试。(2) Q08 补具体同schedule组合；Q09 所请求的局部实例化并无新的遗漏证明，已有 M 供应。(3) 本次没有建立原稿数学反例。完整几何 producer 认证、共同策略和 signed compiler 的不同边界不得混作一个“未编译所以不存在”的缺口。
