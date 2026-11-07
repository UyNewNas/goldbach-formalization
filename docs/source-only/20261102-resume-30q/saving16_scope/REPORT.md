# Q08 saving16_scope — 必要范围审计与同 schedule 原 Q96 端点

已补一条具体源码连接：原 `1222997719565324892497827 / 2^96` 下界落到 O 已构造的**同一 pre-N archive/history schedule** 上的真实 ordinary 十四 cell signed charge。共同历史、原第四／第五 signed gain 保留、ordinary 负互补支付和 39741 个 simplex 的积分比较全部复用。没有增加或重证任何分析估计。源码未编译、未 kernel 验证，`formal_credit=0`；继承有限体仍为 `UNEVALUATED`，P2.5 broad target 与完整物理 compiler/reserve 仍 **OPEN**。

主表当前把“完整 cell/facet/active-eight 覆盖”与共同策略放在同一必要黄叶，范围过强。该完整几何过程确实出现在原始 producer 的方法说明中，但它**不是原正 saving 下界的必要依赖**。本任务只给严格依赖证据，不为闭表增加该更强定理。

## 1. 原稿、原始 producer 与覆盖依赖

已读 Q/BRIEF、P 的 saving16 两份 REPORT/REGISTRY 及 `reviews/t23_review_compact_s16.md`。原稿为 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`，SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。

- 原稿 435–449：实际第六 parent 仅需由 R6 从上方控制；原 density 的系数为 4，没有 Chen quarter 或排序 factorial，保留 cutoff `53/13824` 及 full/selected-complement squares。
- 原稿 1354–1356：正 saving 允许使用合法子集并舍弃其余部分；负 cost 的上积分必须覆盖完整保留域。
- 原稿 1364–1369：描述 exact active-basis、每个原始 facet、boundedness、face lattice 与 pulling 的计算认证方法。它支持更强的 producer 完整认证要求，并不改变前述正下界的单向依赖。
- `../chen-imbalanced-semiprimes/proof-library/source/eighth-prefix-family-20261009.tex:74–103` 描述 96 原始非恒定行、完整 active-eight 枚举及逐 simplex Q96 floor；105–124 另外要求同一因果历史、实际 parent 保守比较及旧 allowance 保留。其 SHA256 为 `d8e63ef277a7d6ac9163283948445287b879c0c6134908950678bd053e2005a8`。
- 原作者 `../goldbach-research/eighth-prefix-family-20261009-exact.py` 的 `certify` 在 active8 枚举、all-original-inequality 顶点测试及 face ledger 之后生成有序 pulling rows 与各自 floor；`main` 排除原 adopted cell7，仅汇总其余 14 个 ascending cells。读的是 source text，没有执行 producer、导入 Python 模块或重放 witness。原 producer hash 为 `e9a38f9f370bccc69613ccbe1da7a81114891e7965a138ec9ebe33f07e55818a`。

必要链可以直接从现有声明核对。令 C 为原 14 个 strict source cells 的并，T_r 为原档第 r 个 simplex 的实际 support，U_r 为仅删去已证明零测例外的 owned support，则已有源码给出

`H_Q96 ≤ Σ_r ∫(T_r) density = ∫(⋃_r U_r) density ≤ ∫C density`。

| 必需事实 | 精确既有来源 | 是否要求全部 cell 被 simplex 覆盖 |
| --- | --- | --- |
| 原始 row support 在对应 cell closure 内 | M `P2OriginalSaving16SimplexBinding.rowSupport_subset_closure:117` | 否；仅单向包含 |
| 同 cell simplex 的交集零测，实际有序原档绑定 | O `P2OriginalSaving16PullingOwnership.original_within_cell_null_overlap:206` 与 `original_pulling_bindings:105` | 否；使用原 facet incidence、primitive pulling Shape 和 separator |
| owned support 两两不交、AE 等于原 support、落在 C 内 | O `P2OriginalSaving16OwnedIntegral:71–127` | 否 |
| 有限积分可加性及正函数的集合单调性 | 同文件 `ownedUnion_integral:129`、`original_simplex_integral_sum_le_source_integral:140` | 否；只用 `ownedUnion_subset_region` 和 density 非负 |
| 原 Q96 端点进入原 source integral | 同文件 `historical_endpoint_le_source_integral:153` | 否；调用 M 原 archive/Jensen/Q96 |
| strict source 进入实际 selected guard | J `P2OriginalSaving16FourteenPhysicalAtlas.sourceRows_cellGuard:162`、`region_selectedFamilyGuard:176` | 否；96 行逐 cell 推导真实 guard，不用 candidate-facet polytope 等式 |
| 实际 common third/sixth history | K `P2OriginalSaving16CommonOldPolicy.exists_common_actual_parent_on_trim:177` | 否；实际 historical mesh、source guard、原 fourth/fifth maxima 及 sixth exclusion |
| ordinary 全 family 下界，含 weak/open inherited 部分 | O `P2OriginalFourteenWholeFamilyLower.exists_actual_whole_family_lower_at_original_cutoff:220` | 否；M retained 源加 O 一侧负互补支付 |

完整覆盖只可能为第一条链增加反向包含或等式，现有正下界没有使用它。这里不能把“覆盖不必需”误读为全部几何证书都不必需：**原顶点在全部 96 行内、实际 facet incidence、Shape/有序 rows/Nodup、所有 39741 个 floor 的原档绑定及无重计仍是实际依赖**，其有限体继续未验。无需的是 candidate-facet polytope 等于整个 cell、active-eight 穷尽及完整 face-lattice 覆盖，而不是已经使用的局部合法性和不重叠。

同样，strict source 与 weak selected guard 不需要逐点相等。O 的 ordinary 负部支付在算术子集上先逐点控制有害项，再乘非负权求和；没有用 Lebesgue-null 墙删除有限 prime histories，没有舍弃 open equality/inherit region，也没有把负 cost 的缺覆盖当作可忽略。

## 2. 实际新增：原端点进入已构造的共同 schedule

唯一新文件：`P2OriginalFourteenCommonScheduleEndpoint.lean`。

唯一新声明：`ImbalancedChen.P2OriginalFourteenCommonScheduleEndpoint.exists_fixed_archive_and_whole_fourteen_q96_schedule:44`。

直接 imports 只有：

1. `ImbalancedChen.P4AOriginalCommonArchiveSchedule`，现有 O 文件 SHA256 `686cbb4a435819025bf43446259b695a5ea95fa11485aeb90eefb2ebd8c79024`；
2. `ImbalancedChen.P2OriginalSaving16OwnedIntegral`，现有 O 文件 SHA256 `5aa1cfb7b3080e4bc3ff0152901ac234d7451da4788fee364a7d5bcc1aeb8047`。

O 的 `exists_fixed_archive_and_whole_fourteen_schedule:68` 已经选出一个真正的 `fixedSchedule`：原 grid400-aligned `m=475*q-1`，`chi=e/20`；`ArchiveSchedule.data` 使用真实原 fifth archive，第四 rows/licence 仍保留原 primitive 输入。它返回原始 `FourteenHistory`，包括真实 firstStop、第三 support、H1/H3/H5/H7 小于实际 lambda3、lambda3 小于等于实际 lambda6、`H7<lambda6<=R`，以及同一 ancestor 的旧第五 gain。它还返回任意 signed terminal test 和原始 occurrence carrier 上原 fourth/fifth gain 的精确保留恒等式。该接口没有假定 ideal `L3=R` 就是 finite actual cap。

Q 保留这些结论和同一组 witnesses，唯一新推导是

`H_Q96 - epsilon ≤ ∫C density - epsilon < normalized_actual_charge`。

因此新端点既不要求调用者提供 source integral 下界，也不要求 history realization、source endpoint、弱补项、几何覆盖或 signed preservation 作为新前提。它是两个已在场具体 suppliers 的实际接合，不是新增泛型 wrapper 或新分析证明；也没有再次证明 Q96 floor、Riemann 极限或 ownership。

量词完整保留为 `rows4/licensed4/Geometry, epsilon → n,e0 → e,omega → q,N0 → N,cap,z`，其中 `0<e<e0`、`omega<=1/100`、`N` sufficiently large and even、`N^mu<=z<=cap`。同一 `s.data`、`lambda6 s.data N`、`policy5 s.data N`、`literalPattern`、原 normalizer `log N / singularSeries N` 和 presieve `w=0` 在端点两侧不变。原 trim 误差 `<epsilon/4` 也原样返回。

新 Lean SHA256：`3da5fa16636a97b0556284a86a8b694032da63a81a100a43cc45966452dfb82f`。预期安装模块为 `ImbalancedChen.P2OriginalFourteenCommonScheduleEndpoint`；这里只交 source，未安装。

## 3. signed physical family 边界及真实剩余项

J `P2OriginalFourteenSignedParentLedger.charge:68` 是独立定义的真实 stopped-continuation 有符号 charge。其 `parent_sub_policy_eq_charge:81` 精确等于同一 parent polynomial 减 literal14 policy polynomial；ordinary residual 字典在 `unpresieved_charge_eq_residual_sum:104`。该 parent 在本实例是 common constructor 的 `policy6`，按定义保留真实 `lambda6` 和 `policy5`，没有换成常量 R。

任意 w 的物理身份也早已存在：J `physical_parent_sub_fourteen_eq_signed_ledger:118` 同时保留 `((hi+lo)/2)*charge(w)` 与 `((hi-lo)/2)*(absoluteMassOld-absoluteMassNew)`。Q 不重写它，更不从 w=0 的端点删去后项或推出 w>0 的下界。ordinary source 进入该 physical identity 所需的 presieve projection、beta-width/absolute-mass 支付及有限 compiler loss 仍是独立真实缺项。

另外，held `P5OriginalCommonRefinedConstructor.policy8:124` 使用 `P5OriginalAdoptedEighthPhysicalMasks.familyPolicy`，不是本 theorem 的 literal14 policy；完整原 87 域成员／源绑定、全 common old policy 和全部 22 gain 保留不能由本定理推出。原第四完整 bank/licence 的实际实例也没有被 `rows4/licensed4/hgeometry` 自动供应。Q 没有增加这些目标型假设，更没有声称消除了它们。

## 4. 主表建议：按必要依赖拆分，不把未编译改绿

针对本次读取的 `../1_+_1.748_lean_proofs/main.md:42–49`：

- 保留已有蓝项“原十四组39741个合法内部simplex的AE归属与积分比较”。
- 将原“实例化十四组完整cell数据与几何许可”限定为“原十四组数据与正下界所需几何许可”，该所需范围已有源码；不借此宣称完整 polytope 穷尽。
- 从本正 saving 下界的**必要**黄叶中撤出“完整 cell/facet/active-eight 覆盖”。若仍跟踪原 producer 全过程认证，应另记为较强 archival/producer audit，说明它不是此端点的必要前提，且没有被本次证明。
- 将已实现的局部共同历史与本次“同一原 archive schedule 的 ordinary Q96 charge 端点”列为源码蓝项；完整原共同旧策略、其余旧收益保留、原第四 licence 实例仍黄，不能把局部 `FourteenHistory` 当成全部历史已闭合。
- “连接 signed compiler 并证明整体积分包络”在 positive-presieve、全87/full policy、两笔 reserve 与最终 K 的真实剩余范围内继续黄。已有 ordinary weak-complement 蓝项继续保留。

这不是给较强全 cell 完整性结论改色，而是撤销一条并非原下界必需的依赖。原稿的较强计算过程描述与 negative-cost 全域覆盖要求均未被否认。主表没有由本任务修改。

## 5. 继承修复、困难分类与验证边界

必须继续采用 P 的同名 `ImbalancedChen.P2Winner9ActualEightSimplexMoment` 最小替换：旧 `2a511a7246bf9dd54d79649c171c34cf741ca4a0fbd10b2701ba42e6e615239e` 源在 line124 反向使用 `integral_const_mul`；P 仅改为正向，SHA256 `6c50d79875f94da6d89d6485fa553647496a2cdaf661ebe138e07fe0782f6834`。此源码修复不是完整 canonical-moment/endpoint 链的验收。O ownership 实际导入整个 M19 `OwnedSource`，尽管只用其 neutral evaluator/affine-null API，其 Original28918 与其他传递 guards/HOLD 仍在 import 图中，不能删去状态记录。

困难分类：(1) 新组合只涉及现有声明和有序域的减法单调性／传递性，仍未经 elaboration；继承 API/资源问题仍可能存在。(2) 这次补的是具体 endpoint-to-common-schedule 遗漏连接；较强 coverage 不是本端点的遗漏步骤。(3) 没有从现有形式模型的缺项推断原稿有实质数学反例。

仅做 source 读取、production／全部 source-only／hidden drafts 的定向去重检索、声明／imports 对照、原始 SHA256、JSON 和文本检查。没有 Lean/lake/compiler、CI、finite guard 求值、数值重放、producer 执行、Git 操作或子代理。只写本 Q task 目录。精确新／复用 paths、imports、声明行号、raw hashes、原始输入前提与未消除项见 `REGISTRY.json`；它只登记直接及关键语义依赖，不冒称审完完整传递 import closure。
