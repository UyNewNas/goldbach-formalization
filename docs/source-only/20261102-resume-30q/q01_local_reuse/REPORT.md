# Q01 — P 黄叶定向复用清点（只读）

日期：2026-11-02。范围：`1_+_1.748_lean_proofs/main.md` 与 `goldbach-proof-continuation/docs/source-only/20261102-resume-30p` 的 README、TASK_STATUS、任务报告和 reviews；定向检查 P1.4、P2.4、P2.5、P2.6 的生产源码、30o/30k/30m候选，并显式包括被默认 ignore 的 `.lake/proof-continuation/source-reviews/drafts`。未作数学重证；没有 Lean、Lake、编译、Git 操作或其他源码修改。本文档是本任务唯一写入。

## 快速复用结论

- **P2.4：四个既定树/积分/charge义务已有具体源码，仍需把完整 Python primitive assertion 与 call-trace refinement 单独保留为缺项。** 直接用 `30p/reviews/t23_review_compact_s16.md` 的四项映射，后续不要重复重做 compact forest/charge proof。
- **P2.5：实际14-cell/39,741 simplex的内部分离、零测重叠、owned union及 source integral 下界可复用 O 的三个模块；选用 P 的一行积分改写修正版。** 这没有给完整全-cell/polytope/active-eight coverage，也没有给共同历史策略。P2.5 broad 仍黄。
- **P2.6：可复用 K 的13域 saving19 bank exhaustion、积分收敛和 signed source list/frontier，以及 M/K/M-owned 的28,918 archive→higher moments→Q96 floor→selectedSaving 源码组合。** 所有关联 closed guards 仍 UNEVALUATED、继承 HOLD 未消；完整13域历史/common policy 与更广 full87 remains yellow.
- **P1.4：P 仅完成原 first-failure H3 的12域 source-semantics 对接。** 143-block archive键完整性、positive-key见证、完整87域 affine gate→真实动态 parent/owner映射、逐parent floor integral 到实际总积分，尚未由本次候选供应。隐藏稿有一个 `Fin 87` + `PhysicalRows` 的假设打包器，不能作为这些供应的复用替代品。

## 逐节点供应/缺项

### P1.4 — archive keys、gates、parent、floor integral

**真正可复用的窄源码：**

- `docs/source-only/20261102-resume-30p/adopted87_policy/P4AOriginalFirstFailureH3Literal.lean` 是原 H3 字面 Lean 段的机械提取；`P4AOriginalFirstFailureH3SourceSemantics.lean:41–138` 将99条原行分作37公共 slack + 62 old-mask planes，并给全部99行的双向语义对应。
- 同文件 `:140–321` 把8个 full-square 和5个 selected-complement-square 条件转成实际整数平方约束；`sourceAffineGuard_iff_StrictH3` 在 `:261`；`actual_h3_guard_iff_source` 等 actual guard 字典在 `:326–350`。适用于原87导航中的H3这12域，不外推。
- `docs/source-only/20261102-resume-30p/adopted87_policy/P4AOriginalFirstFailureH3SourceSemantics.lean:326–350` 保留 H7 < lambda6(actual ancestor) 与 lambda6 ≤ R6 的真实父条件；它没有产生这些条件对所有历史的实例。
- `docs/source-only/20261102-resume-30p/all22_common_history/P4AOriginalRankThreeRestorationSource.lean:35–108,110–176,183–312,318–389` 可复用为 rank-three before-test restoration、active/inactive parent继承、signed恢复项及真实 prime carrier residual 字典；`P4AOriginalFiniteSignedHistoryRefinement.lean:34–107,120–166,170–214` 可复用为 occurrence-preserving 的有限源重组。仅局部二/三层及保留源码重排，不是完整87域策略。
- `docs/source-only/20261102-resume-30p/adopted87_policy/P5OriginalFourthFifthSourceInputs.lean` 对第四/第五原始输入有窄的绑定；`reviews/t26_review_policy_reserve.md` 说明来源与明确边界。

**仍缺且不能视作已供应：**

- typed fifth 143-block archive 仍为 held；需要 archive records 的 keys `Nodup` / positivity 和编码→真实 typed rows 的完整绑定，不能拿原始 byte payload 可读取或其它模块的一般 `List.Nodup` 定理代替。
- 全87 affine domains（12+7+10+其余域）的原 rows、cell 分离/覆盖与 real gate 到每个真实 history/owner 的构造。P H3 的12域语义源码不覆盖余下75域。
- 每个实际 dynamic Q3/Q4 parent、短/继承路径和 selected-complement squares 要由相应原域和历史产生，不能作为 `PhysicalRows` 输入假设。
- 对每个 actual parent 的 archived floor 积分包络、同一真实数据上的求和/实际总积分连接仍缺。
- `30p/reviews/t26_review_policy_reserve.md` 所指 `P5OriginalAdoptedEighthPhysicalMasks.lean` 隐藏稿 (`.lake/proof-continuation/source-reviews/drafts/20261028-Coefficient-Sol6-EighthMask-Phase3/`) 在 `:91–96` 仅索引分区；`:101–116` 的 `PhysicalRows` 将目标 parent bound、first/third/fifth/seventh histories、full/selected-complement squares放进字段，`:189–198` 从 `∃ i : Fin 87, PhysicalRows ...` 选 cap。该稿是先决字段封装，并无从 archive/原 cells 推导这些字段的消费者证明；视为候选线索而不是已供应。

### P2.4 — compact tree / integral / endpoint

`docs/source-only/20261102-resume-30p/reviews/t23_review_compact_s16.md:30–45` 的四项映射已经具体到：

| 子义务 | 复用位置 |
|---|---|
| 原 adaptive ClosedCutTree 实例 | `docs/source-only/20261102-certificates-l/compact_run_certificate/P2OriginalCompactConcreteLoop.lean:49–60,199–218`；`docs/source-only/20261102-resume-30k/compact_priority/P2OriginalPriorityForestLedger.lean:34–50,100–103` |
| 完整 charge 列表与原叶序 | `docs/source-only/20261102-resume-30k/compact_priority/P2OriginalPriorityForestLedger.lean:75–110`；L `P2OriginalCompactConcreteLoop.lean:134–149,199–205`；O `docs/source-only/20261102-resume-30o/compact_total_endpoint/P2OriginalCompactWholeFunctionalEndpoint.lean:53–61` |
| 每个实际叶子的积分上界 | `docs/source-only/20261102-certificates-l/compact_q80_encloser/P2OriginalCompactQ80CompleteSoundness.lean:76–82,124–128`，由 O 在原 run 实例化 |
| charge 总和达到历史端点 | L `P2OriginalCompactCachedEndpointCandidate.lean:23–42`，ConcreteLoop `:207–213`；O WholeFunctionalEndpoint `:53–61` |

P 提供的 `docs/source-only/20261102-resume-30p/compact_total_endpoint/Part4ActualThirdOriginalClosedSplitAggregation.lean:31` 是 production partition namespace 缺失 abbrev 的最小修复副本；应先于依赖模块选用。O 的两个整体消费者见 `.../P2OriginalCompactWholeFunctionalEndpoint.lean:85–136` 与 `P2OriginalCompactArchivedTotalCandidate.lean:31–39`。详细边界在 P 报告及 T23 review。

**仍缺：** L `docs/source-only/20261102-certificates-l/compact_q80_encloser/P2OriginalCompactQ80Encloser.lean:476–483` 的 `sourceAssertions` 明示是 partial inventory；L `docs/source-only/20261102-certificates-l/compact_run_certificate/P2OriginalCompactConcreteRun.lean:202–212` 的 sourceCheck 不覆盖所有 Python primitive guards；L `docs/source-only/20261102-certificates-l/compact_q80_encloser/P2OriginalCompactQ80CompleteSoundness.lean:15–19` 保留完整 primitive-assertion/call-trace refinement。故四个数学 leaf 能标源码覆盖，完整 producer 认证仍缺。所有相关历史有限 proof bodies/guard UNEVALUATED，P2.4 parent 继续黄。

### P2.5 — saving16 fourteen cells

**真正复用模块：**

- `docs/source-only/20261102-resume-30o/saving16_pulling_ownership/P2OriginalSaving16PullingFaceInduction.lean:91–120` 的 `supporting_child`、`pull_pair_separated` 等实际原 face incidence 归纳。
- `.../P2OriginalSaving16PullingOwnership.lean:105,154,206,220` 的 `original_pulling_bindings`、`original_row_separator`、`original_within_cell_null_overlap`、`original_within_cell_ae_pairwise`，用同一 M 原档、保存顺序/ordinal 和 actual row supports。
- `.../P2OriginalSaving16OwnedIntegral.lean:96,107,129,140,153` 的 `ownedSupport_pairwise_disjoint`、`ownedSupport_ae_eq`、`ownedUnion_integral`、`original_simplex_integral_sum_le_source_integral`、`historical_endpoint_le_source_integral`。
- 真正原档/39741计数与 Q96 floor records 位于 `docs/source-only/20261102-resume-30m/saving16_q96_endpoint/P2OriginalSaving16OriginalArchive.lean:43–50,257–319`；source rows/support/interface在 `P2OriginalSaving16SimplexBinding.lean:114–141`、`P2OriginalSaving16CellOwnership.lean`。P 报告详列了边界。
- `docs/source-only/20261102-resume-30p/saving16_pulling_ownership/P2Winner9ActualEightSimplexMoment.lean:124` 仅作继承 canonical-moment 的积分常数 rewrite 方向单行修正版；选择此修订副本，避免冻结依赖中的确定表达/API错误。
- ordinary `w=0` whole-family weak-complement 一侧支付另见 `30o/saving16_weak_face/P2OriginalFourteenWholeFamilyLower.lean:27–65,84–134,139–215`，与 `30m/saving16_compiler/P2OriginalFourteenUniformResidual.lean:57–95`；只支付一侧 ordinary complement。

**仍缺：** 完整 cell = candidate-facet polytope、full face-lattice/active-eight 穷尽并未由上述合法内单纯形子集结论供应；common historical strategy / 旧收益保留仍缺；same-rho signed compiler/reserve及全策略仍缺。`30p/reviews/t23_review_compact_s16.md:66` 明确建议把“合法内部并集”与更强完整 coverage 区分。P2.5 `full cell/facet/active-eight coverage`、`common policy` 继续黄。

### P2.6 — saving19 thirteen cells / 28,918 floors

**真正复用模块：**

- `docs/source-only/20261102-resume-30k/saving19_preservation/P4AOriginalSaving19BankExhaustion.lean:186,235` 的 `original_eventually_bank`、`original_eventually_bankRegion`，证明实际13个原 strict cells 被该组有理内 bank regions 穷尽；`P2OriginalSaving19BankIntegral.lean` 给原 density 对 bank omission 的实际积分收敛；`P4AOriginalSaving19BankFrontier.lean:82–...` 的 `selected_signed_sum` 保 occurrence/sign/incoming mass/prefix/source。
- `docs/source-only/20261102-resume-30k/saving19_moments/P2OriginalSaving19SimplexMoments.lean` 推出真实物理 simplex 的 gap mass 与 weighted factor means；`P2OriginalSaving19MomentFloorConsumer.lean:265–272` 固定原13域 row counts 合计28,918并给 floor-sum consumer。准确组合在 `docs/source-only/20261102-resume-30m/saving19_owned_integral/P2OriginalSaving19OwnedIntegral.lean:136–151`：`:136` 将 consumer 实参设为 M 的 `fullMomentRow`，`:141` 接上原 Q96 绑定，`:149` 给出 `original_endpoint_le_selectedSaving`。这已完成 M/K 的 row/floor/integral→J.selectedSaving 源码组合。
- `docs/source-only/20261102-resume-30m/saving19_original28918/P2OriginalSaving19Archive.lean`、`P2OriginalSaving19Original28918.lean`、`P2OriginalSaving19Original28918FloorBinding.lean` 已给 exact-file-driven archive/parser/physical rows/floor bindings 的封闭 proof requests；`30m/saving19_owned_integral/P2OriginalSaving19PullingOwnership.lean` 和 `P2OriginalSaving19OwnedIntegral.lean` 是实际几何/owned-integral桥接候选。报告见 `30m/saving19_original28918/REPORT.md` 和 `30k/saving19_moments/REPORT.md`。

**仍缺：** M 已 source-level 构造 exact-file-driven 28,918 typed family并给 parse/shape/physical/floor/aggregate closed proof requests，且 `P2OriginalSaving19OwnedIntegral.original_endpoint_le_selectedSaving` 已将 M `fullMomentRow`、K floor consumer及原 Q96 binding 接到 `selectedSaving`；该组合不是待写缺口。相关 closed guards 全部 `UNEVALUATED`，故仍无通过的 archive authentication 或 kernel 接受；M 报告所列 inherited K HOLD 也仍在。另需区分几何源码：OwnedIntegral 已提供 original simplex integral sum ≤ `selectedSaving` 的组合，不应再列为缺口；但完整13域历史/common policy、previous gains preservation、same-policy reserves/all22 是不同的全局义务，仍 HOLD。

## 隐藏搜索的处理与证据边界

确实执行了 `.lake` 的显式搜索：`rg --files --hidden --no-ignore goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts`，并针对 `P5OriginalAdoptedEighthPhysicalMasks`、`ClosedCutTree`、`primitive assertion/call trace`、`archive key/Nodup/positive key`、`floor integral` 与相关 saving16/19 名称在 hidden drafts 与源码中检索。没有用默认 ignore 结果推断“无候选”。当前 `.lake` 中与 P1.4 目标显式相关的 PhysicalMasks 文件，正是上文被 t26 review 限定为目标条件封装的候选；未找到可替代 30p 缺项表中 archive→87域→actual parent→floor integral 的端到端消费者。

所有材料均是源码候选/静态记录：30p README/TASK_STATUS 明确 `compiled=false`、`kernel_verified=false`、有限 guard `UNEVALUATED`、new green nodes=0。本文只为复用定位，不闭合任何数学判断。




