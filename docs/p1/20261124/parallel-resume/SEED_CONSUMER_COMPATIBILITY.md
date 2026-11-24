# Winner9 opaque entry：P1 四出口必要消费者

## 结论

核对范围固定为 `context-recovery/FOUR_ROOT_SOURCE_GRAPH.json` 的四个原 P1 出口。SeedData 在该图中有 159 个下游模块；其中 9 个模块显式使用 `entry`、`allRows`、`physicalVertices` 或 `RowIndex`。6 个模块存在依赖 `entry` 透明归约的证明。此次候选集为 7 个文件：修补这 6 个原模块，并增加现有 `P2Winner9LedgerCore` 依赖。原 SeedData 算法及 P2agent 的 90 个复用文件未写入。

候选目录为本目录的 `ImbalancedChen/`。所有候选均为 **SOURCE_ONLY，未在本轮运行 Lean**。哈希、来源与相对 evidence 路径见 `MANIFEST.json`。

| 原消费者 | 透明依赖 | 最小处理 |
|---|---|---|
| `P2Winner9CompleteSeedChronology` | 全行 maxima、三个完整 selected totals 的 `decide +kernel` | 原字节复用旧 P2 的 `P2Winner9LedgerBridge.lean` 到原 Chronology 文件路径；它本来就使用原 Chronology namespace，并通过 `entry_eq_allRows` 连接分块 totals；同时原字节复用 LedgerCore |
| `P2Winner9CompleteSeedPositiveDomains` | `all_original_means_positive` | 仅在原 `decide +kernel` 前重写 `entry_eq_allRows` |
| `P2Winner9CompleteSeedMomentDecoder` | `all_source_facts`、`all_field_facts` | 仅展开原有行局部定义并重写 `entry_eq_allRows`，保留原有限决策证明 |
| `P2Winner9CompleteSeedLogBranch` | `all_log_facts` | 同上：展开原有 log 行局部定义并重写入口等式 |
| `P2Winner9CompleteSeedSelectedFloors` | `full_source_membership` 的第二个 `rfl` | 精确替换为 `entry_eq_allRows ⟨n, hn'⟩` |
| `P4AOriginalFull87SeedRefinements` | `original_seed_vertex_bindings` 的 `decide` | 仅先重写入口等式 |

`P2Winner9CompleteSeedGapReserve`、`P2Winner9CompleteSeedT10Q6`、`P2Winner9CompleteSeedSourceGates` 不需要为本次 opaque entry 改动。SourceGates 的有限决策只涉及原 201 顶点、97 gates 和固定 mask；PositiveDomains 的 `actual_vertex_lookup := rfl` 两侧使用同一 entry 索引，仍是定义相等。

## 复用依据与合同

检索全部 scratch 中这 9 个旧文件名，每个旧文件均只有一个字节版本（文件重复位置与 SHA 见 `EXISTING_VARIANTS.json`），没有另一个现成修好 postimage。再次检索全部 Lean 源码中的 `entry_eq_allRows`，现成消费者只有旧 P2 的 LedgerBridge、CompletePullingGeometry、CompleteNumericalChecks；后两者不提供旧 MomentDecoder/LogBranch 的完整合同。

LedgerBridge 复用 SHA 为 `3eba8ce7a985bfae133b911aaf9fd75c1b9683f3ab43f52f2272db8d078a45fc`。其 namespace 正是 `ImbalancedChen.P2Winner9CompleteSeedChronology`。原 Chronology 的 8 个定义/abbrev 均逐项保持，9 个旧公开定理全部保留；除 `all_actual_row_maxima` 将前置 `∀ i` 写成显式 binder 外，旧定理类型文本规范化后一致。这一 binder 写法是同一 Pi 类型。新增加的 totals 辅助定理无需改旧消费者。

LedgerCore SHA 为 `6e7d69c2f429fc4d174d608255be3726718ecae945878cdfc38f15482549ab82`，旧日志记录 strict compile 成功，耗时 2.239 秒。完整 LedgerBridge 的旧尝试 SHA `3e35abc…` 在总和三元组投影达到 recursion depth 上限；现在复用的 `3eba8ce…` 是旧团队已经准备好的 symbolic-projection 修复，旧 checkpoint 明确记录 **未编译**，此次没有重新编写其证明，也不转移不具备的验收信用。证据摘录见 `REUSE_EVIDENCE.json`。

LedgerBridge 所需的 `P2Winner9CompleteSeedTypes` 和 SeedVertices 在两个仓库逐字节相同。`P2OriginalSeedChronologicalMaxArithmetic` 的仓库版本差异在 import、说明文字和新增末尾 `eighth_stage_ledger_sum`；LedgerBridge 使用的原定义与定理保持一致，所以不需为此次复用再替换该模块。

## 不应混同的剩余义务

新的 90 文件体系提供 `ArchiveRowCheck = RowShape ∧ curvatureRaw ≤ mixedRaw`、源数组绑定及 maxima 接口。它不提供全部均值正性、所有矩阵/多项式矩恒等式、Q80/Q96 精确上下舍入、两条分支各自的完整字段事实。

旧 `all_source_facts`、`all_field_facts`、`all_log_facts` 仍使用对 11,026 行的原 `decide +kernel` 证明体。此次薄接线消除 opaque entry 的表示障碍，但不替代、缩小或宣称已执行这些全族数值义务。新版 P2 的 winning-branch checker 仅检查每行选中分支，不能直接替换旧 FieldFacts/LogFacts 更强的完整字段合同；其完整数值 pages 在现有 evidence 中也仍是未执行候选。

按 1106 稿分类：

- `entry` 从透明查表改为 certifiedEntry 是表示/接口变化，等式 `entry_eq_allRows` 即是已有连接。
- 大规模有限数值证明未执行，是形式化证书尚未完成，不能据此判定稿内数学有实质缺口。
- `numerical-appendix.tex` 的 `num:simplex-moment` 明确给出单纯形精确矩公式，并要求有理 kernel/log 包络；`num:upper-table` 前明确后两行是相对于前序父值的 curvature/mixed 增量。复用 LedgerBridge 保留这一 chronology，薄修补不引入新的数学假设。

## 复核状态

已核对文件哈希、旧公开名/类型和原定义保留、两个现有 Ledger 文件的精确字节复用，以及没有新增 sorry/admit/axiom/native_decide。只写入本独占目录；未开云任务，未运行编译或内核验收。所有当前候选是否通过仍由 root 的唯一编译队列确认。
