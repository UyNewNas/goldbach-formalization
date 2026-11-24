# PositiveStratumMass → P5 Wire → row5：只读就绪检查

## 结论

`P1OriginalFifthPositiveStratumMass` 当前属于 **尚待正常编译的过期前沿**，没有在已下载的 Batch6/7 原日志中发现该模块的实际 Lean 证明错误。不能据此猜测修改，也不能把其后的静态依赖链全部算作失败。现有源码七份副本一致，未找到不同且可靠的已验修补。

源码基线为 `15fbbdd842d11df0ca4db340cae2eddfa7ed39d7`。本次没有修改任何 Lean 文件，没有运行 Lean/Lake、云任务、内核重放或大规模数值检查。Batch8 仍由根代理执行；本目录不声称其尚未返回的审核结果。

## 已有运行证据与分类

| 模块或目标 | 实际可证状态 | 对下一步的影响 |
| --- | --- | --- |
| `P1OriginalFifthPositiveStratumMass` | Batch6 Wire `lake --no-build` 退出 3，只报 target out-of-date；`project_error_count = 0` | 原样做一次 normal；只在出现真实 leaf error 后修 proof |
| `P1ActualVariableFourthFifthCellTestLimit` | Batch7 原日志明确 `Built ... (18s)`；源码 SHA `02107314…` | 上次 Wire 的另一 stale 项已 normal 通过；无需重复修补；当前 audit17 结果待根代理 |
| `P1OriginalFifthEnvelopeTerminalReduction` | Batch5 原日志明确 `Built ... (10s)`；源码 SHA `052218e6…` | Positive 的直接父项之一；normal 成功可复用；当前 audit17 结果待根代理 |
| `ActualPrimeBoxMass` | 位于上述成功 Envelope normal 的项目闭包；历史仅 completed guarded candidate、kernel=false | 不需要另造 Mertens 供应；刷新 readiness，保留对象绑定检查，不宣称独立 kernel 已验 |
| `P5OriginalChildIntegerWireBinding` | 上次仅 no-build 被上述两个 stale 项阻挡；没有实际 leaf failure | Positive 通过后仍须刷新 Wire 的下一前沿；不是直接进入 row5 |
| row5 的两个 DataBlock000 import | 不在 Batch7 / audit17 已记录源码 context 内；历史 checkpoint 没有 completed trace | 实际 readiness 未知，执行探针前必须单独纳入三 import 的 no-build gate |

上次 Wire 命令原日志 SHA 为 `423fe5dbfdf2fdeebf084e9c7d38f4b6272dc41fee20109888552de97fdf20f5`，命令记录 SHA 为 `6275e6d70dc1a9d6e3fc4e1f106bb4b3b7c6282006a8f276198d130676e73a10`。其两个 reported failed_modules 是 no-build 过期项；没有 leaf error sections。CellTestLimit 所在 normal 组整体退出 1，但该模块的逐项 Built 记录是真实成功，不把整组说成成功。

原始定位与完整 SHA 见 `LOG_EVIDENCE.json`。历史来源定位见 `HISTORICAL_ACCEPTANCE_MAP_EXCERPTS.json`：Positive 和 Wire 的 `accepted_object`、`actual_setup_import_read_receipt` 都是 null。T01 checkpoint 对 Positive 下游 41 项全部只给 `MISSING_COMPLETED_TRACE_OR_SETUP_NOT_REUSABLE`；这些旧记录不是可复用 proof acceptance。

## 1106 稿与现有证明的边界

手稿 pin `a988cba584d803ae2856a0de50efb582f4f3dd6a`。`argument.tex` 的 `eq:current-mertens`、`sieve-appendix.tex` 的 `sv:euler-ratio` 给出 Mertens 归一化；同附录 finite-realization 证明先截小末素数尾项，再在正末素数 cutoff 与严格 margin 的紧块上处理。

Positive 源码的工作正是固定 `0 < δ < 19/96` 后控制有限所选 fifth mesh cells 的质量。严格有序五元组的最后坐标至少 δ，使五个坐标都至少 δ；原 cap 假设给出上界，故其权重和被 target-deleted 实际 prime box mass 控制。固定 box 的 Mertens 极限再给出 eventual 界：所选 cells 数乘以 `∏ᵢ log((19/96)/δ) + 1`。

这里的 eventual 阈值可依赖固定 δ、所选 cells 和其它已固定参数。此定理不声称 δ 随 N 趋零时一致成立，也不替代末素数零 cutoff 的证明。直接消费者 `P1OriginalFifthMovingHarmonicEnvelope` 明确另用全整数调和上界处理 moving windows，并以有限恒等式连接 terminal mass；本次检查未见把 fixed-positive-window 渐近误当作 moving-zero 一致渐近的用法。

因此，此处没有发现具体数学反例或合同缺口；这是有限范围的源码/稿件核对，不是对尚未编译的 41 模块作新的整体数学验收。原定义、假设、常数和强有限 exact 合同全部保留。

## 最小下一步

1. 当前 Batch8 结束后，由根代理按现有 serializer / guard 刷新 Positive 两个直接父项的 no-build readiness：`P1OriginalFifthEnvelopeTerminalReduction`、`ActualPrimeBoxMass`。
2. 父项就绪后，只编译原样 `P1OriginalFifthPositiveStratumMass`；其源码 SHA 为 `f0fa416fbce1ec22d0bd48888edefa18cd76243aa922bb22018952ed2a41d2be`，Git blob 为 `8d2e382b4f5584bd1fd607cedfd094b336a48fc4`。
3. 成功后刷新 `P5OriginalChildIntegerWireBinding` 的 no-build，按实际暴露的前沿续编。静态下一项是 `P1OriginalFifthMovingHarmonicEnvelope`。`NEXT_STEPS.json` 保存全部 40 个下游模块的拓扑次序，供实际就绪检查使用；不预先把它们全部提交为待修或失败。
4. Wire 自身编译完成后，对 probe 的三个 imports 一起做 no-build：Wire、`Data.P1HistoricalFifthSavedDataBlock000`、`Data.P5SubdivisionStoredBlock000`。只读取就绪状态，按精确源绑定复用现有对象；两份 Data block 当前尚无此次已下载 evidence 的 readiness 结论。
5. 三 import 全部就绪后，执行原 row5 探针，保留显式 `--root` 与既有 guard。探针 SHA `37b009ce5f50c968bc54c812b56bd6ddd6620184a5da4c88a9feee6aded753d5`；不重算 row0，不缩短 64 个 children，不把原 3/4 定义换成 4/5。

Wire 的项目闭包 322；row5 probe 闭包 325；Positive 闭包 212。Positive 自身不依赖 CellTestLimit，Wire 依赖它。Wire 闭包与正在执行的 Batch8 normal17 不相交，与 audit17 相交的只有 CellTestLimit 和 Envelope；下一轮必须读取它们的实际结果，不能预测通过。

## 强有限数据证明仍未验收

Wire 已有源码声明 `stored_first_two_parent_replacements_exact`，覆盖 row0/1，因此无需另造 row0 探针。但目前没有找到 Wire 的对应接受收据，不能把“源码有 theorem”称为“kernel 已验”。其 128-child 有限声明也会影响首次 cold build 时间；Wire 完成之后再测 row5 才能隔离该新增闭合定理的性能。

全体 `292633 × 64 = 18728512` 子项的原 3/4 parent exact max 合同仍是尚未验收的强有限数据证明。先前 8 行的精确 rational 诊断只排除了这些样本的反例，不构成全体 kernel 验收。本报告没有重复这些计算，也没有替换公有结论。

## 交付索引

- `READINESS.json`：结论、手稿 pin、源 SHA、精确接受边界。
- `NEXT_STEPS.json`：最小目标顺序与完整静态下游拓扑候选。
- `SOURCE_GRAPH.json`：当前基线的 import 图、325 个 probe 项目源绑定及交集。
- `LOG_EVIDENCE.json`：原始命令、日志 SHA 和精确 Built / stale 行。
- `EXISTING_SOURCE_BINDINGS.json`：七份相同 Positive 源码与原 Git 来源。
- `HISTORICAL_CHECKPOINT_STATUS.json`、`HISTORICAL_ACCEPTANCE_MAP_EXCERPTS.json`：现成历史索引的准确未验状态。
