# P3 Cell00 既有对象恢复计划

状态：只读审查与待填执行清单；没有启动 Lean、没有恢复远端文件、没有产生新的形式化结论。

## 结论与适用范围

先复用已经找到的原对象，随后仅对最终盘点仍缺失的对象做原源码正常编译。若编译产物逐字复现旧 SHA-256，旧独立 kernel replay 与完整 owned 审核继续绑定同一对象，不重复执行。正常编译本身必须记为本次恢复的新动作，不能把恢复记录写成“没有重编译”。

目前依据同目录外的 `docs/verification/20261126-p2-5-resumed/p3-cache-recovery/RECOVERY_MANIFEST.json`，41 个项目对象中 31 个已有精确匹配位置，10 个仍缺失；完成的 P3 盘点在其现有文件/归档中找到其中 21 个对象，14 份原 witness 也全部匹配。这个数量不是不可缩减的重编译名单：恢复 driver 仍先解析全部原字节来源，只重建实际仍缺的对象。任何同名但不同 SHA 的现存对象均不能冒充匹配项。

本计划不修改原 `run_cell00_four_consumers_v7.py` 的门禁。原 v7 的运行前提是完整恢复历史字节及其路径。只恢复 41 个 `.olean` 并不足够：consumer005 的 `frozen_inputs` 有 16,646 个路径，其中 5,312 个外部对象和 10,624 个外部 companion 来自现有工具链与 `/mathlib`；另有 706 个非外部路径，以及 Lean、leanchecker、mathlib manifest、mathlib toolchain 共 4 个运行时文件。244 个项目 `.olean` 路径全部对应上述 41 个对象 SHA，没有额外的项目对象版本。

核心证据入口：

- `docs/verification/20261126-p2-5-resumed/consumer-attempt005/RESULT.json`，SHA `bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88`。聚合仍失败，只有 Decoded owner 接受。
- `docs/verification/20261126-p2-5-resumed/field-symbolic-attempt006/RESULT.json`，SHA `82123af5bc4f1e9334da8f578de11147effe73da0a7ab90b55459abbb25bcb0e`。FieldDecode 接受。
- `docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v7.py`，SHA `4d0b9e19a564f99416fc5f57ccb41f0570df2b3af53d5a61277f31b3ee063197`。本计划按其实际代码审查，文件头旧注释中的 attempt006 不改变实际 `OUT=...attempt007`。
- `docs/verification/20261126-p2-5-resumed/p3-cache-recovery/expected-original-witnesses.json`，从原 outer receipt `cb11eb092d12e3e1f08eb9dccad4ecbe53311f456babe6c0ccabe72b93c3fa65` 抽取的 14 份 witness 原字节要求。
- 本目录 `RECOVERY_MANIFEST.template.json`：固定源码、预期对象、命令参数、历史路径要求和待填的新执行记录。模板中的空结果不表示任何门禁通过。

## 最小执行范围

| 类别 | 正常编译 | 独立 replay | 完整 owned audit |
| --- | --- | --- | --- |
| 已找到原 SHA 的 31 个对象，历史审核材料亦可恢复 | 0 | 0 | 0；重新读取并校验旧记录 |
| 最终仍缺失的对象，正常编译后精确复现原 SHA | 每个缺失对象 1 次 | 0；复用绑定原对象的旧 replay | 0；复用绑定原对象的完整旧库存及审核 |
| 缺失对象正常编译后 SHA 不同 | 停止旧 v7 恢复路线 | 需要新的独立验证；不能填旧 receipt | 需要新的完整验证；不能填旧 receipt |
| v7 的 4 个未接受 consumer | 每个 1 次 | 每个 1 次 | 每个 1 次，由原 v7 执行 |

前两行成立的前提包含：源字节、所有项目依赖对象、工具链、输入文件、外部对象与 companion、旧三阶段日志、完整库存、原 owner publication 和 receipt 都按旧身份门禁恢复。源码相同但对象不同不满足这一条件。

当前暂缺集合的一种合法拓扑次序如下。表中名称均带 `ImbalancedChen.` 前缀；完整 SHA 在 JSON 模板中。

| 次序 | 模块 | 暂缺前置 |
| --- | --- | --- |
| 1 | P2OriginalSaving16DecoderChars | 无；复用 Decoder |
| 2 | P2OriginalSaving16DecoderCompose | DecoderChars |
| 3 | P2OriginalSaving16OriginalInput | 14 份原 witness 输入 |
| 4 | P2OriginalSaving16FiniteCore | OriginalInput |
| 5 | P2Saving16CanonicalCell00Binding | OriginalInput |
| 6 | P2Saving16Cell00OriginalJson | CanonicalCell00Binding |
| 7 | P2Saving16Cell00TypedPayload | 无；复用 Decoder |
| 8 | P2Saving16Cell00PayloadBinding | TypedPayload |
| 9 | P2Saving16Cell00ScalarDecode | DecoderChars、TypedPayload |
| 10 | P2Saving16Cell00StoredFloors | TypedPayload |

没有必要为 Decoder、Q96FloorCore、SourceJson、SourceJsonFuel、SourceJsonFuelBridge、DirectParse、SegmentedParse、StringCharBinding 再编译；对象盘点已经找到这些原 SHA。也不重编译已找回的 FieldDecode 或 Decoded。

## 执行清单

1. 固定最终对象盘点与源码 publication，记录其 SHA、工具链二进制 SHA 和 `/mathlib` commit。只使用 Lean `4.33.0-rc1` 与 mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。读取盘点确定最终缺失集合，不再扫描整个工作区或重新下载仓库。
2. 从已验证实体或归档 member 导出精确字节。在新恢复目录建唯一内容对象；同设备的历史路径副本用硬链接恢复。每次安装前后核对 SHA、字节数、常规文件类型和 companion 集合。既有非空目标只可验证一致，不能覆写。归档按 member 读取，不运行无限制解包。
3. 单独恢复历史 receipt、日志、审计源码、声明 JSON、库存 JSON、外部快照、冻结源码和旧 runner。按照 JSON 模板的历史路径要求逐项校验。它们可以来自原始归档、已发布 exact 文件或保留原文的 capsule。JSON 必须恢复原字节；重新序列化一个语义相等的 JSON 可能改变 SHA。
4. 核对全部 14 个 witness 的实际原字节。`OriginalInput.lean` 的 unchanged elaborator 使用 `cwd=/workspace/p25-q96-20261125`，读取 `../goldbach-research/eighth-prefix-family-20261009-cell-XX.witness.json`，ID 为 00..14 除 07。不能改 cwd、不能改源路径、不能重排 JSON、不能以另一份摘要替代原文。编译前后都记录这 14 个输入的 SHA、长度和实际文件身份。
5. 建新的恢复 attempt，例如 `/workspace/p25-q96-20261125/.lake/diagnostic/p25-cache-rematerialization-attempt001`，确认不存在后才使用。这不是 v7 的 attempt007，也不写回任何旧 attempt。依赖库只放已经确认的 31 个原对象以及按次序成功恢复的缺失对象；拒绝项目默认 build 库作为 fallback。
6. 只安装本地已写且已发布的准确源码。按上表缩减后的次序，对仍缺失对象执行正常编译，把 stdout/stderr、完整命令、开始/结束时间、退出码、超时状态、对象 SHA 和 companion 清单写入新的恢复 receipt。每一步先验证所有依赖已存在且 SHA 正确；正常编译后立刻比较原 SHA，未匹配时停止。
7. 正常编译精确复现原 SHA 后，记录“由原源码正常编译重建且与历史对象相同”，并把独立 replay/owned 证据指向原始 receipt 与日志。不要给旧记录增加阶段、不要把新日志放进旧文件路径、不要伪称重建前原对象仍在。
8. 原 v7 所需的全部历史字节、别名路径与 41 对象复原后，再逐项只读验收其前置。旧 failed consumer 的未接受目标文件必须仍不存在。最终确认 attempt007 不存在、tracked checkout 干净、已发布 v7/parse override 字节一致、完整外部对象集与 companions 原样可解析。
9. 由主线程交付原 v7，传入准确的 40 位 publication commit。v7 自己创建 attempt007，复用 41 个对象，仅对 OriginalParse、OriginalFloors、OriginalArithmetic、OriginalSourceFacts 执行 12 个新阶段。Decoded 保持原 failed005 聚合下的 accepted owner。不要用恢复工作替代这四项尚未完成的证明验收。

## 复用的具体编译命令

以下是已有流水线的参数化命令，不是已执行记录。`${RECOVERY}` 表示新的恢复目录，`${MODULE}` 是完整 Lean 模块名，`${REL}` 是其斜杠路径。模板给每个当前暂缺模块列出了完整 argv；运行者应使用 argv 数组，不拼接未经引用的 shell 字符串。

```text
cwd = /workspace/p25-q96-20261125
LEAN_SYSROOT = /workspace/toolchains/lean-4.33.0-rc1-linux
LEAN_SRC_PATH = removed
LEAN_PATH = ${RECOVERY}/lib + accepted005 的原 mathlib tails

/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean
  -t0 -j1 -M11264 -DwarningAsError=true
  -DmaxRecDepth=1000000 -DmaxHeartbeats=80000000
  --root=${RECOVERY}/src
  -o ${RECOVERY}/lib/${REL}.olean
  ${RECOVERY}/src/${REL}.lean
```

正常编译只为重建缺失字节。若未来确需建立新的对象验收，已有的独立 kernel 命令是：

```text
/workspace/toolchains/lean-4.33.0-rc1-linux/bin/leanchecker --verbose ${MODULE}
```

完整 owned audit 的命令是同一 Lean 严格 flags，加 `--root=${RECOVERY}/audit` 和相应审计文件。审计模板复用 `docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_AUDIT.lean`，SHA `cd452bddeee765b82187f03893cddb5f7136e3420591f0ea00c9bfe1028f670a`，只替换目标模块名。其要求包括：serialized、environment、声明记录三个集合完全相等；包含 private/generated 声明；无 unsafe、partial、新 axiom；传递 axioms 只允许 `propext`、`Classical.choice`、`Quot.sound`；实际项目 import closure 与冻结图一致。外部完整快照有 5,312 个对象，但每个模块实际 import 数量应按原审核核对，不能把 OriginalJson 原来的 2,872 个 imports 机械改成 5,312。

每阶段沿用 600 秒墙钟上限及严格退出码/超时处理。保留 v7 初始 320 MiB、每阶段 256 MiB 和 64 MiB metadata 的容量门槛；恢复过程须另计仍需写入的唯一对象、14 份 witness 与 metadata 的真实空间，不能把 v7 的门槛误当成恢复 payload 已包含在内。OriginalInput 原对象单独约 93.65 MB。先计算恢复后余量，不删除旧证据腾空间，不靠重复复制依赖。

## 历史失败证据与不可伪造边界

以下关键失败字节已经在本地重新核对过，能够按原 SHA 恢复，不需要重跑失败：

| 历史 | 已保留原记录 |
| --- | --- |
| consumer004 磁盘不足 | RESULT `2c8f7b25…`；427-byte exception `e615dca0…` |
| consumer005 OriginalParse normal 失败 | RESULT `bc26ddfa…`；1,046-byte normal log `8c4de444…`；426-byte exception `7a6f4d49…` |
| field004 normal 失败 | RESULT `c8f52525…`；487-byte normal log `2445cd3e…` |
| field005 normal 失败 | RESULT `812f4317…`；192-byte normal log `03ffeec7…` |

field001 的 58,970-byte failed normal log `4528afb4…` 在 rescue manifest 中有原 SHA 记录；该记录本身不能替代实体内容验证。field003 failed normal log `623cd44b…`、field002 RESULT `3af403db…`、旧完整 external snapshot 及其余冻结产物仍必须按全清单恢复并实测 SHA。当前未得到它们均不可恢复的证据，不能提前宣称已丢失；也不能因 manifest 写有 SHA 就宣称已恢复。

如果最终存在找不回的旧 failed 输出，只能在新恢复 receipt 中列为 `UNRECOVERABLE_HISTORICAL_BYTES`，保留原路径、预期 SHA、搜索过的已知归档和缺失事实。不得补写“相似”错误日志、伪造旧时间或退出码、重跑旧失败以冒充旧字节、改写历史聚合 accepted 状态，或删去 v7 门禁。原 v7 因此无法执行，应明确记录该阻塞。新 continuation 若改为新证据链，必须作为独立变更列出与旧历史的关系；本计划没有实施该变更。

若某个重建对象 SHA 不同，仍保存实际产物与新日志，但不装入旧期望路径。新的独立验证至少要覆盖变化对象及其受影响的项目闭包；不能只 replay 缺失对象便继续承认所有旧 context。以当前全部十项都变化的最坏集合计算，45 源图的反向闭包为 36 个模块，其中 32 个属于已有的 41 个 accepted dependencies，另 4 个是新 consumer；这只是风险范围，不是无条件安排 36 次重编译。先定位字节差异，再确定新的最小验收范围。

## 完成判据

恢复 receipt 必须分别给出：找到并复用的对象、通过正常编译精确重建的对象、原 replay/owned 证据引用、未能恢复的历史字节、全部实际新执行命令、输入/工具链/外部快照前后核对结果。恢复成功只说明 v7 的既有依赖链重新可用；`P2_5_proved` 与十四 cell Q96 总结论保持 false。Cell00 的四个 consumer 也须由后续实际三阶段记录决定，不由本计划推定。
