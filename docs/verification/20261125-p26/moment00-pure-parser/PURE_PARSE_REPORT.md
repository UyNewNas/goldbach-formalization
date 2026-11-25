# moment00 原 SourceJson 全文件解析：本地验收证据

## 结论与精确边界

本目录已对原 moment00 文件的完整纯 JSON 解析证明执行 normal 与独立 `leanchecker`，两者均通过。最终无假设定理为：

```lean
ImbalancedChen.P2OriginalSaving19Moment00Parsing.momentPacked00_parse :
  SourceJson.parse (String.ofList momentPacked00.toList) = .ok momentRootValue
```

这里 `momentPacked00` 是正式 v4 候选的同一公开名称 `ImbalancedChen.P2OriginalSaving19Archive.momentPacked00`。本地 loader 与 MomentData00 的源字节和正式 v4 候选完全相同。全部 28,999 字符、10 个根对象字段（9 个 metadata 字段与 records 字段）、56 条 records 都进入原解析器，末尾 CRLF 另以原 `white` 规则证明为空。成功结果是明确的 `SourceJson` 值 `momentRootValue`，并另导出 `parseChars` 和 success tag 推论。

本包目前仅声明 **纯 SourceJson 解析**。没有声明 `decodeMoments`、cell/row shape、Q96 数学检查、所有 26 个输入、旧 Core 原 String literal 的闭合等式或 P1 strict 验收已经通过。真实 typed decode 将在独立后续 owner 中使用原样 Schema 处理。本次不修改生产源码，不提交远端任务，也不重编任何已接受 helper 或 geometry owner。

## 输入与生产连接

原件 staging 路径：`/workspace/p26-original-inputs/eighth-third-moment-refinement-20261009-a23-low-00.witness.json`。

本地实际解析路径：`/workspace/p26-recovery-candidates/archive-moment00/goldbach-research/eighth-third-moment-refinement-20261009-a23-low-00.witness.json`。本地 Lean cwd 为 `/workspace/p26-recovery-candidates/archive-moment00/project`，因此原样 `../goldbach-research/eighth-third-moment-refinement-20261009-a23-low-00.witness.json` 正确解析到该副本。本报告不会把此 staging 路径称作 P1 路径。

原件和副本均为 28,999 bytes，SHA256 `d88e9d02334dfa840f81c0e2be8e97d559978ac3848fdea13990deced9a65052`。读入使用原 `IO.FS.readFile`，完整 `s.toList` 经已证明的 `pack` 后按 Tree 构造机械报价。原始 CRLF 保留；不通过 `read_text` 读取原件，不标准化换行。每次 normal/kernel 运行前后都核对原件、副本、全部依赖源和对象的 SHA，回执保存精确路径。

`P2OriginalSaving19ArchivePackedLoader.lean` SHA `5f1ff6c68faba7bdbde44b7bb7f7aac57c1c1d71563b781ee25a5ab050717f27`；`P2OriginalSaving19ArchiveMomentData00.lean` SHA `5ba66c5a3064fa77d102e6ab1503e87bb66b61aa102db3db61c78df788592234`。原 SourceJson SHA `ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424`，无改动。

## 证明组织与可信边界

`Moment00Input` 定义 `momentChars00 := momentPacked00.toList` 与 `momentRest00 n := (momentPacked00.drop n).toList`。已证明通用 Tree.drop/list.drop 桥直接复用，只有实际 `momentPacked00.count = 28999` 是新的闭合 kernel guard。结合 `Tree.length_toList` 得到真实字符长度，避免重新展开整份字符链求长。

Metadata owner 先证明九个任意 tail 的原 object 状态等式，再组合成 348 字符的前缀，最后以 `take` 的闭合 `rfl` 和已证明的 drop 定理绑定到真实原字符。原 key、colon、整数数字边界、逗号、空白以及 duplicate-key 检查均保留。

Records 分为 56 个约 500 字符的小片段，每 4 个片段组成一个 owner。每个片段证明原 `array` 在任意 fuel、tail 和 accumulator 上的等式；先组合四段，再一次绑定该约 2 KiB 的真实原文区间。这复用 higher agent 已过的 `fragments.py` / `block_single_bind.py` 模板，未导入其 geometry 数据或特定字段信用。14 个 owner 的累积等式连接全部 56 条记录，最后一段保留真实 `]` 和累积器 reverse。

最终 owner 对真实 records header、对象结束 `}` 和末尾 `\r\n` 分别作闭合原文绑定。`value_moment00_original` 保留任意额外 fuel；实例化为原整串长度加一的 fuel 29000，再使用已过 `parseChars_of_value_eq` 和 `SourceJson.parse_ofList` 回到原 `SourceJson.parse`。

Python raw planner 只提供候选 token spans、候选 AST 和 Lean 源文本，既不把 host parse 成功当作结论，也不执行 witness 数学检查。候选每个真实 span 必须由 Lean 的 `rfl`/list 定理绑定，每个 AST 必须由原 reader 的等式确认。完整根等式没有隐藏的解析成功假设。

## 验证环境、资源与回执

Lean `4.33.0-rc1`，commit `62eed1db4d67327ec8120be05f1a1b0847d74561`，runtime 位于 `/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux`。本层只依赖 Lean 与已接受的五个 helper，不需要 Mathlib/Consumer。24 个项目源构成完整闭包，其中 5 个 helper 原对象按 SHA 逐字复用；19 个 owner 在本地分别 normal 后独立 kernel。

每次上限为 4 GiB RSS、180 秒、1 线程；`maxRecDepth = 1000000`，诊断 `maxHeartbeats = 0`。记录的峰值为 20 ms 采样进程树 RSS。成功 normal 合计 63.965s，成功独立 kernel 合计 29.494s；这是各调用耗时之和，并非 P1 队列或全项目构建耗时。

| owner | normal 秒 | kernel 秒 | normal 峰值 bytes | kernel 峰值 bytes |
|---|---:|---:|---:|---:|
| P2OriginalSaving19ArchiveMomentData00 | 1.275 | 0.863 | 1619927040 | 1391079424 |
| P2OriginalSaving19ArchivePackedLoader | 1.114 | 1.088 | 1628422144 | 1390923776 |
| P2OriginalSaving19Moment00Input | 1.375 | 1.020 | 1626927104 | 1392488448 |
| P2OriginalSaving19Moment00Metadata | 3.068 | 1.921 | 1652998144 | 1408114688 |
| P2OriginalSaving19Moment00Parse | 1.298 | 0.968 | 1642053632 | 1404121088 |
| P2OriginalSaving19Moment00RecordsBlock000 | 4.571 | 1.857 | 1735581696 | 1448312832 |
| P2OriginalSaving19Moment00RecordsBlock001 | 4.399 | 1.840 | 1733365760 | 1448484864 |
| P2OriginalSaving19Moment00RecordsBlock002 | 3.728 | 1.677 | 1733214208 | 1448685568 |
| P2OriginalSaving19Moment00RecordsBlock003 | 3.714 | 1.580 | 1741230080 | 1448861696 |
| P2OriginalSaving19Moment00RecordsBlock004 | 3.588 | 1.585 | 1734057984 | 1448927232 |
| P2OriginalSaving19Moment00RecordsBlock005 | 4.187 | 1.769 | 1733988352 | 1449189376 |
| P2OriginalSaving19Moment00RecordsBlock006 | 3.623 | 1.876 | 1741979648 | 1449336832 |
| P2OriginalSaving19Moment00RecordsBlock007 | 3.580 | 1.501 | 1734295552 | 1449459712 |
| P2OriginalSaving19Moment00RecordsBlock008 | 4.027 | 1.765 | 1733914624 | 1449594880 |
| P2OriginalSaving19Moment00RecordsBlock009 | 4.108 | 1.646 | 1731989504 | 1449758720 |
| P2OriginalSaving19Moment00RecordsBlock010 | 4.170 | 1.728 | 1734438912 | 1449918464 |
| P2OriginalSaving19Moment00RecordsBlock011 | 4.024 | 1.647 | 1734586368 | 1450115072 |
| P2OriginalSaving19Moment00RecordsBlock012 | 4.296 | 1.633 | 1732235264 | 1450246144 |
| P2OriginalSaving19Moment00RecordsBlock013 | 3.820 | 1.531 | 1736736768 | 1450356736 |

最终 source SHA `8bfd640dcb02e36bede41d009479636d0151db248c0b2cd9c9a9b65e25b6ca2d`，object SHA `e1bd8bb9b86dfe44110ff9c46cae9f33daf380e285685aa1bdfd198178f960d0`。最终 parse 定理的精确 axioms 为 `[propext, Classical.choice, Quot.sound]`；parseChars 定理为 `[propext, Quot.sound]`。全部 164 个本轮打印的定理依赖集合均在 `PURE_PARSE_RESULT.json`，原始多行日志完整保留。

## 保留的失败与后续验收

唯一局部失败 `input-v1` 为 `momentRest00_end` 证明中未关闭的 `28999 ≤ 28999`，未输出对象；失败源、日志和回执均在 attempts/logs。随后 `input-v2` 只增加 `Nat.le_refl`，normal 和独立 kernel 均通过。失败 elaboration 输出的占位依赖不属于已接受信用；成功对象的精确 axioms 已重新核对。

`PURE_PARSE_SOURCE_MANIFEST.json` 固定全部 24 源和生成脚本，`PURE_PARSE_RESULT.json` 固定 38 份成功回执及完整失败记录，`BOOTSTRAP.json` 固定五个复用 helper 和正式输入 owner 的来源。此 pure 层 checkpoint 不需要因后续 typed decode 增加新文件而改写。
