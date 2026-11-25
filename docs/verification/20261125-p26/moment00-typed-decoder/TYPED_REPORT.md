# moment00 原 parser 与真实 typed decoder：本地完整结果

## 已关闭的最终义务

以下无假设定理已通过 normal 与独立 `leanchecker`：

```lean
ImbalancedChen.P2OriginalSaving19Moment00Decoding.momentPacked00_parse_decode :
  (SourceJson.parse (String.ofList momentPacked00.toList) >>= decodeMoments) =
    .ok momentConcrete00
```

左侧使用正式 v4 候选的生产 FQN `ImbalancedChen.P2OriginalSaving19Archive.momentPacked00`，原样 `SourceJson.parse`，以及真实 `ArchiveSchema` 中原样的 `decodeMoments`。右侧是具体 `Moments` 结构值，含全部九项 metadata 和原顺序的 56 条记录。每条记录明确固定 `simplexId`、10 个 `factorFloorsQ80 : Int`、`oldFloorQ96` 与 `newFloorQ96`；本包因此绑定了全部 560 个 Q80 整数及 112 个 Q96 整数，不依赖默认值或 success tag 替代具体字段。

最终源：`project/ImbalancedChen/P2OriginalSaving19Moment00Decoded.lean`，SHA `8a269a5a9e0387deb15c7a145cf1a1bbdc94fe106babf84d20827c8c7ebb8151`。本地 object SHA `a93385473fa8f9444663524528dc4e89177fd5383a813dae0ab4f61f84bffa18`。最终 normal 1.406s / 2,137,665,536 B 峰值；独立 kernel 2.586s / 1,807,523,840 B 峰值。两个公开最终定理的精确 axioms 均仅为 `[propext, Classical.choice, Quot.sound]`。

## 明确的 metadata 值

| 原字段 | 具体解码值 |
|---|---|
| cell_id | 0 |
| source_witness | eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json |
| dimension | 8 |
| vertices_per_simplex | 9 |
| factor_count | 10 |
| log_degree | 6 |
| exp_degree | 3 |
| log_floor_denominator | 1208925819614629174706176 |
| final_floor_denominator | 79228162514264337593543950336 |

具体 records 数值全部保留在 14 个 `Moment00DecodedBlock000` 至 `013` owner 的 `momentTypedRecord000` 至 `055` 定义。最终 `momentConcrete00.rows` 是这些已证值按原顺序累积后转为 Array；没有丢弃、去重或重排 records。

## 原件、schema 与 pure 层复用

原件仍为 28,999 B 的 `eighth-third-moment-refinement-20261009-a23-low-00.witness.json`，SHA `d88e9d02334dfa840f81c0e2be8e97d559978ac3848fdea13990deced9a65052`。实际本地读取路径、生产相同 relative path、原样 loader/Data00 与 CRLF 保留均见已冻结 `PURE_PARSE_REPORT.md` / `BOOTSTRAP.json`。所有 pure 源、对象及回执在本轮保持逐字不变。

真实 Schema 源 SHA `b877c0c35ace12cd76e0ed737b3a4b1ff3917fa15c4cc32b961450ee4761418b`，object SHA `8c3b41bd6b27e92b7a3c724b5d5ee9b191b4a4079fb40bd3ff5daad34129f9cc`，逐字复用 Root 已 normal/kernel 通过的对象。本轮不重编 Schema。`parseInteger` 至 `decodeMoments` 的原始 5399 B 切片 SHA 仍为 `21b86bcf4e04123dc6841cd25e50dcd073ecd9c9ac4c077b0174578a96c57a30`。Schema 的原验收与来源文件副本保存在 `typed-provenance/ArchiveSchema/`。

本轮使用相同 Lean 4.33.0-rc1 / commit `62eed1db4d67327ec8120be05f1a1b0847d74561` 与 Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。`run_typed.py` 固定 Schema 源/对象、纯层所有源/对象、原件和副本，以及 Mathlib pin 与直接 schema import 源/对象的指纹。每个命令前后均核对，无依赖重建。

## 组合方法

每条原 JSON record 从已通过原 parser 片段的 `momentRecordsChunkNNNPush []` 用 `List.head` 提取，携带 `List.cons_ne_nil` 非空证明；没有 `headD`、`getD` 或 fallback。对应 `Push acc = originalRecord :: acc` 由 `rfl` 闭合，因此数据来源仍是原解析结果。

每个具体 `decodeMomentRecord originalRecord = .ok concreteMomentRecord` 用普通 Lean kernel 的 `decide +kernel` 关闭。每四条记录使用既有 `List.mapM_cons` / `mapM_append` 等式组合；同时保留原数组累积器 reverse 的顺序语义。14 块覆盖全部 56 条记录。

metadata owner 对原 root 的九个字段逐一给出确定的读取结果，再证明一个记录列表仍任意的 `decodeMoments_momentObjectWithRecords`。`Moment00DecodeFromRows` 把 `List.mapM_toArray` 和 Except bind 的改写放在抽象记录列表上完成。最终 owner 仅应用这些不透明定理到已证明的实际 56 条记录，再与完整 pure parse 定理组合；不会在最终组装时重新运行整组 decoder。

这只是原定义的证明表达拆分。最终公开陈述与 `momentConcrete00` 定义在修复前后逐字相同，检查记录见 `TYPED_RESULT.json`，proof-only diff 见 `TYPED_GLUE_REPAIR.diff`。

## 资源回执

所有调用继续使用 4 GiB RSS 监测上限、180 秒、1 线程、`maxRecDepth=1000000`、`maxHeartbeats=0`，未提高预算。17 个新 typed owner 各做一次成功 normal 与独立 kernel；记录块与 metadata 一旦通过便没有重编或重复核验。合计成功 normal 68.996s，成功 kernel 71.524s；各次详细资源数据如下。

| owner | normal 秒 | kernel 秒 | normal 峰值 bytes | kernel 峰值 bytes |
|---|---:|---:|---:|---:|
| P2OriginalSaving19Moment00DecodeFromRows | 2.056 | 1.965 | 2136018944 | 1806209024 |
| P2OriginalSaving19Moment00DecodeMetadata | 3.457 | 2.840 | 2186764288 | 1834430464 |
| P2OriginalSaving19Moment00Decoded | 1.406 | 2.586 | 2137665536 | 1807523840 |
| P2OriginalSaving19Moment00DecodedBlock000 | 4.628 | 4.960 | 2271133696 | 1934868480 |
| P2OriginalSaving19Moment00DecodedBlock001 | 4.022 | 4.555 | 2274545664 | 1935040512 |
| P2OriginalSaving19Moment00DecodedBlock002 | 4.703 | 4.984 | 2272006144 | 1935310848 |
| P2OriginalSaving19Moment00DecodedBlock003 | 4.911 | 4.740 | 2272694272 | 1935724544 |
| P2OriginalSaving19Moment00DecodedBlock004 | 4.484 | 4.096 | 2273259520 | 1936117760 |
| P2OriginalSaving19Moment00DecodedBlock005 | 4.066 | 4.391 | 2275037184 | 1936461824 |
| P2OriginalSaving19Moment00DecodedBlock006 | 4.465 | 4.356 | 2276098048 | 1936465920 |
| P2OriginalSaving19Moment00DecodedBlock007 | 4.402 | 4.233 | 2273386496 | 1936867328 |
| P2OriginalSaving19Moment00DecodedBlock008 | 4.262 | 4.369 | 2269483008 | 1936662528 |
| P2OriginalSaving19Moment00DecodedBlock009 | 4.568 | 5.228 | 2271592448 | 1937362944 |
| P2OriginalSaving19Moment00DecodedBlock010 | 4.285 | 4.603 | 2277249024 | 1937719296 |
| P2OriginalSaving19Moment00DecodedBlock011 | 4.385 | 4.577 | 2274926592 | 1937723392 |
| P2OriginalSaving19Moment00DecodedBlock012 | 4.470 | 4.437 | 2270912512 | 1937997824 |
| P2OriginalSaving19Moment00DecodedBlock013 | 4.428 | 4.604 | 2271268864 | 1938182144 |

本轮共打印并精确解析 185 个定理的 axioms，见 `TYPED_RESULT.json`。成功 metadata 源保留三个 `unusedSimpArgs` 警告（两个分母解析 lemma 和 `pure_bind`）；它们不是失败，原始日志保留。没有为了清理这三个警告改写或重编已通过对象。

## 失败基线与修复

`typed-records-v1` 首块是表达失败：四个解码等式不能用 `rfl` 直接闭合，且 list mapM 化简后仍需 `rfl` 收尾。无对象生成。源、日志和生成器前像均保留；v2 只改证明表达为 `decide +kernel` 并增加收尾，不改 record 数值或公开陈述。

`typed-whole-v1` 在 11.470 秒、采样峰值 4,299,735,040 B 时被 4 GiB 监测停止，无对象生成。旧源没有前置 flush marker，因此空日志不能单独确定失败在何个内部 elaboration 步骤。本轮未加预算、未重复整组 decode；改为单独证明抽象 mapM/bind 接头后，`typed-whole-v2` 的各阶段 marker 与最终两项定理均正常完成，且独立 kernel 通过。

这两次失败及所有错误占位输出不属于通过信用。失败源、回执、日志完整保留，成功版本重新核对 axioms。

## checkpoint 与后续接线

`PURE_PARSE_*` 是已冻结、未改变的第一 checkpoint。`TYPED_DELTA_WHITELIST.json` / `TYPED_PACKAGE_MANIFEST.json` 只列出本次新增或修复保留文件，不重复 pure 的既有 whitelist，不包含任何 `.olean`，也不重复 raw input。`FULL_SOURCE_CLOSURE.json` 固定最终 42 个项目源闭包；其中 36 个 owner 在本目录 normal/kernel 通过，5 个 helper 与 1 个真实 Schema 按既有 SHA 复用。环境无关 canonical source closure SHA 为 `a9e32a772854b5668232bb8a702fcc3dd17ce560d9c013024606500bd861899f`。

本结果只为 cell00 的真实 parse 与 typed value 绑定提供本地证据。尚未声明 P1 strict、所有 13 个 moment/geometry cells、旧 Core 原 String literal 闭合等式、typed shape 总验收、Q80/Q96 数学 floor 正确性、pulling geometry 或 P2.6 最终积分端点通过。待正式新版 Core/all-input maps 接好，Root 可通过 index 0 的原定义展开把此直接生产 FQN 定理接到 `momentParse 0`；本包不加载所有其他输入或216个分析供应商来冒充该后续验收。
