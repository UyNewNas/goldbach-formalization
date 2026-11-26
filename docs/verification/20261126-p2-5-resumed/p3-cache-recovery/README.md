# P3 编译缓存缺失：只读恢复核盘

日期：2026-11-26。状态：**历史验收保留；当前 P3 物化依赖链不可用。已准备外部对象包，未向 P3 安装或重建。**

## 当前结论

v7 所选择的 45 个项目模块中，41 个属于既有对象复用集合，4 个是待编译的 original consumers。本轮在本地现存文件、相关归档与 P1 环境中，已逐字节核实 **31 / 41 个旧对象的完整 SHA-256 匹配**。这 31 个对象去重后共 **23,647,104 字节**，可以恢复既有工作；没有必要重新证明或重新编译它们来替代备份。

在已完成的本地、P1、P3 核盘范围内，仍未找到精确备份的对象共 10 个，详见下表。P3 已完成全部 41 个目标的文件与 56 份相关归档检查；31 个可恢复对象中，21 个可直接从 P3 现存文件/归档读取，另外 10 个需要本地对象包补传。这个结论严格限于已记录的扫描范围，P2 未重复入队。

既有 P2.6 任务 `24a95f8ec1ab460c902d14fb4683f01b` 自行完成后，41 对象扫描 `72d6e64058c34aa4afc8c2876fa81b7e` 与 14 份原 witness 检查 `71474430b22e43708cfecced0bcb6348` 均正常完成，exit code 为 0。前者用时 186.209 秒，后者 0.228 秒。本轮没有停止、替换或改动已有编译任务，也没有向 P2 排入查询或编译。

本报告不新增形式化信用，不改变 P2.5 节点颜色，不把失败 aggregate 改为成功，也不撤销已有 owner 的历史验收。

## 机器清单与证据

- [RECOVERY_MANIFEST.json](RECOVERY_MANIFEST.json)：41 个对象的历史对象 SHA、源 SHA、旧路径、每个实测匹配位置、归档 member、不同 SHA 的同名候选及 receipt 状态。
- [expected-project-objects.json](expected-project-objects.json)：从 consumer005 的 40 个依赖对象加已验收 Decoded 抽取的完整目标集合。
- [READONLY_TASKS.json](READONLY_TASKS.json)：本轮远程只读任务 ID、作用、结果及 incident 关联任务。
- [local-41-scan.jsonl](local-41-scan.jsonl)、[p1-41-scan.jsonl](p1-41-scan.jsonl)、[p1-all-archives-scan.jsonl](p1-all-archives-scan.jsonl)：原始核盘输出。
- [p3-filesystem-scan.txt](p3-filesystem-scan.txt)、[p3-archive-scan.txt](p3-archive-scan.txt)、[p3-exact-hash-scan.txt](p3-exact-hash-scan.txt)：P3 已完成的三对象、归档及内容寻址备份核验。
- [p3-rescue-manifest-excerpts.json](p3-rescue-manifest-excerpts.json)：与本任务有关的 94 条备份记录及编译产物排除策略摘录；不是全备份清单。
- [p3-compiler-info.json](p3-compiler-info.json)：P3 编译服务验证的版本、路径、依赖 pin 与只读挂载配置。
- [p3-41-scan.jsonl](p3-41-scan.jsonl)、[p3-original-witnesses-scan.jsonl](p3-original-witnesses-scan.jsonl)：最终 P3 全对象/运行库及 14 原 witness 的实际输出。
- [expected-original-witnesses.json](expected-original-witnesses.json)：从历史 outer receipt 原样抽取的 14 份 witness 元数据，供按原始文件字节核对。没有重新序列化任何 witness JSON。
- [PAYLOAD_EXPORT.json](PAYLOAD_EXPORT.json)：31 个精确对象的外部打包元数据。对象包不在 Git 仓库内；其 31 个对象 member 已回读并逐一复核 SHA。
- [readonly_scan.py](readonly_scan.py)：本地只读搜索脚本。输出证据到标准输出；不执行 Lean，不创建、清理或改写编译缓存。

## 三个最初阻断对象

| 对象 | 字节数 | 历史 SHA-256 | 已完成核盘结论 |
|---|---:|---|---|
| `P2Saving16Cell00Decoded.olean` | 16,208 | `f700e8e866da0192152040a0853e27eab857ee007c0076df61613e3a849e534f` | 本地 consumer005/artifacts 有精确副本；P3 初始搜索未找到 |
| `P2Saving16Cell00FieldDecode.olean` | 246,368 | `be8aa94f8754aa8404da5dc12d8c4544ce3063b75af82ddbb51879e19ccf70eb` | 本地 field006/artifacts 有精确副本；P3 初始搜索未找到 |
| `P2OriginalSaving16OriginalInput.olean` | 93,650,960 | `72488821ccb01dec90188d2f09b0e3a73c0087b54c6c4bae4410a109b6f82f91` | 本地、P1 和已完成的 P3 三对象/归档/CAS 搜索均未找到 |

本地两个精确副本分别位于：

```text
docs/verification/20261126-p2-5-resumed/consumer-attempt005/artifacts/P2Saving16Cell00Decoded.olean
docs/verification/20261126-p2-5-resumed/field-symbolic-attempt006/artifacts/P2Saving16Cell00FieldDecode.olean
```

`OriginalInput` 的已验收源文件只有 1,714 字节，SHA 为 `792a5adf50263cfc1a0f67fb3d088c7612910388e4d1fa65db45c3c50065aca5`。它导入 `Lean` 和 `Mathlib.Data.Fin.VecNotation`，在 elaboration 时读取 `../goldbach-research` 中 source ID 0–14 除去 7 的 14 份原 witness。恢复该对象需要核实这些原始文件的完整字节身份；不能用解析后重新输出的 JSON 替代。

## 31 个可恢复对象的来源

| 来源组 | 个数 | 精确对象 |
|---|---:|---|
| 旧本地项目已有对象文件 | 8 | Decoder、Q96FloorCore、SourceJson、SourceJsonFuel、SourceJsonFuelBridge、DirectParse、SegmentedParse、StringCharBinding00 |
| `cell00_field_split_attempt003.tar.xz` | 10 | FieldBase、FieldSimp、Simplex00Decode 至 Simplex07Decode |
| `cell00_remaining_arithmetic_accepted.tar.gz` | 8 | Row01Arithmetic 至 Row07Arithmetic、AllRowsArithmetic |
| `field2_and_row00.tar.gz` | 1 | Row00Arithmetic |
| `cell00_typed_source_facts_accepted.tar.xz` | 1 | TypedSourceFacts |
| `p1_fastdet_accepted.tar.gz` | 1 | Winner9FastDetPure |
| 本地本轮已保存的两个 artifact | 2 | Decoded、FieldDecode |

所有完整模块名、路径、member、大小和实际重算 SHA 都在机器清单中。优先位置指向当前仓库已有归档和 artifacts；仅有旧本地对象文件可用的 8 个对象仍保留原路径，原文件没有改写。为恢复 driver 准备的外部包按内容 SHA 存储这 31 个既有对象，没有安装到远程路径。

该包为 4,110,796 字节，SHA-256 是 `ce1e92e0494b8e0f156ac34c27987929813dd5571cace331c59e0e5c1f7de56b`，包含 1 份元数据与 31 个 regular-file 对象 member。它不是新的编译结果；具体本地位置与 driver manifest 入口见 `PAYLOAD_EXPORT.json`。

P1 和其他本地项目还存在同名 `P2OriginalSaving19SourceJson.olean`，但它们的 SHA 为 `ec7361a2e508c323bf2dfa5f384d31a4bd71ffd47e032bfbf428c13bc1c2e467` 或 `865aaca31da595e69687b69f7dc0aa69edc01800d55e286cd5ba767239ac4d3f`。这些不同字节对象已明确排除；所选历史对象是 `50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7`。

## P3 直接复用与最小补传

[P3_EXISTING_OBJECT_MAP.json](P3_EXISTING_OBJECT_MAP.json) 逐项列出 21 个 P3 对象的完整 SHA、字节数、原路径或 archive/member。它们共 7,869,992 字节，直接读取 P3 已有文件，不需要传输。

本地独有的 10 个对象共 15,777,112 字节：Decoder、Q96FloorCore、SourceJson、SourceJsonFuel、SourceJsonFuelBridge、DirectParse、SegmentedParse、StringCharBinding00、Decoded、FieldDecode。它们已组成单独的 2,640,212 字节 xz 包，SHA 为 `b0719bd03bab9be02756e298cfef4bc44fa61cabbff722d00025ae460fe3ea80`，比传输原 31 对象包少 1,470,584 字节。包内每个对象均已回读校验 SHA。路径、driver manifest 与全量条目见 [P3_LOCAL_ONLY_PAYLOAD_EXPORT.json](P3_LOCAL_ONLY_PAYLOAD_EXPORT.json)。这里的“本地独有 10 个可复用对象”和下一节“仍缺失的 10 个对象”是两个不同集合。

P3 原 witness 已核实 14/14 均存在，大小和 SHA 与历史输入快照逐字节匹配，总 93,508,187 字节。因此不需要重新下载或重新序列化 OriginalInput 的输入数据。旧对象包所引用的首版 inventory 以 `RECOVERY_MANIFEST_BEFORE_P3.json` 原字节保留；当前 `RECOVERY_MANIFEST.json` 记录最终 P3 盘点。

## 暂未找到的 10 个对象

下表模块名前统一加 `ImbalancedChen.`。这是已完成的本地、P1 与 P3 扫描后的缺失集合；所有已找到的 31 个精确对象应直接复用。

| 模块 | 历史对象 SHA-256 |
|---|---|
| `P2OriginalSaving16DecoderChars` | `af720770a2f637e468c1f153b76891e0c6efedd627d3d144ca20024e638a1c7d` |
| `P2OriginalSaving16DecoderCompose` | `df91e32fa010265bb3ad1dba9f317233ce9c1b48beb0c668e5bca70666c452ed` |
| `P2OriginalSaving16FiniteCore` | `83923cb30eed3a39509324af01988e9708005913b304bb63fd2f56dcee82604c` |
| `P2OriginalSaving16OriginalInput` | `72488821ccb01dec90188d2f09b0e3a73c0087b54c6c4bae4410a109b6f82f91` |
| `P2Saving16CanonicalCell00Binding` | `fa7ad4fd4333a9e4fc13fb64448b91db539d65ecf51c6d572e98322e2ccd1837` |
| `P2Saving16Cell00OriginalJson` | `a1c280a1f6724e6fb7895f474a4a3f02ab7adcbf9b8c178efbedd97b24cc2e62` |
| `P2Saving16Cell00PayloadBinding` | `f1bff7f79f8e43f8a98e5eca39b520b928b46016a297af9272a6cb2b65f065c8` |
| `P2Saving16Cell00ScalarDecode` | `6a313fad2e0bb6a42a0a73e8f0c5c3360576b10e6de8f34511139711a6e64aeb` |
| `P2Saving16Cell00StoredFloors` | `f7c880efb54b82fe9c42d7e9f6216817eea15e00e50ec7545a0c73578566e3ae` |
| `P2Saving16Cell00TypedPayload` | `1c61948df2571b065f3b27ae2eeeff1202b942e39bb16229f93c9cc40b1e8c75` |

## Receipt 与历史验收边界

以下本地 receipt 原始字节均已重新计算 SHA-256，结果完全匹配既有引用：

| Receipt | 字节数 | SHA-256 | 历史含义 |
|---|---:|---|---|
| consumer005 `RESULT.json` | 5,049,315 | `bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88` | aggregate 失败；其中 Decoded owner 已验收 |
| field006 `RESULT.json` | 4,867,343 | `82123af5bc4f1e9334da8f578de11147effe73da0a7ab90b55459abbb25bcb0e` | FieldDecode owner 已验收 |
| consumer004 `RESULT.json` | 5,016,911 | `2c8f7b252d2e42f8ac09a6be391401258b0ed8fda1da57dd50cc7269f50b193a` | 失败历史保留 |
| OriginalInput private receipt | 5,086 | `8cca39ad7ae91d0be9d7b8f5d7a92251ca80e2f0b80a4f17f4816e77b41c34fb` | OriginalInput owner 已验收 |
| unguarded outer `RUN_RESULT.json` | 149,179 | `cb11eb092d12e3e1f08eb9dccad4ecbe53311f456babe6c0ccabe72b93c3fa65` | 原输入、源码和 owner 绑定历史 |

后两份 receipt 在 P3 rescue-export 内也有精确保存的原始字节：

- OriginalInput private receipt：`core-residual.tar.xz` 与 `priority-objects.tar.xz`，member 都是其完整 SHA。
- unguarded outer receipt：`evidence-receipts.tar.xz` 与 `priority-objects.tar.xz`，member 都是其完整 SHA。

检查已实际读取并重算 member 字节哈希。不能从“CAS 文件名恰好是 SHA”直接推定内容身份。

P3 rescue-export 的清单记录 OriginalInput 对象因 `rebuildable_compiled_artifact_extension` 被排除；归档重打包策略也排除了编译产物。因此它能够恢复许多源文件和 receipt，但不能视为完整编译缓存备份。该事实不说明项目 `.lake` 消失的原因或操作者。

## Lean 与 Mathlib 的可恢复性

P3 `compiler_info` 仍验证：

- Lean `4.33.0-rc1`，commit `62eed1db4d67327ec8120be05f1a1b0847d74561`。
- Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。
- Mathlib provider 是独立只读路径 `/mathlib/.lake/build/lib/lean` 及 `/mathlib/.lake/packages/...`，不是消失的 `/workspace/p25-q96-20261125/.lake`。

P3 物理核盘进一步确认 `/mathlib` 与主库目录是现存独立目录，主库有 8,311 个 `.olean`；VecNotation、Lean、leanchecker 的实际文件 SHA 均与下表一致。服务路径 `/toolchains/bin` 与旧历史路径 `/workspace/toolchains/lean-4.33.0-rc1-linux/bin` 的两个可执行文件都匹配旧 SHA。因此不需要因项目缓存缺失而重建工具链或先重编 Mathlib；完整的 5,312 模块外部快照仍由恢复 driver 按旧 frozen inputs 全量复核。

P1 与 P3 的下列实际文件都已确认与历史 receipt 完全匹配：

| 文件 | SHA-256 |
|---|---|
| Lean 二进制 | `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` |
| leanchecker 二进制 | `ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a` |
| `Mathlib/Data/Fin/VecNotation.olean` | `46f40fe44063e92eb5d66a5590cc1c83328e1c32c6dce91dd6d860ae20e3e03f` |

本地现存 p34-runtime 中的 VecNotation 对象也匹配此 SHA。P1 的 Mathlib 路径最终解析至 `/workspace/goldbach-formalization/.lake/packages/mathlib`；源 pin 相同。这里只确认所列文件；未把单个库对象的匹配外推为 5,312 个外部模块及其所有 companions 均已复核。

## 搜索范围与限度

本地扫描访问 422,567 个文件条目，检查 184 份候选归档。扫描跳过 Git 历史、第三方应用缓存、虚拟环境和工具链目录，不跟随目录符号链接。权限拒绝的 `lost+found`、一个断开的旧 FastDet 路径和六个断开的旧 P2.1 zip 路径均在原始输出保留；其他已找到的 exact FastDet 副本不受这些断链影响。

P1 文件扫描访问 320,253 个条目，无扫描错误。后续补查全部 157 份 tar/zip 归档，无归档错误。归档按 member 原始字节重算目标哈希，不提取或覆盖现有文件。没有把本地找到的同名但不同 SHA 对象加入复用集。

P3 初始三对象扫描访问 306,522 个文件且无错误，另检查 56 份相关归档和内容寻址备份。后续完整 41 对象扫描访问 307,108 个文件、完成全部 56 份候选归档、无扫描/归档错误，找到 21 个不同的精确旧对象，均已在本地 31 个可恢复集合内。原始输出保存在 `p3-41-scan.jsonl`。

## 最小后续工作

恢复应先直接复用 P3 已有的 21 个 exact 对象，并补传本地独有的 10 个 exact 对象及相应原始证据。对剩余确实没有精确副本的 10 个对象，才使用既有、固定 SHA 的源码与原始 witness 做最少重建。无需改写数学证明，也不应重建已经找到可靠副本的项目对象或在未证明库缺失前重编 Mathlib。

对象恢复之外，v7 仍会校验历史 receipt、日志、源复制、完整外部快照以及 consumer005 的 16,646 条 frozen paths。恢复三个最初阻断对象并不足以宣称整条链已经可用。旧 receipt 中的状态、路径和哈希不能被重写以迁就新目录；重新编译生成的字节如果不匹配旧对象 SHA，应建立真实的新验收记录，并保持原有 normal、replay、完整 owned inventory 与源/依赖哈希门槛。

详细执行计划由另一只读审查任务维护于 `docs/source-only/20261126-p2-5-cache-rematerialization/`。本核盘只提供现有字节证据与缺失边界；本轮没有运行恢复、Lean、leanchecker、依赖构建、Git 暂存或 Git 提交。

