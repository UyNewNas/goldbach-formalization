# P2 原完整审计与证据保全的空间分析

状态：只读调查和设计。没有删除、压缩、去重、挂载或改写远端文件；没有更改原工具、完整类型输出、资源选项或验收范围。本报告没有新增数学验收 credit。

## 结论

把最终原 CLI exporter 的完整 gzip 放在同一 job 的 `/tmp`，在该 job 结束前把全部非 immutable-native 原始成员无损保全为持久 xz，再由另一个 job 重建完全相同的原 gzip，是可复用的已验证机制。但它不消除原 owned audit 必须在 canonical 路径产生的三份大文件。当前已量化的自有诊断副本，也还不足以保证 A 原完整审计和剩余 324 审计全部容纳。

第二个只读 probe 的即时可用空间为 **379,904,000 B**。以实际 P3 full2048 的原格式三份输出 **510,596,115 B** 为规划锚点，raw 文件本身差 **130,692,115 B**，加原保全方案的 32 MiB 余量后差 **164,246,547 B**。这是对已测 P3 序列化的预算差额；canonical A 的名称和辅助声明不同，尚未实际测得 A 完整审计体积，不能把此数字称作 A 的已证下界或精确预测。

## 1. 实际证据和原工具

两个远端只读任务均 exit 0、完整 stdout 无截断：

| 任务 | 内容 | 耗时 | peak RSS | stdout |
| --- | --- | ---: | ---: | ---: |
| `25d1518ecc5446318698731dd01b7beb` | 我方诊断根的大 metadata / archive 路径、大小、SHA | 0.658 s | 16,977,920 B | 8,289 B |
| `c6de65f940764b889e845ede03c4c454` | mountinfo / statfs、一级各根有界 stat、遗漏 metadata | 19.246 s | 19,845,120 B | 202,910 B |

命令、提交回执、任务最终状态、原始 stdout、逐行解析结果均在本目录；解析用 Python 保留 `mtime_ns` 等大整数，没有经过 JavaScript 浮点再序列化。第二次检查包含 63 个顶层根的有界统计，排除了 protected native/source/object/audit/log/baseline 子树。该统计不是受保护目录的全树 `du`。

原工具固定如下：

- `run_winner9_private_audit.py`: `571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5`。
- `export_winner9_private_evidence.py`: `fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645`。
- 原 audit template: `2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b`。

原 audit `main` 只支持 modules、`--summary-name`、`--external-snapshot`、`--memory-mb`。它固定使用 `cwd/.lake/p2-private/lib` 和 `cwd/.lake/p2-private/audit`，没有合法的输出目录参数。原 exporter 的 `validate_receipt` 会重新读取原 audit.log，并核对 declarations.json 的完整解析值及 types.txt 的完整名称/类型串。改变 cwd、临时迁移 audit 根或把原文件换成压缩内容，不是本次允许的原 CLI 输出配置。

## 2. 三份完整类型输出的准确锚点

原 audit 的实际写入顺序是 independent replay、Audit.lean、audit.log、完整 parse_audit、declarations.json、types.txt、receipt/latest。最后两个文件必须和 audit.log 同时存在。新 attempt 下 declarations.json 的临时文件只是首次落盘过程，不需要另加一份已存在的大目标文件；receipt 等小文件另计。

对已完整核验的 P3 full2048 原 audit.log，运行锁定 `parse_audit` 的同一 AST，并按原 `write_json` 和 types.txt 拼接格式计算，得到：

| 文件 | 字节 |
| --- | ---: |
| audit.log（实际原件） | 171,331,783 |
| declarations.json（精确原序列化计数） | 171,694,035 |
| types.txt（精确原序列化计数） | 167,570,297 |
| 合计 | **510,596,115** |

合计 486.942401 MiB；仅按 4096 字节文件数据块向上取整为 510,603,264 B，还未算目录、receipt、其他阶段日志。P3 有 2,285 个 owned declaration、2,048 个块、131,072 个节点事实，全类型 UTF-8 文本共 167,176,820 B。canonical A 不是该诊断模块，不能直接授予它体积或数学 credit。

已完成一个只计数、丢弃输出的压缩测量：上述三份精确流形成 510,607,360 B tar，以 XZ preset 6 / CRC64 压缩得到 **23,593,560 B**，耗时 107.672138 s。没有持久写出该压缩包。它是未来保全增量的规划依据，不是未来最终包的已测大小。

剩余 324 中仍需重新审计的模块，其完整 raw 增量记作 R；当前不能用旧 receipt 个数或平均声明长度代替它。新 source/import/object 绑定必须由原 selector 决定是否可复用。

## 3. 已找到的我方诊断副本

完整路径、每文件 bytes / allocated bytes / SHA / inode / nlink 见 `own-large-file-inventory.json`。下表的简写根均在 `/workspace` 下。

| 原路径 | 字节 | 保全设计中的地位 |
| --- | ---: | --- |
| p24-nine-source-promotion-20261126/attempt-001/registry-before.json | 27,148,830 | 1087 完整已核归档中有精确成员 |
| 同目录 registry-after.json | 27,051,479 | 同上；与下一轮 before 同 SHA |
| p24-integration-proof-repairs-20261126/attempt-001/registry-before.json | 27,051,479 | b55 完整已核归档中有精确成员 |
| 同目录 registry-after.json | 27,176,800 | 同上 |
| p24-finite-selector-flags-20261126/attempt-001/selected-records.json | 5,660,806 | 诊断选定 registry 副本；需先保全与独立恢复验证 |
| p24-finite-selector-list-rec-20261126/attempt-001/selected-records.json | 5,660,806 | 与上一文件同 SHA；需保留两个历史路径映射 |
| p24-owned-flags-preflight-repro-20261126/attempt-003/inventories.json | 1,753,191 | 诊断 inventory；需先保全与独立恢复验证 |
| 上述七文件合计 | **121,503,391** | 已分配数据块共 121,524,224 B；尚未释放 |

两轮 four-registry 合计 108,428,588 B。1087 的两份 full324 快照各 181,315 B，四个主要快照合计 54,562,939 B；它们低于第二次大文件列表的 1 MiB 门槛，但完整成员索引仍在归档 descriptor 中。

两个已完整取回、逐成员核验并保存 Git blob 的归档必须保留：

- 1087: `/workspace/p24-nine-source-promotion-20261126/evidence-1087.tar.gz`，6,810,804 B，SHA `28344d7aa71ce2a13ae73cfa695af4fc9b849f444a6142687dc19817be1b3439`，20 成员。
- b55: `/workspace/p24-integration-proof-repairs-20261126/evidence-b55.tar.gz`，6,838,405 B，SHA `23d612dc0fb8266cb8928e1d11f69e4ebb9a4ed0e1429ddad91751071dc39c2c`，23 成员。

其他条件性候选仅列出，不批准释放：

- canonical `.lake/p24-cache-migration/attempt-001/ORIGINAL_DONOR_RECORDS.json` 16,227,671 B，`MIGRATION.json` 4,134,853 B，共 **20,362,524 B**。这是历史迁移证据，需要精确保全，并另核所有原工具、native qualification 和后续 recipe 是否仍要求其物理路径；当前不把它们直接删去的安全性视为已证明。
- canonical `.lake/p24-audit-export/source6e-full324-preflight-001/manifest.json` **11,997,843 B**。其精确 bytes 已在既有成功保全 xz 内，原 gzip 已由独立 job 重建验证；原路径目前仍保留。

三组名义逻辑体积合计 **153,863,758 B**。即假设全数释放且新保全文件占用为零，对当前空间与 A 锚点加 32 MiB 余量仍差 **10,382,789 B**。再加入约 52,392,168 B 的规划最终保全包，差额变为 **62,774,957 B**，尚未加 R 和后续 metadata。

这些是候选逻辑体积，不是已保证的实际可回收空间。OverlayFS 的层位置和其他作业占用会影响 `statvfs`；真正释放只能在另行批准的具体动作后读取实际空间增量。不存在凭此报告删除整个目录的授权。

第二次补查在我方已知范围没有找到更多大于等于 1 MiB 的旧 321/322/Bcancel registry 副本。大于 10 MiB 的其余项目属于 p25、p26 或旧研究工作，不能计入本任务可回收额度。小于 1 MiB 的 JSON/文本可能还存在，但其合计和物理消费者未审查；实际 isolated audit 日志即便位于我方诊断根，也不能算可释放副本。

## 4. 文件系统能力：未确认支持，未做写式测试

实际 `/workspace` 是 OverlayFS（statfs magic `794c7630`），mountinfo 给出 `lowerdir=/run/kata-containers/erofs-multi-layer/.../lower-0`、宿主路径 upperdir/workdir、`index=off`、`metacopy=off`。该结果没有揭示 upper 的实际文件系统，也没有证明 reflink / dedupe / 透明压缩可用。可见工具仅有 findmnt；btrfs、zfs、xfs_info、filefrag、compsize 均不可见。

没有执行 clone/reflink ioctl、压缩属性修改、去重、挂载或写测试。结论是 **没有已确认的透明压缩/CoW 节省路径**，不能把它写成肯定支持，也不能仅据 OverlayFS 断言所有底层完全不支持。

Linux 官方 OverlayFS 文档说明其上下层可由不同文件系统提供；直接改动正在挂载中的下层/上层底层文件系统不属于安全操作路径。删除 lower 文件通过 whiteout 表示，因此不能仅把候选 st_blocks 相加当作确定的 free 增量。资料：https://docs.kernel.org/filesystems/overlayfs.html 。

## 5. 诊断松散副本的最小无损保全流程（未执行）

1. 精确列允许的普通诊断文件路径，逐文件记录 bytes、SHA、物理 inode/nlink 和来源归档成员。排除 canonical 当前 records.json、所有实际 source/object/native/audit/log、原 baseline 和未确认消费者的文件。不能用一个目录前缀代替白名单。
2. 优先复用已有 1087/b55 完整归档；其现有压缩 bytes 已计入当前 free，恢复这些快照无需另写一套大包。其他尚未保全的 metadata 在 job-private `/tmp` 先生成无损包、完整 index 和恢复 recipe，持久写入需先满足实际包体积加 32 MiB 余量；fsync 后重读逐成员 SHA。
3. 在独立 job 中只用持久归档/recipe 恢复到新的 job-private 临时树，核每个恢复路径映射、bytes 和 SHA。不要把当前 mutable registry 再序列化来冒充历史 bytes。需要恢复原 JSON 的空白、顺序和全部记录。
4. 只有完整恢复 PASS 以及所有原工具物理消费者检查完毕，才能另由 owner 执行精确白名单释放。保留原 historical receipt 的 bytes，另加 release/reconstruction receipt，明确松散路径已不存在以及恢复入口；不在原路径放冒充原件的 marker。
5. 释放后重新测量实际 free，按实际净增量重新算预算。若仍不足，保留空间 blocker，不删 protected 文件、不减全类型输出、不扩大资源或另建环境。

## 6. 最终原 exporter 的同-job 保全方案（未实现）

### 前置原验收

最终使用当时真正通过的 source pin、原 ordered324 fingerprint、当前 compile registry 和原 audit receipts。固定完全相同的 qualified native context、runtime、571b/2975/fc0 等工具。当前 A 正在运行不等于 A owned 或全 324 已通过。

### 第一个 job：原 CLI 实际执行成功并立即保全

- 在 canonical cwd 调用完全不改的原 exporter，显式全 324，`--split all --output-dir` 指向本 job 独有且不存在的 `/tmp` 目录。这个参数属于 exporter；audit 没有对应参数。
- 要求实际 exit 0，并额外核 accepted 模块集合恰为 324、unselected 为空、duplicate_owned_declarations 为空。原 exporter 即使有 unselected 也可能 exit 0，故不能仅凭退出码宣称完整通过。合法淘汰的旧 rejected_candidates 不必为空。
- exporter 子进程退出后再启动保全，释放其把全部 Evidence bytes 留在 RAM 的占用。捕获原 manifest 的完整 bytes、原 all.tar.gz 的 bytecount/SHA、原 package metadata、modules 顺序和 transfer_page_bytes。
- 在同一 job 的 `/tmp` 中流式遍历原 tar。只把精确 qualified staged 根 `/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169` 下已资格冻结且逐 SHA 核验的成员作为共享输入；其余所有成员，包括 synthetic、canonical source/registry/audit/tooling 和其他外部文本，都保全精确原 bytes。旧包共享集合为 1,752 成员 / 4,089,256,851 B；最终必须核实实际清单，没有放宽根或自动排除新项。
- 使用已冻结 fc0 原 package 语义保全 trial tar，再把同一 tar 字节流无损转 xz；不需要落盘数 GB 的未压缩 tar。原 package 的 basename、gzip mtime、tar metadata、排序和 Python/zlib runtime 均保持。
- 精确 outer manifest 可以保存在 xz 的 `metadata/original-export-manifest.json` 内，不必在持久区再落一份约 12 MB 明文副本。保留小型 pointer/receipt 记录其 bytes/SHA/成员名。现有重建脚本已经从 bundle 中读取它。
- 用实际压缩大小、recipe/receipt 预算和 32 MiB 余量做持久空间检查；通过后 fsync/rename/重读全成员验证，再结束 job。原 gzip 只在 job `/tmp` 中存在，其路径要标作历史临时位置，不能称作持久下载文件。

### 第二个 job：独立重建

- 仅读持久 xz、冻结 recipe 和 exact qualified native 原件，在新的 `/tmp` 重建原 all.tar.gz。
- 不重跑 exporter 的 selector/main 生成新时间戳 metadata；复用保存的原 members、origin/role/index/modules/page bytes，由原 fc0 `package` 生成。
- 要求完整 gzip bytes/SHA 与第一个 job 一致，逐成员 exact names/bytes/SHA 一致，并核 native 和 bundle 前后未变。保存独立 verification receipt。
- 无需删除原大 gzip，因为它从未落在持久 workspace。旧 stage2 的 `--release-original` 删除步骤不适用于这个未来临时原包流程。相关派生 recipe 的字段和约束要明确区分“本 job 未删除”与“跨 job 仍在原路径”。

远端 `/tmp` 按 job 隔离，所以把保全任务排在 exporter job 之后会丢失唯一临时原包。第一次 job 的原 exporter PASS 不能替代 durable handoff PASS。

## 7. 资源和停止条件

持久额外空间公式是：

`A_actual + R_remaining_raw_audits + final_preservation_xz_actual + new_metadata + 32MiB - verified_release_net_bytes`。

旧成功保全 xz 为 28,798,608 B；加 P3 三份流的 23,593,560 B 计数，只形成约 52,392,168 B 的规划锚点。最终包不可在实际生成前承诺该大小。

job `/tmp` 峰值需容纳原完整 gzip G、outer manifest M、保全 trial gzip Q、最终 xz C 和小元数据；流式转换避免额外未压缩 tar。旧原 gzip 为 581,735,403 B，未来 G 未知。原 exporter 把约 4.089 GB shared native 文本及其他原成员 bytes 存在 RAM 中；旧完整 payload 4,302,650,543 B，加 P3 三份锚点为约 4,813,246,658 B，另有解析和 Unicode 对象。保持原资源限制并以实际结果为准，不能因为输出在 `/tmp` 就声称内存峰值下降。

旧 owned batch wrapper 的 256 MiB free 前置 guard 也须计入排程：A 完成后余量可能低于它；改顺序可提前暴露 R，却不消除总体空间缺口。不在本报告中改原 guard 或门控。

若已批准的具体副本保全与释放完成后仍不足，报告 `max(0, required - actual_free)` 的真实缺口。所有原 source/object/native/实际 audit/log 与原完整验收保持；本次读取、压缩大小计数、归档保全均不授予 canonical A/B/W/full324 或最终数学结论 credit。
