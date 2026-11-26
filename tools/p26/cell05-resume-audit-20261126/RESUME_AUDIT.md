# Cell05 独立 14 个连接目标续跑条件审计

## 结论

14 个原有 source candidate 的依赖图不含 P1 的 15 个新 row owner。它们可复用 P2 历史已验收的 15 个基础供应商与 73 个 field owner，共 88 个源/对象对；14 个目标实际使用其中 83 个。目标源码及 owned audit 均逐字节匹配已有两个 source capsule，未修改源码或重新计算任何旧模块。

当前尚不能称为可以直接执行：现有 `scalable-cell05-connections-run` 的 join 固定要求 103 供应商与 P1 row capsule；新连接 runner、exporter、stage entrypoint 和最终 workflow/join 清单尚不存在。P2 既有对象、完整证据 archive、runtime snapshot 的当前物理存在及 pins 还待唯一已排队的只读任务返回。本审计没有运行 Lean、编写新 runner、取消任务或更改旧文件。

## 精确目标与依赖

下表全部模块均带前缀 `ImbalancedChen.P2OriginalSaving19Geometry05Scalable`。`READY14_TARGETS.json` 保存完整模块名、精确源/audit pins、原始 archive/member、每个目标的完整新旧依赖集合与拓扑顺序。14 个目标预期 42 个新 normal/kernel/owned 步骤，当前接受数为 0。

| # | 原始目标 suffix | 直接 project imports | 旧供应商闭包数 |
|---:|---|---|---:|
| 1 | `Active8EnumerationHeader` | `Metadata05` | 9 |
| 2 | `Active8EnumerationField` | `Active8EnumerationHeader`, `Active8EnumerationValue` | 31 |
| 3 | `VerticesHeader` | `Active8EnumerationField` | 31 |
| 4 | `VerticesField` | `VerticesHeader`, `VerticesValue` | 39 |
| 5 | `VertexValuesHeader` | `VerticesField` | 39 |
| 6 | `VertexValuesField` | `VertexValuesHeader`, `VertexValuesValue` | 51 |
| 7 | `AllOriginalConstraintMinimaHeader` | `VertexValuesField` | 51 |
| 8 | `AllOriginalConstraintMinimaField` | `AllOriginalConstraintMinimaHeader`, `AllOriginalConstraintMinimaValue` | 65 |
| 9 | `FacetVerticesHeader` | `AllOriginalConstraintMinimaField` | 65 |
| 10 | `FacetVerticesField` | `FacetVerticesHeader`, `FacetVerticesValue` | 68 |
| 11 | `FaceLedgerHeader` | `FacetVerticesField` | 68 |
| 12 | `FaceLedgerField` | `FaceLedgerHeader`, `FaceLedgerValue` | 83 |
| 13 | `SimplicesHeader` | `FaceLedgerField` | 83 |
| 14 | `ShapeArrays` | `VerticesNode000To001`, `VertexValuesNode000To003`, `TypedFacetVertices000`, `FaceLedgerNode000To004` | 42 |

14 份源码共 57,284 bytes，14 份 audit 共 38,476 bytes。前 13 个属于 parse/decode 原始批次，最后一个 `ShapeArrays` 属于 finite-shape 原始批次。源 capsule 共 49 与 18 个 regular members（包含各自 manifest），均已逐项核对所选源码与 audit 的原始字节。

剩余九个原始目标保持 blocked：`SimplicesValue`, `SimplicesField`, `PhysicalVolumeField`, `WholeValue`, `WholeParse`, `DecodeFields`, `Decoded`, `ShapeRows`, `Shape`。每个均传递依赖全部 15 个 P1 新 row owner。没有用额外计算或旧模块重编替代这些依赖。

## 88 个可复用供应商

`FIELDS88_SUPPLIERS.json` 保存全部 88 个模块的原始 P2 project/objects 路径、bytes/SHA、精确 imports、来源锚点和 73 个新 field 的 219 个 accepted-receipt pins。全部 88 个对应源码在当前 repo 的 bytes/SHA 已验证。对象 pins 对旧 15 个比对 fields RUN 原始 supplier context，对新 73 个比对固定 EXPORT_MANIFEST 的 objects 成员。

88 个源共 2,456,591 bytes，对象共 15,079,848 bytes。原始 registry 期望 sidecars 为空；本审计不将历史期望冒称为新的 P2 实物观测。83 个是所选 14 目标真实外部闭包；保留完整 88 个 provider 最少改变原工作流。其余五个为 `RowsNode000To001`, `SimplicesBlock000`, `SimplicesBlock001`, `TypedRows000`, `TypedRows001`。

已知根目录：

```text
/workspace/p26-continuation-59264dd64286/scalable-geometry-cell05-fields-v1/project
/workspace/p26-continuation-59264dd64286/scalable-geometry-cell05-fields-v1/objects
```

“21 个 typed/row owner 已验收”不能推导这 21 个对象全部当前存在于 P2：其中 6 个在原始基础闭包，另 15 个的原验收在 P1 独立 stage。唯一排队盘点同时检查精确 103 个 supplier，若此前已发生传送可由结果证实。

## 不需新增 P2 shell 即可取得的 pins

完整 fields73 archive 的固定身份为：

```text
/workspace/p26-continuation-59264dd64286/scalable-geometry-cell05-fields-v1/exports/fields-p2-cell05-fields73-v1-v1-evidence.tar.xz
bytes: 2059356
sha256: aa955ea9e64ba08e1902ff53a19d1e8db87e8aa371a189b9f54edfc3d1ccafbd
```

本地 `accepted-metadata/fields73/EXPORT_MANIFEST.json` 已保存 1,432 个 payload pins；连同 manifest 共 1,433 个 archive members。其中 73 个新 field 对象共 7,868,416 bytes；包不含旧 15 个 supplier 对象。`SUCCESS.json` 已保存全部 219 个 accepted-receipt pins，且这些 pins 与固定 export manifest 一致。原始 proof job 为 `ba5a4a916d8e43ee9f5747fa6b0976d1`，本地 ACCEPTED_CLOUD_SUMMARY 记录其成功；没有为获取已有 pins 重跑 shell 或 proof。

完整 archive 本体未在 `/workspace/scratch`、`/tmp` 的精确已知文件名及 fields/evidence 命名包搜索中发现。当前 Git commit `552531bf9ee992b249f180c1a1b2b395989c3f94` 的 fields 文档树（本地递归 tree 与 GitHub connector 顶层查询对应）包含 ACCEPTED_CLOUD_SUMMARY 与 source/workflow 包，没有完整 evidence archive。没有检查其他任意分支、release、无关命名 archive；不能据此声称所有远端历史版本均不存在。本地 source/workflow 包不能替代该对象/证据包。

## 现成代码可复用点及最小后续改动

1. 保持原 23-target manifest 与 source/audit 字节不变；另冻结 14-target selection 和原 fields88 supplier 子集。每个新 owner 的实际 external object inventory 按原 imports 计算，provider 可保留 88 个 exact namespace。
2. 建一个独立 fields-only join 入口，复用 `evidence_io.checked_export`、`supplier_capsule.full_export_view`、`supplier_capsule.validate_original(..., 'fields73')`、`supplier_join.context_shared_reader`、`baseline_from_fields`、`check_provider`、`resolved_paths`。须重新读取原始 219 条链并确认完整 owned inventory，保持原 receipt 及绝对路径上下文，通过显式路径映射解析；不得仅凭 SUCCESS 字段接受。原 15 个 closure 仍须验证 156 个基础控制/证据文件及 raw05 current-context kernel addendum。
3. `supplier_join.joined_inputs`、`validate_join` 和 `install_join` 当前硬编码 103/45+219 及 row capsule，因此现成 `join_suppliers.py --provider ... --row-capsule ...` 不是这 14 个目标的可直接使用入口。应在新入口调用现成验证函数并冻结 fields88 专用 contract，保留现有完整 join 不动。
4. 复用 `runtime_compat.runtime_evidence`、`capture_runtime_guard`、`check_runtime_guard`。P1/P2 历史 probe summaries 与 MCP 成功记录已在本地，runtime 比较不需要再连离线 P1。P2 的完整 snapshot 固定为 `/workspace/p26-continuation-59264dd64286/cell05-runtime-P2-v1.json`，12,773,129 bytes，SHA `fd7749b90ebc482c9450ce6021864370aec0a6459d7c14470b4cf8698434edd7`。先重哈希已有 10 个 runtime root 的 59,579 个文件，再建立只读 stat guard；不复制 8,042,816,961 bytes runtime，不增加 compatibility kernel replay。
5. 新 normal/kernel/owned driver 最小来源是已验收的 `tools/p26/scalable-cell05-fields/verify_fields.py` 和其 `receipt_checks.py`、`receipt_support.py`。需要显式调整新 tool/stage/schema、14-target/42-step 与 88-supplier 配置和 frozen-input contract，接入上面的供应商 join/runtime guard；保留原始 argv、context、完整 owned、恢复与成功对象缺失时拒绝重跑的检查。旧 driver 的 73/15 固定配置不能原样执行新任务。
6. stage/export 入口可机械复用原 `export_fields.py` 及 archive helper，限定新 14 个对象/证据，提供新 schema 与完整 regular-member readback。新入口、driver、exporter 及 workflow 清单均需冻结和独立 review 后再运行 42 个新步骤。本审计只列出改动，未实现这些组件。

## 当前外部阻断与交接

唯一新提交为只读 inventory job `717a19f6ceff43218793705784a92e52`（120 秒 / 256 MiB / 1 CPU），提交时 queued、queue position 3。本审计先检查了 system_info/compiler_info，没有取消其他会话任务，没有绕过队列或忙轮询。已保存脚本、请求、实际提交结果与系统快照。P2 当时空闲磁盘 568,356,864 bytes；保留既有树并使用硬链接可避免不必要复制，实际新 proof 的资源许可仍应以执行时系统状态判断。

后续先读取该唯一 job 的最终 metadata：确认 88 个源/对象、原证据 archive 与 runtime snapshot/二进制 pins 的可用性。此盘点不解包 archive，也不逐条验证 156 个基础证据；后者须由后续 fields-only join 调用现成 `baseline_from_fields` 完成。然后才补写并独立审查上列最小本地执行组件。P1 离线不会成为 14-target 路线的依赖；P2 队列及其现存材料的可验证性仍是当前云端阻断。九个依赖 P1 的新目标继续保持 blocked。

此次审计涉及 parse/decode/finite shape 的部分新连接，未声称 Cell05 整体解码验收、积分结论或 P2.6 完成。
