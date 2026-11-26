# Cell05 剩余九连接：15 个原验收 row-owner 的独立恢复调查

## 结论

已检查的本地文件、相关已下载包及内容哈希备份索引中，没有找到这 15 个对象的同字节副本。已知的原对象与完整 45 条验收链仍定位在 P1 的原 stage/archive。15 份源码、原 RUN/SUCCESS/EXPORT_MANIFEST 和精确对象 pins 已在本地；这些元数据不能替代对象本体或完整验收证据。

没有提交任何 P1/P2/P3 查询或任务，没有运行 Lean，没有复制或重建受限 row001 完整证据。P3 的现时全盘缺失并未声称已证明：现有记录未给出具体传送、对象胶囊或已验收 stage 候选，故按要求没有无依据地排队搜索。

## 检查范围与结果

- 精确文件名扫描覆盖 `/workspace/scratch`、`/tmp`、`/mnt/data`，包括 `.lake` 等构建目录：15 个对象全部无匹配。
- 七个明确相关的本地 archive 已核对成员名。Cell05 completed-evidence 包有基础 15 个对象；所需的新 15 个均不在其中。row-network v2/v3、row-capsule-builder 和已有 transfer 包均没有对象成员。
- 已下载 workspace-rescue 的 44 份 JSON 内容索引，共 133,729 条字典记录，另有 448,868 行 restore manifest。按 15 个对象 SHA、完整 rows15 archive SHA 和 198 个原验收步骤证据 digest 查询，匹配数为零。此步骤未读取备份 archive 本体。
- 原 CLOUD_EXPORT_SUMMARY 与既有 ACTIVE_JOBS 记录均写明 `full_archive_transferred: false`；原验收任务 `job_03820698aca949449a3c8543e9bb8652` 成功，45 步、5,147 owned declarations。
- 已有成功 P2 inventory 的 15 个目标记录均没有对象或 source 副本；本轮没有再次占用 P2 队列。
- P3 记录里只找到 README 的可选运行计划，没有实际 rows15 接收/验收 locator。旧 P3 inventory 的检索模块集合不包含这 15 个，不能拿它冒充这次对象缺失证明。

## 逐对象缺口

以下 suffix 均带前缀 `ImbalancedChen.P2OriginalSaving19Geometry05Scalable`。所有对象的已知原路径为下面根目录加 `ImbalancedChen/<完整模块末段>.olean`；各项当前状态均为「原 pin 已核对；可访问副本未找到」。

```text
/workspace/p26-continuation-59264dd64286/scalable-geometry-cell05-complete-v3/objects
```

| 模块 suffix | Object bytes | 原 Object SHA-256 |
|---|---:|---|
| `SimplicesBlock002` | 1,279,416 | `6b1f32d2d893e65494068515b9ae0ddbd4e58626bdbb381d90ab2960f1c16567` |
| `TypedRows002` | 611,528 | `90263f63732d9e8a929da58f42cff8b38c7502277e103ed01b278be8ed2c8132` |
| `SimplicesBlock003` | 1,325,488 | `604234c70514117017bbdb33c42eeb42c480d21fbb2c25253956088d15c9c9d1` |
| `TypedRows003` | 630,200 | `94d6f22d25498a783feaeba215610fe87575009b7501ef608e699939d90ff355` |
| `SimplicesBlock004` | 1,264,856 | `1fa5d4749bf12de410ca576fa7626d37350602d37dc1d5648d121775f078ffc6` |
| `TypedRows004` | 605,592 | `f53c21a717596abeb398a39b653fe19ac8ab9dd395aca978b020656b0de7f234` |
| `SimplicesBlock005` | 1,268,032 | `d5d532859150454436278aded2a165030060c51cd371d20b9bb4759dff9891c8` |
| `TypedRows005` | 607,784 | `f7951c0169a50ff2c13289d50e40d1209e6c6d863e3ffbdfbdb2a4243c7d12ed` |
| `SimplicesBlock006` | 1,258,224 | `6bf376fcd50bd77f0d95f61b0d13716c4e46f6be0b2ef47b4080849bf353c284` |
| `TypedRows006` | 603,008 | `10c2242b2e64f4b21063c9483a2a72631807cdbaecbe553df4a133c99eccc965` |
| `RowsNode002To003` | 32,416 | `9458ca3bc701ff39fc05e06f7247564d61d0950476206afd85ffc455e0392808` |
| `RowsNode004To005` | 32,416 | `00b2d42d4e4173451b6df145acd98c41a445f75c2ff59d7488efab84e443dfd0` |
| `RowsNode000To003` | 31,680 | `7587385aef3467d25287187556d2839f75ca89873832fda7175a9fb69006b596` |
| `RowsNode004To006` | 37,480 | `32b908a1c31d0f1ac32e53aab3ac237c88e64f6c2eaf9a567aa9be6be6cbe377` |
| `RowsNode000To006` | 36,984 | `ad5bb48df75c8d9a163cf7adbd956409eb41d22fd98d557d2673a09a0ada8711` |

对象合计 **9,625,104 bytes**；对应源码合计 **2,026,335 bytes**，全部本地源码 pins 已验证。JSON 清单保存每个对象的完整原路径、archive member、源/对象 pins 和三个原 accepted-seal pins。

## 可恢复的原始 archive

```text
/workspace/p26-continuation-59264dd64286/scalable-geometry-cell05-complete-v3/exports/phase1-p1-cell05-complete-rows-v3-v2-evidence.tar.xz
bytes: 2486324
sha256: bb4ee98e403f46f28d5882ff4f20d6b2c1e8e1608c63befc398e06b4668b104d
```

该原包的 435 个成员含 15 个新对象及原验收证据。当前可用的是 manifest 与摘要，完整 archive 本体未找到。已有 `build_row_capsule.py` 和独立审查过的 source-only builder 包，可在原 P1 材料恢复可读后复核 45 条链并制作复用胶囊；此次没有执行 builder，也没有将缺失对象重新编译为替代品。

## 继续 blocked 的九个目标

- `SimplicesValue`
- `SimplicesField`
- `PhysicalVolumeField`
- `WholeValue`
- `WholeParse`
- `DecodeFields`
- `Decoded`
- `ShapeRows`
- `Shape`

这九个目标各自传递依赖上述全部 15 个对象。14-target 独立路线不受该缺口影响，其已排队 dispatcher 保持原样。
