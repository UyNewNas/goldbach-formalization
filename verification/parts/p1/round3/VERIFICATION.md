# Part 1 round 3：实际验证记录

**VERIFIED：本轮六个指定目标的当前源码已通过六次严格原 Lean 前端编译、六次原 `leanchecker` 调用，以及完整定义模块声明审计。**

此结论来自 [VERIFICATION.json](VERIFICATION.json)，记录时间为 `2026-10-12T21:45:03.892552+00:00`。回执 SHA-256 为 `4bd9c3220492d29202625fbfcf54745b34458eac7394fd7443bb74251c34b8db`。它不把原前端 API 编译标称为 stock Lean CLI 或公共根的 `lake build` 成功，也不声称重新 replay 所有导入模块。

## 实际执行与覆盖

| 项目 | 实际结果 |
| --- | --- |
| 指定目标严格编译 | 6 / 6，全部实际返回 0 |
| 原前端 | `Lean.Elab.runFrontend`，`trustLevel = 0`，正常初始化 |
| 警告模式 | 六个目标均 `warningAsError = true` |
| metadata adapter | `false` |
| 原 checker | 6 / 6，分别实际返回 0，每次日志准确 replay 对应模块 |
| 完整定义模块审计 | 5 个模块，100 个声明；包含 private/generated declarations |
| 实际传递公理并集 | `Classical.choice`, `Quot.sound`, `propext` |
| 工具链 | `leanprover/lean4:v4.33.0-rc1`；原二进制、原驱动、项目和依赖 pins 均重新绑定 |

最终六个目标为四个生产模块、保留的历史回归 probe、以及新完整审计模块。原 round 2 辅助 Audit 不是最终六个验收目标之一，未计入本轮六次原 checker 覆盖。

| 目标模块 | 编译、checker 与最终回执共同绑定的源码 SHA-256 |
| --- | --- |
| `ImbalancedChen.HistoricalUpperFiveCellGeometry` | `a131b783d59540ea98cc11574f31489e2f75d519927445b49a2e4c688ab74cbe` |
| `ImbalancedChen.ActualHistoricalFifthCellIntegral` | `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de` |
| `ImbalancedChen.ActualHistoricalFifthSavingIntegral` | `bcd7075649dcc6f374ea2318f77a45eb0c260f301a00045bb7ba60f6355da74e` |
| `ImbalancedChen.HistoricalFifthCutoffInvariance` | `abe06826e099ec0beb73329c1c887fc5aeca0583efe1ff46c3b92ec91d9cdb3d` |
| `verification.parts.p1.round2.HistoricalCellProbe` | `60d27f341b74f61f0fc3e6b03c67ea7a35d999245f186b6d478bffbd533b901e` |
| `verification.parts.p1.round3.Part1HistoricalSavingAudit` | `e3539741b7db8340b15c39d7334fff2ff84d44b0aa8dcd4f811449b1b08777af` |

每个目标的回执保留实际命令、源码快照、源码前后 SHA、对象各部分 SHA、直接导入对象 SHA，以及原始 frontend/checker 日志。日志和对象绑定在编译、replay、最终收集之间逐一检查。证明修复、共享运行时的并发观察和已知成功记录的接收依据见 [RUNTIME_EVENTS.md](RUNTIME_EVENTS.md)；没有把外部队列的全局状态文件视为独立验证结论。

## 完整声明审计

审计通过 Lean 环境的 defining-module metadata 枚举所有声明，使用原 `collectAxioms` 检查传递依赖；不按源码文本或 namespace 前缀猜测声明数。它拒绝 unsafe 声明、自定义公理以及许可集合以外的传递公理。

| 定义模块 | 声明数 |
| --- | ---: |
| `ImbalancedChen.ActualHistoricalFifthCellIntegral` | 23 |
| `ImbalancedChen.ActualHistoricalFifthSavingIntegral` | 15 |
| `ImbalancedChen.HistoricalFifthCutoffInvariance` | 9 |
| `ImbalancedChen.HistoricalUpperFiveCellGeometry` | 23 |
| `verification.parts.p1.round2.HistoricalCellProbe` | 30 |

实际展开类型和每条公理列表保存在回执中。[KEY_THEOREM_TYPES.md](KEY_THEOREM_TYPES.md) 与 [JSON](KEY_THEOREM_TYPES.json) 另外提供 15 个关键定理的完整源码头；它们逐一匹配实际成功审计中的 theorem 名字和验证过的源码 SHA，避免 pretty printer 对无关证明参数的省略被误认为完整源码类型。

## 依赖对象来源

最终源导入闭包共有 9364 个模块，其中 685 个本地供应模块和目标、8679 个原缓存分类下的第三方包模块。后者有一个明确例外：`Batteries.Tactic.OpenPrivate` 本轮已实际重编译，其原命令使用 `metadata_adapter = false`，生成的全部 parts 与旧绑定相同。其余缓存对象与历史对象的复用不计为本轮重新编译或完整 replay。

| 本地对象实际来源 | 模块数 |
| --- | ---: |
| `ARCHIVED_FIRST_ROUND_ACTUAL_COMPILATION` | 170 |
| `ROUND2_ACTUAL_COMPILATION` | 118 |
| `ROUND3_ACTUAL_COMPILATION` | 397 |

| 原缓存分类下的第三方对象实际来源 | 模块数 |
| --- | ---: |
| `OFFICIAL_CACHE_RESTORED_ROUND2` | 8678 |
| `ROUND3_ACTUAL_THIRD_PARTY_SUPPLIER_COMPILATION` | 1 |

所有本地对象均重新检查源码、当前对象及直接导入 SHA；每个实际来源保留原成功命令和日志。官方缓存保留原下载/恢复证据、当前源码和对象绑定。`OpenPrivate` 的旧泛化缓存标签在本轮细化为实际第三方供应编译；旧 bootstrap 记录与旧回执原样保留，没有追改历史状态。它与重建的本地 `Architect.Command` 均由原前端实际通过并匹配旧对象全部字节。`fresh_all_import_declaration_replay = false` 是本回执的明确范围。

同一依赖清单另绑定当前存在的 34732 个 IR、签名及 hash 文件，保留实际恢复的 176 个官方 IR payload 及原归档身份。这项清单记录验证后的文件 SHA；它不宣称是逐命令加载轨迹，恢复操作也不计为前端编译或 checker。

## 可复现材料与限制

完整证据归档因 GitHub 单对象上传请求限制，按 8,000,000 字节保存为
`EVIDENCE.tar.gz.part00` 至 `EVIDENCE.tar.gz.part03`。四段按序连接后的
`EVIDENCE.tar.gz` SHA-256 由 [ARTIFACT.json](ARTIFACT.json) 固定；运行
`python3 verification/parts/p1/round3/verify_archive_parts.py` 会检查每段摘要、
完整归档摘要、1,124 个成员、生产回执和六目标范围。归档保留本轮成功与失败
尝试、真实日志和源码快照；不包含编译二进制缓存，也不会把旧停止检查点或
失败尝试改写成成功。

[check.sh](check.sh) 给出正常 pinned stock CLI 环境的六目标复现命令。本机 stock `lean` CLI 启动仍报 `failed to locate application`；本轮成功执行的是原 `Lean.Elab.runFrontend` API 路径及原 `leanchecker`，不是这个 shell 脚本的 stock 执行成功。脚本仅做过 `bash -n` 语法检查。

已观察到旧头 `744316efd1887f21c91dd4b63c218fa27704c931` 的公共根 CI 成功，但该根未导入这些新叶模块；该 CI 不计入本轮目标验收。本轮没有主动启动 CI 或 Codex 任务。

公共根集成由 Part 0 负责。当前 P0 integration 为 `d0366ce64272e81faf6166a8a90050f56b328d38`，已经接收并导入旧 stored-cap permit。[PART0_D036_HISTORY_IMPORT.patch](PART0_D036_HISTORY_IMPORT.patch) 是对该固定头的四个历史模块导入提案；[PART0_D036_IMPORT_CHECK.json](PART0_D036_IMPORT_CHECK.json) 记录真实 `git apply --check` 成功，未改公共根，不能替代集成后的根编译/checker。先前针对 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` 的提案和检查作为带时间的历史记录保留。

Part 0 须按本交付的完整 Git 树接收四个历史叶模块。`HistoricalUpperFiveCellGeometry` 与 `ActualHistoricalFifthCellIntegral` 已存在于 P1 父头 `744316efd1887f21c91dd4b63c218fa27704c931`，其中后者本轮没有源码变动；仅 cherry-pick 本轮增量不会自动带入这些尚未进入 P0 生产分支的父头文件。旧 permit 已在 P0 接收，勿重复计算其 14 项生产声明。本次 P0 接收状态的完整有界核对见 [FINAL_P0_INTAKE.md](FINAL_P0_INTAKE.md)。
