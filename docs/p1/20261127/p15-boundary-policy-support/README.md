# Boundary 支撑层：实际正式验收

`ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport` 已在原验收提交 **`96beb9f97836d6832ccffe0dbdc5fd8e9957303d`** 完成 normal、kernel replay、完整环境 owned type/axiom 审计及独立只读复核。实际 census 为 **21 owned / 19 public / 2 private**；公理并集仅为 `Classical.choice`、`Quot.sound`、`propext`。计数来自 [OWNED_EXPORTS.json](evidence/OWNED_EXPORTS.json)，并与 [VALIDATION_RESULTS.json](evidence/VALIDATION_RESULTS.json) 及 [READONLY_RESULT.json](evidence/READONLY_RESULT.json) 一致。

## 验收范围与实际任务

| 项目 | 实际结果 |
| --- | --- |
| 正式验收及独立 readonly/export 的 provider 任务 | `job_e11a7ce15000432eb9a8ef370d97e5d4`，`succeeded`，exit 0 |
| Normal | exit 0，仅构建本 Boundary 模块；实际命令耗时 24.321 秒 |
| 依赖 | 56 个已有模块复用，连本目标共 57 个源码模块；没有重编译依赖 |
| Kernel replay | `leanchecker` exit 0，耗时 14.778 秒 |
| 完整 owned 审计 | exit 0，覆盖 private/generated 声明及完整 type/axiom 输出；无输出省略 |
| 独立只读复核 | 原 `check` 返回 `REVALIDATED`；`normal_or_kernel_commands_executed = 0` |
| 原成功 probe | `job_db8ff4c14e1f4adc8f9c8d714ca1ad5b`，exit 0，Lean 耗时 8.694 秒；preservation 通过、无目标对象输出 |

正式任务先运行 formal，再启动独立 Python 进程进行 readonly/export。原 successful normal 未重复执行，源码及五项输出在 kernel 与完整审计前后保持一致。对应证据为 [正式任务记录](evidence/formal-task.json)、[正式 PASS](evidence/PASS.json)、[完整审计结果](evidence/VALIDATION_RESULTS.json)、[成功 probe 原记录](evidence/PROBE_RESULT.json) 和 [probe 任务记录](evidence/probe-task.json)。

56 个依赖包括原 Dictionary 上下文中的 53 个旧模块，以及各自保留原验收身份的 Partition、PolicyComparison、CoefficientDifference。此次只新增 Boundary owner；旧 Dictionary 验收未重放、旧依赖 owner 未重新验收。来源及原回执引用保留在 [PASS.json](evidence/PASS.json) 的 identity 中。

## 源码与四处记号修复

验收源码路径为 `ImbalancedChen/P1HistoricalBoundaryPolicyDifferenceSupport.lean`。实际选定源码为 **20,356 bytes**，SHA256 为 `38aec5706c23b20e6893223767f13101254f90058f1d554c445a186dc56c1a46`；其精确副本见 [验收源码](https://github.com/UyNewNas/goldbach-formalization/blob/96beb9f97836d6832ccffe0dbdc5fd8e9957303d/ImbalancedChen/P1HistoricalBoundaryPolicyDifferenceSupport.lean)。成功 probe 的源码发布为 `f8c9aa12aab3306960454b98c1517f968edc735f`。

原 `29f47e87989a554c13365cfc989663dc00d34d28` 版本为 20,316 bytes / `7ac7742c3a9ada5d3a8f1e5c6e37526b5acc7d6d89d791cd61387f06fcb9b9c2`。此次仅将四处声明中的 `<+` 关系显式写成 `List.Sublist`，**全部 proof bodies 字节保持不变，源码整体字节确有变化**。原、新双 pin、精确变换及逆向恢复记录见 [REPAIR.json](repairs/sublist/REPAIR.json)；正式 PASS 的 `source_repair` 明确记录 `source_bytes_unchanged = false`、`proof_bodies_unchanged = true`。原失败 probe 保留，未替换成成功记录。

## 回执与 ZIP 索引

| 文件 | Bytes | SHA256 |
| --- | ---: | --- |
| [PASS.json](evidence/PASS.json) | 8,227 | `61d729fb2f96ab70b488d54cb638b2459399eb35b8ae70ceaf66c5f6db2a027c` |
| [READONLY_RESULT.json](evidence/READONLY_RESULT.json) | 6,943 | `59b684aac6dc83a5e0f4653c8627322f036c1361f3d79d5d909e234128d7970a` |
| [FILE_INDEX.json](evidence/FILE_INDEX.json) | 38,097 | `21d29b312c198f34b9614f43dda70ddeb02fa84817fd4601476684fd51129c74` |
| `boundary-evidence.zip` | 635,495 | `dd985983e569e3eb7d6560623c35be8feb624a6fd84dea22e483c09931261cb2` |

ZIP 共 **86 个条目**：索引列出 85 个文件，另有索引本身。内容包括完整 owner 回执目录、operation、19 项原成功 probe 文件、独立 readonly、发布入口，以及 21 个目标 artifact 位置中实际存在且按原 pin 核验的 **8 个对象文件**。原始云端路径、每个文件的 bytes/SHA256 和实际父验收 binding 见 [FILE_INDEX.json](evidence/FILE_INDEX.json) 与 [EXPORT_RESULT.json](EXPORT_RESULT.json)。

本证据只确认 Boundary 支撑层，所有实际回执仍标记 **`whole_P1_5_complete = false`**。后续原系数桥接和实际 medium 结论保留各自证明及验收义务。本说明仅整理既有回执，没有再次执行编译或验收。
