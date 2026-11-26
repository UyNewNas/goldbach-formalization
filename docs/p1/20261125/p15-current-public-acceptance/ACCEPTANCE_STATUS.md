# P1.5 当前可核验的验收进展

## 已通过的模块范围

本记录按实际编译源提交区分身份，不把当前分支 HEAD 代替历史验收提交。

| 范围 | 实际源码提交 | P1 任务 | 自有 / 公开声明 |
| --- | --- | --- | ---: |
| 原 Atlas 10 模块在当前 P1 环境的集成 | `418ad4b9a5f2d992871062258a2eefd7fdf4b9ee` | `job_5f42ad18fde84377987c244daf0b5bfc` | 242 / 229 |
| `Part3FiniteLambdaOverLogCore` | `ef450be0a89b6a3f88b3bca19d06e04e7967fa18` | `job_0c98f60f3fbe4aaa8d3e23fcf53dbcb8` | 13 / 13 |
| `Part3BrunWeights` 在当前 P1 环境的集成 | `418ad4b9a5f2d992871062258a2eefd7fdf4b9ee` | `job_41c06d666c6642889cc27d82ee281eb7` | 28 / 24 |
| `PrimeProductsMellinExactMeanInsertion` | `21789da92213323d645122cfcc7dff9c10dc82d6` | `job_8d58f7741c56448980ca0984ae5c0239` | 14 / 14 |
| `P1OriginalSingletonSupportData` | `3d292e4cd193ab422ca990e80a25165d5aca33a1` | `job_216f3dbd13b24dab8524da9ada0cac1b` | 5 / 5 |
| `P5OriginalPrimeChartHBWitnesses` | `080d4178711ae042235104f7f4768649f51da2ab` | `job_f0761da7e6124e818d654afef54ff5c5` | 7 / 7 |

前三行的固定历史回执已由 `01508da7f46ec29a815c19b97afce65dbb185b0d` 中的完整只读 collector 核验，任务 `job_ada64b3f780c4080868b4004460c1542` 成功。对应 `ATLAS10_PUBLIC_ACCEPTANCE.json`、`CORE_PUBLIC_ACCEPTANCE.json`、`BRUN_PUBLIC_ACCEPTANCE.json` 保存实际源码、normal / named-kernel / full-owned 证据哈希、计数及原任务范围。自有声明包括编译器生成的声明，因此不等同于手写 theorem 数。

Mellin 后续单模块任务已完成精确源码修复、普通编译、独立内核和完整自有声明审计，返回 `OWNER_ACCEPTED`，整体 exit 0；其有限和、原同余项与精确互素均值保持不变。修复只替换已有 Mathlib 零常量可积性引理的调用；其余 167 项源码保持一致。实际终端观察见相邻 `p15-original-atlas-proper-power/MELLIN_COMPILE_ACCEPTANCE_OBSERVATION.json`。Core 未重新编译。

2026-11-26 的只读任务 `job_e86dac8253cd430cabc4c4fac9c7b62e` 使用固定 `6067deae…` collector 完成 Mellin 原验收的完整回执核对，exit 0，确认 14 个自有声明、14 个公开声明，公理集合仅为 `Classical.choice`、`Quot.sound`、`propext`。本次未执行 Lean 或内核命令；结果见 `MELLIN_PUBLIC_ACCEPTANCE.json` 与 `MELLIN_COLLECTION_RECEIPT.json`，前三份历史摘要保持原样。

SupportData 的两处 API 修复已在原入口通过 normal、named kernel 和完整 owned 审计。只读任务 `job_0bac33ba5f2842189411dadbfc1c858d` 随后用同一原 API 复核这一个 owner，确认 5 个自有声明、5 个公开声明；未重编译。精确摘要为 `SUPPORT_CURRENT_PUBLIC_ACCEPTANCE.json`，原 source commit 保持 `3d292e4c…`。该 first3 任务随后在 HBWitnesses 的 `R` 命名冲突处失败，Cutoff 尚未开始；不将它改写为三目标整组成功。

HBWitnesses 的显式 dyadic 名称修复随后在 F 提交 `080d4178…` 下通过 normal 和完整 owned kernel 审计。只读任务 `job_d6bf8f957aa745919b43d347d9142bcf` 用原 F API 复核该 owner 的 67 项实际源码闭包、六份验收回执和全部 21 项目标产物，确认 7 个自有声明、7 个公开声明，且原文件与产物前后保持一致。原样有界摘要见 [HB_F_PUBLIC_ACCEPTANCE.json](HB_F_PUBLIC_ACCEPTANCE.json)，收集范围及终态见 [HB_F_COLLECTION_RECEIPT.json](HB_F_COLLECTION_RECEIPT.json)。本次收集没有执行 Lean 或 kernel，没有导出自有声明类型或私有归档，也没有收集或推测公理并集。

F 的后续 Cutoff normal 编译在四处 Lean 表达/API 调用停止，因此原配对任务仍是 exit 1、仅 HB 被接受。后十五项条件任务据此返回 HOLD，源码写入和 Lean 命令均为零；见 [F 配对观察](../../20261126/p15-cutoff-first-compile-repair/F_PAIR_COMPILE_OBSERVATION.json) 与 [条件任务观察](../../20261126/p15-cutoff-first-compile-repair/LATER15_CONDITIONAL_HOLD.json)。下一次只修复并编译 Cutoff，HB 与 Support 分别保留 F、B 的原验收身份。

## 部分任务的失败范围仍保留

Core 所属原两目标任务整体 exit 1，因为当时 Mellin 仍失败；这不被改写为整组成功。BrunWeights 所属原二十目标任务亦整体 exit 1，第二目标 `Part3CompletedReciprocalWeil` 停在外部依赖的 stock readiness 检查，其 normal 编译尚未开始，其余十九目标未获此轮接受。JSON 保留这些失败和未接受集合。

Atlas 与 Brun 的成功属于已有数学源码在当前 P1 编译上下文中的集成，不计为重新开发这些外部或远程已有证明。所有相应旧接受身份均保留。

## P1.5 整体仍未关闭

原实际第四、第五均值链的 23 个 owner，以及第一阶段四个输入 owner 的既有验收保持有效，未重复编译。当前 proper-power、trim、rough-prime 与 remaining-Type-I geometry 的后续目标依其真实依赖继续推进。

尚须把原有符号 von Mangoldt 分布误差、medium Atlas、remaining Type-I Atlas 和同一历史系数的最终余项连接起来。全局状态仍是 `whole_P1_5_complete=false`。源码静态核验、对象存在或一次普通编译均不单独升级为整体完成。
