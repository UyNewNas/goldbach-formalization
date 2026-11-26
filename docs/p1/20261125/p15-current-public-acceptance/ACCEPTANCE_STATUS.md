# P1.5 当前可核验的验收进展

## 已通过的模块范围

本记录按实际编译源提交区分身份，不把当前分支 HEAD 代替历史验收提交。

| 范围 | 实际源码提交 | P1 任务 | 自有 / 公开声明 |
| --- | --- | --- | ---: |
| 原 Atlas 10 模块在当前 P1 环境的集成 | `418ad4b9a5f2d992871062258a2eefd7fdf4b9ee` | `job_5f42ad18fde84377987c244daf0b5bfc` | 242 / 229 |
| `Part3FiniteLambdaOverLogCore` | `ef450be0a89b6a3f88b3bca19d06e04e7967fa18` | `job_0c98f60f3fbe4aaa8d3e23fcf53dbcb8` | 13 / 13 |
| `Part3BrunWeights` 在当前 P1 环境的集成 | `418ad4b9a5f2d992871062258a2eefd7fdf4b9ee` | `job_41c06d666c6642889cc27d82ee281eb7` | 28 / 24 |
| `PrimeProductsMellinExactMeanInsertion` | `21789da92213323d645122cfcc7dff9c10dc82d6` | `job_8d58f7741c56448980ca0984ae5c0239` | 14 / 14 |

前三行的固定历史回执已由 `01508da7f46ec29a815c19b97afce65dbb185b0d` 中的完整只读 collector 核验，任务 `job_ada64b3f780c4080868b4004460c1542` 成功。对应 `ATLAS10_PUBLIC_ACCEPTANCE.json`、`CORE_PUBLIC_ACCEPTANCE.json`、`BRUN_PUBLIC_ACCEPTANCE.json` 保存实际源码、normal / named-kernel / full-owned 证据哈希、计数及原任务范围。自有声明包括编译器生成的声明，因此不等同于手写 theorem 数。

Mellin 后续单模块任务已完成精确源码修复、普通编译、独立内核和完整自有声明审计，返回 `OWNER_ACCEPTED`，整体 exit 0；其有限和、原同余项与精确互素均值保持不变。修复只替换已有 Mathlib 零常量可积性引理的调用；其余 167 项源码保持一致。实际终端观察见相邻 `p15-original-atlas-proper-power/MELLIN_COMPILE_ACCEPTANCE_OBSERVATION.json`。Core 未重新编译。

2026-11-26 的只读任务 `job_e86dac8253cd430cabc4c4fac9c7b62e` 使用固定 `6067deae…` collector 完成 Mellin 原验收的完整回执核对，exit 0，确认 14 个自有声明、14 个公开声明，公理集合仅为 `Classical.choice`、`Quot.sound`、`propext`。本次未执行 Lean 或内核命令；结果见 `MELLIN_PUBLIC_ACCEPTANCE.json` 与 `MELLIN_COLLECTION_RECEIPT.json`，前三份历史摘要保持原样。

## 部分任务的失败范围仍保留

Core 所属原两目标任务整体 exit 1，因为当时 Mellin 仍失败；这不被改写为整组成功。BrunWeights 所属原二十目标任务亦整体 exit 1，第二目标 `Part3CompletedReciprocalWeil` 停在外部依赖的 stock readiness 检查，其 normal 编译尚未开始，其余十九目标未获此轮接受。JSON 保留这些失败和未接受集合。

Atlas 与 Brun 的成功属于已有数学源码在当前 P1 编译上下文中的集成，不计为重新开发这些外部或远程已有证明。所有相应旧接受身份均保留。

## P1.5 整体仍未关闭

原实际第四、第五均值链的 23 个 owner，以及第一阶段四个输入 owner 的既有验收保持有效，未重复编译。当前 proper-power、trim、rough-prime 与 remaining-Type-I geometry 的后续目标依其真实依赖继续推进。

尚须把原有符号 von Mangoldt 分布误差、medium Atlas、remaining Type-I Atlas 和同一历史系数的最终余项连接起来。全局状态仍是 `whole_P1_5_complete=false`。源码静态核验、对象存在或一次普通编译均不单独升级为整体完成。
