# 原 U5 三个基础模块的组合验收

本目录保存固定数学源码提交 `3aafcd2464df9486f98788a657086db9d686b187` 的三个模块的完整验收证据。独立审查结论为通过，范围严格限定为这三个模块的 28 条完整声明。

| 模块 | 完整声明 | 本次可使用的结果 |
| --- | ---: | --- |
| `P2ActualPairPlanRunSupport` | 7 | 实际 pair-root run 的冻结 cap 与已接纳完整 word 的支撑界 |
| `P5OriginalU5PhysicalRho` | 10 | 原 U5 标签到完整整数模数的 pushforward、原 fibre 唯一性与原系数值的一致性 |
| `P3OriginalU5PhysicalModulusCap` | 11 | 六个公开模数界定理与五个生成定理；完整物理模数严格小于 `N^(599/1000)` |

最后一项保留原 `selectedPolicy ... false N t`、同一 literal `rho` 和完整小 beta 因子。定理中的 `0 ≤ buffer ≤ 1/1000`、相应的 `attachmentNu * epsilon ≤ buffer`、`N ≥ 2`、原 `pairSupport` 和非零条件均未删去；最终整数系数定理还要求 `0 < epsilon < 1/8`。

## 如何核对

- `INDEPENDENT_REVIEW.md` 说明独立审查方法、来源边界和结论。
- `INDEPENDENT_REVIEW.json` 保存阶段、工具、源对象、完整声明类型哈希和公理绑定。
- `OWNED_DECLARATIONS.json` 是归档中 `continuation/declarations.json` 的原始字节副本，可直接查看全部完整 Lean 类型。
- `RECEIPT.json` 与 `TASK_TERMINAL.json` 保存审计续跑的实际记录。
- `evidence.tar.xz` 包含父任务的成功阶段、源码与对象，以及本次审计的脚本、完整输出、绑定快照和声明清单。
- `TRANSPORT_STATUS.json` 及输出前后缀记录无损传输；按前缀、归档、后缀的顺序拼接即可重构原任务 stdout。

归档为 4,559,760 字节，SHA-256 为 `95c14de12928cf047491db283d098ce99de6a789e25b4074c00f154dabea986c`。全部 314 个成员均已独立核验。28 条声明的传递公理仅使用 `propext`、`Classical.choice`、`Quot.sound`。

## 阶段来源与不重复工作

三个模块的严格编译和官方 bundled leanchecker replay 来自父任务 `job_345d68b9a44a4e33b6913f4e612cac72` 的六个成功阶段。父任务后来在声明审计阶段超时；其 `timed_out` 终态和 `COMPILED` 报告保持原样。

续跑任务 `job_3f41695f60954734a1340a4fa4e96cba` 只完成遗漏的完整声明审计，审计用时 678.86 秒，任务 exit code 为 0。它在前后检查 37,744 个源文件、对象、sidecar、工具和证据快照，并检查实际 Lean namespace 解析与依赖固定提交。因此这里复用已完成的编译与 replay，没有重做它们。

## 仍未闭合的目标

本验收不包含下一批四个 EXTRA 模块、RootV/rough-endpoint 三模块或 rounded 候选；也不提供 common physical Q、whole-atom/tensor、family admission、密度收敛或最终 PP 估计。整个 **P3.6 仍未完成**。
