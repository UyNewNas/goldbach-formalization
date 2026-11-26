# P3.1：原物理完成核的公共 Poisson 分块

## 当前正式状态

精确源码提交 `8e895502586ad41d5222ed5fd54386855b909b32`，tree
`dab003597c3064fa021b6924ccb642f4775a122a`，已经在 P3 task
`8172cbb2c4a340358d38b706c9b6455a` 中 **SUCCEEDED，exit 0**。
`poisson-kernel-lanes` 的 34 个阶段全部通过，包括严格 Lean 编译
（warnings-as-errors）、bundled `leanchecker` 内核回放、完整环境声明／传递公理
清单、源码／对象绑定及最终工作树检查。

本组件正式验收 **18 个环境声明：13 个源码顶层声明，加 5 个自动生成声明**。
顶层为 7 条定理、5 个定义和 1 个 abbreviation；5 个自动生成项全部是证明或等式
辅助声明。实际传递公理并集恰为 `Classical.choice`、`Quot.sound`、`propext`。
全部 54 个可达项目模块均有源码／对象绑定；53 个非 target provider 在 strict
前后保持一致，审计后全部项目对象保持不变。

当前记录见 [RUN.json](RUN.json)、[report](verification/report.json)、
[完整声明清单](verification/declarations.json)、[定理类型](verification/theorem-types.txt)
和 [逐名分类](DECLARATION_CLASSIFICATION.json)。此前三个模块的 107 个声明没有
重复验收或计数，本轮四模块的去重并集为 125，详见
[本轮完成记录](../p31-20261126-acceptance/ROUND_COMPLETE.md)。

## 接入范围

本组件继续复用已验收的 `Part3OriginalCommonPoissonLanesCore` 与
`Part3PhysicalSmoothReciprocalPoisson`，从三份实际可取的历史源码中选择四段原证明，
保留其原命名空间、数学陈述、定义和假设。新单模块为
`ImbalancedChen/Part3OriginalCommonPoissonKernelLanesCore.lean`。

选中的 13 个具名声明包括 7 条定理、5 个定义和 1 个 abbreviation：三个原负号
引理、原 `Output` 与 `completedKernel`，以及原 CommonPoissonLanes 的负频、
有限模数权重和完成核分块。它们没有被改写成另一套 `OriginalData` 接口。

## 实际证明内容

原 `completedKernel` 是有限物理模数和：只保留 `0<c≤floor(10C)` 且
`c.Coprime z` 的模数，以 `scaledDyadicCutoff N c` 加权原 Poisson 全整数级数。
它的定义来自原 `ActualCompletedSquarePushforward`，没有假设所需的分块恒等式。

对同一个事先给定的自然数 `J`，代码证明

\[
 K=K_0+\sum_{j\in\operatorname{range}(\operatorname{Nat.log}_2J+1)}
       (K_j^++K_j^-)+K_{\mathrm{tail}}.
\]

这些项使用已经验收的共同区间 `commonMBlock J j`。补集尾项是原级数的实际
子级数；`c.Coprime z` 过滤保留在每一项中。证明没有舍弃尾项或声称它很小。

三个负号引理通过全部 `ZMod c` 上的双射 `u↦-u` 证明 Kloosterman 双负号恒等式，
覆盖模数 `c=1`。负频的 Fourier 参数保持为 `-(M/c)*p`；没有将系数共轭或把
正负项视为相同复数。

这接入了 1106 稿原物理完成核的共同分频步骤。实际原族的 `OriginalData` 组装、
全局截断选择、原 carrier 与 packet 的识别，以及谱核的两侧 Fourier 因子分解
`hkernel` 仍需后续衔接，不能由这一物理核恒等式直接宣告完成。

## 来源与表达修复

原始 Git blobs：

- `Part3ActualReciprocalSquarePoisson.lean`：`58e9a86e0bd60aee30ebc7a15c781f2dd96a49c9`。
- `Part3ActualCompletedSquarePushforward.lean`：`04972fd9774d63bfa5aca69b23d2e389446b448b`。
- `Part3OriginalCommonPoissonLanes.lean`：`00a797ac77cb444479ce097f4b44c56930489e32`。

前两份来源由既有 Y04 选择记录定位，并实际取回、校验 Git blob 和 SHA256。
选段不需要导入原文件中与这些声明无关的未恢复依赖。当前项目中没有这 13 个
声明的重复定义；原选择记录是 source-only 记录，不能代替本次验收。

`weightedC_add` 原证明的条件简化在当前编译器中失败；局部修复仅把正、负两个
分支分别用 `if_pos` 与 `if_neg` 展开。定理陈述、加权定义和所有原假设保持不变。
四段原始／当前哈希及修复记录保存在 `SOURCE_INTAKE.json`。

## 验证

该组件只为一个新模块取得验收；此前三个模块的 d28d340 验收继续复用，不能重复
计数。本次正式运行绑定上述精确源码提交，并已通过原有严格 Lean、bundled
`leanchecker`、完整 defining-module 声明清单、传递公理白名单和全部项目源码／
对象绑定检查。

```bash
python3 -B verification/verify_part3_continuation.py \
  --group poisson-kernel-lanes --expected-head 8e895502586ad41d5222ed5fd54386855b909b32 \
  --output-dir .lake/p31-kernel-lanes-verification
```

## 完整验收证据

[verification-evidence.zip](verification-evidence.zip) 为 **236,982 字节、53 个成员**，
SHA256 为 `cde3814da4442181eb64c806f9aa7187e93308dababc9f95210148e118a531cb`。
它保留原任务内嵌导出的全部 42 个成员，再加原任务完整终态 metadata、两段原始输出
响应、完整 stdout、实际命令和本地核对记录。没有另排导出或重复编译；没有包含对象
二进制或其他任务。各成员大小与哈希见 [ARCHIVE_MEMBERS.json](ARCHIVE_MEMBERS.json)。

原内嵌导出包为 53,331 字节，SHA256 为
`5456f89a7b76911ed41f7ee83c392ae20f19af0c87db48873922e9bc523c79d0`。
原任务运行 148.862 秒，峰值 RSS 记录为 5,709,750,272 字节；完整输出 73,434 字节，
无截断。普通 Lake build 只实际构建了新 KernelLanesCore（7.2 秒）；旧 Common core
和 Physical provider 没有重建。源码／对象冻结与真正的内核回放证据分别保存。

`SOURCE_INTAKE.json`、`CLOSURE.json`、`EXPRESSION_REPAIR.json` 和早期 probe 回执
保持原字节。正式报告直接记录前两者的文件哈希；表达修复与 probe 记录按来源提交
保留为历史证据，其接入时 pending 标签是历史快照。当前结果以 `RUN.json` 与正式
报告为准。不声明整个 Mathlib 或历史供应者经过本轮新的内核回放。
谱 `hkernel`、原族 `OriginalData` 及全族 J/A 组装仍待衔接；**完整 P3.1 仍未闭合**。
