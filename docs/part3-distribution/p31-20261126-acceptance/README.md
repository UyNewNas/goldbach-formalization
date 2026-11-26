# P3.1 三模块正式验收：公共 Poisson 分块与有限 Shiu 窗口

## 已验收结果

精确源码提交 `d28d340b0240dc5cd8658893d07b61637ee94aa2`，Git tree
`24ac67c09f7fbd2aa7c1d6cc37710e0ef8231302`，在 P3 原任务
`c8f3589c6e604553bb5075f6c358270d` 中 **SUCCEEDED，exit 0**。
`poisson-lanes` 与 `shiu-windows` 分别运行并保留退出码，完整输出末行为
`P31_GROUP_EXIT_CODES lanes=0 shiu=0`。

三个目标模块均完成严格 Lean 编译（warnings-as-errors）、bundled `leanchecker`
内核回放、完整环境声明与传递公理审计，以及源码／对象绑定、最终工作树检查。
两组共 70 个记录阶段全部 exit 0。正式验收共 **107 个环境声明**，分解如下：

| 模块 | 源码顶层声明 | Lean 自动生成声明 | 环境声明总数 |
| --- | ---: | ---: | ---: |
| `Part3OriginalCommonPoissonLanesCore` | 17：6 定义、11 定理 | 15 | 32 |
| `Part3MediumPrimitiveShiuFiniteCover` | 24：6 定义、18 定理 | 12 | 36 |
| `Part3MediumPrimitiveShiuWindowGate` | 9：1 structure、8 定理 | 30 | 39 |
| 合计 | **50：12 定义、37 定理、1 structure** | **57** | **107** |

源码顶层数只计显式命名的 `def`、`theorem`、`structure`。自动生成列包括证明辅助
声明、等式引理、结构字段投影、构造器和递归器等；结构字段在源码中写出，其展开后的
投影常量在该列单列。完整逐名分类见
[DECLARATION_CLASSIFICATION.json](DECLARATION_CLASSIFICATION.json)。

两组实际传递公理并集都恰为 `Classical.choice`、`Quot.sound`、`propext`，与既有
白名单一致。该结论来自本次完整清单，不以源码关键词扫描替代内核验收。

## 完整证据

[p31-final-verification-evidence-20261126.zip](p31-final-verification-evidence-20261126.zip)
为 **119,371 字节、92 个成员**，SHA256：

```text
d0553804ecba52c52e2d6d41819822160a031f341241e5129787f1ccc0f701d2
```

归档包含两个原 verification 目录的全部报告、gate 日志、生成审计源码、环境声明
清单和定理类型，以及原 combined task 的原始状态／输出、一次只读导出的命令和状态。
报告内完整保留源文件及对象哈希和 strict 前后的绑定快照；没有收录对象二进制或其他任务。
ZIP CRC、各成员大小及 SHA256 均已核对，外部成员目录见
[ARCHIVE_MEMBERS.json](ARCHIVE_MEMBERS.json)。

原任务运行 257.239 秒，记录峰值 RSS 为 5,725,536,256 字节，CPU 时间为 247.29 秒。
完整输出为 3,698 字节，无截断，其 SHA256 为
`de1ce498ad7fdd931a1995cedb732e116cec9e03e288f7e85d6b127c78d476f5`。
这些资源数字属于两组合并任务，不重复归到每个组件。

只读导出 task `ee247df42b414a0890fb44dc7658147e` 成功，未重复验收，也未修改仓库。
云端原导出包为 98,351 字节、79 个成员，SHA256 为
`d7e7bc5e65a1d5e63bca3a36f511d5649b903467a3d51fe0a1efb163775aac7e`；
上面的最终归档在完整保留这些原成员的基础上，加入原任务回执和本地计数核对。

结构化总记录见 [ACCEPTANCE.json](ACCEPTANCE.json)。便于直接审阅的原始副本如下：

- [Poisson lanes report](../p31-poisson-lanes-20261126/verification/report.json)、
  [声明清单](../p31-poisson-lanes-20261126/verification/declarations.json)、
  [定理类型](../p31-poisson-lanes-20261126/verification/theorem-types.txt)。
- [Shiu windows report](../p31-shiu-windows-20261126/verification/report.json)、
  [声明清单](../p31-shiu-windows-20261126/verification/declarations.json)、
  [定理类型](../p31-shiu-windows-20261126/verification/theorem-types.txt)。

## 对象复用和验收范围

`poisson-lanes` 的项目源码闭包和对象绑定均为 53 个模块，其中只有新 core 是 strict／
replay target。52 个非 target 项目供应者在 strict 前后字节绑定一致，审计后全部
53 个项目对象保持不变。`shiu-windows` 的项目闭包和对象绑定均为两个模块，两者
全部是 target；该组没有未选中的项目 provider。两组都使用固定 Lean／Mathlib
及依赖 pin，不声称本轮重新内核回放了全部 Mathlib 或历史供应者。

本次普通 Lake build 实际只构建了 Core（9.3 秒）、FiniteCover（4.2 秒）和
WindowGate（7.2 秒）。早期首轮失败曾重建 Physical 供应者 12 秒，该历史在
[lane 历史 RUN](../p31-poisson-lanes-20261126/history/RUN-before-d28d-acceptance.json)
及原失败包中保留。缓存诊断里的 `Replayed` 不被当作本次 bundled `leanchecker`
内核回放证据。

Poisson core 复用了已找到的原分块／真实补集尾项证明；四类局部表达修复没有改变
数学陈述。FiniteCover 是用户明确授权后的新初等覆盖证明；WindowGate 使用实际
上传的原调用者。未恢复的旧 FiniteCover 字节没有被冒充为已找到。详情分别见
[Poisson lanes 组件](../p31-poisson-lanes-20261126/README.md) 与
[Shiu windows 组件](../p31-shiu-windows-20261126/README.md)。

源级 `SOURCE_INTAKE.json`、`CLOSURE.json` 和 `EXPRESSION_REPAIR.json` 保留正式
报告绑定的原字节，其中接入时 pending 状态是历史快照。当前验收状态由本目录和
两个组件的新 `RUN.json` 记录；旧失败 RUN 逐字节保留，不覆写历史结论。

## P3.1 尚未闭合的部分

本次验收没有给出原始实际 `PacketData`、其 `hI`／`hkernel`／`full_uniform` 供应者，
没有完成实际谱族的 Theorem A/J 组装或最终谱估计。`PrimitiveShiuTauBoundary`
仍显式承载 primitive Shiu 分析输入；本组证明的是窗口几何和调用条件，没有把
该分析输入证明掉。未恢复源码的 SignedSplit／OverlapCover 调用者也未被宣称兼容。

后续新增 kernel 原文接入或其他组件不属于这 **107 个环境声明** 的验收范围。
**完整 P3.1 仍未闭合。**
