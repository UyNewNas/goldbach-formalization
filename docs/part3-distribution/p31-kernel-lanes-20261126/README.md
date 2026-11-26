# P3.1：原物理完成核的公共 Poisson 分块

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
计数。最终运行需绑定精确源码提交，并执行原有严格 Lean、bundled `leanchecker`、
完整 defining-module 声明清单、传递公理白名单和全部项目源码／对象绑定。

```bash
python3 -B verification/verify_part3_continuation.py \
  --group poisson-kernel-lanes --expected-head <source-commit> \
  --output-dir .lake/p31-kernel-lanes-verification
```

此刻为源码接入阶段，最终验收状态以随后发布的 `RUN.json` 与完整日志为准。
不声明整个 Mathlib 或既有供应者经过本轮新的内核回放，也不声明完整 P3.1 已闭合。
