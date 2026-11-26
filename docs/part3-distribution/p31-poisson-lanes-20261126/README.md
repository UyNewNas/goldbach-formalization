# P3.1 原始公共 Poisson 分块：已有源码接入

## 当前状态

原源码提交 `c5ccf81ce1a55e2dafeca0116cd70177bf169504` 的验证任务
`bfc679557318469381929f9806d79fc7` 已 **FAILED，exit 1**，失败位置为
`build-new-targets` 中的新 core。任务在 UTC 2026-11-26 02:18:33 开始、
02:19:07 结束，运行 34.058 秒；完整 38,756 字节输出已取回，无截断。

三类局部表达修复现已应用并记录，**修复源码仍待严格验证，新增验收声明为零**。
此前 52 个 provider 缓存对象复制成功；随后普通 `lake build` 实际重新构建了
`Part3PhysicalSmoothReciprocalPoisson`（12 秒）。缓存复制不等于 Lake 从不重建。
此次失败未进入 `after_build` 对象快照、新 core 的 strict 编译、内核回放或公理审计。
其他旧模块的 `Replayed` 行是 Lake 缓存诊断日志，不是本轮新的内核回放。

[RUN.json](RUN.json)、[完整失败证据](failed-run-evidence.zip) 和
[EXPRESSION_REPAIR.json](EXPRESSION_REPAIR.json) 记录失败与修复状态；
[原排队与准备回执](queued-run-evidence.zip) 作为历史记录保留。
后续由 root 发布修复源码并针对其精确提交运行 `poisson-lanes` 验证；
不重复提交已经失败的旧源码，也不把 source-only 通过视为 Lean 验收。

模块 `ImbalancedChen/Part3OriginalCommonPoissonLanesCore.lean` 保留原命名空间和
17 个具名声明的数学陈述（6 个定义、11 条定理）。初始接入片段与原文逐字节一致；
当前已登记三类表达修复，因此不再声称当前证明正文与原文逐字节相同。

## 首次失败与表达修复

- 八处 `Finset.image` lambda 显式标注 `p : ℕ`，保留自然数到整数的正负嵌入。
- `commonMBlock_owner` 先得到明确类型的 filter 合取再投影，避免反向推导错误的元素与谓词。
- `poisson_series_eq_lanes` 在 `ring` 前展开既有 `poissonTail`，使原补集级数与其命名定义一致。

没有添加数学假设、删除尾项或修改 provider 源码。原始片段哈希保持不变，
当前片段哈希、源码哈希和逐项 `mechanical_repairs` 保存在来源记录中。

## 接入的实际恒等式

对一个事先选定的全局自然数截断值 `J`，代码保留

\[
 I_j=[2^j,\min(2^{j+1},J+1))\cap\mathbb N,
 \qquad j\in\operatorname{range}(\operatorname{Nat.log}(2,J)+1),
\]

其中 `J = 0` 时自然数对数取零，唯一列出的 `j = 0` 块为空。
代码同时保留原物理 Poisson 频率函数 `frequency` 的精确分解

\[
 \sum_{m\in\mathbb Z}F(m)
 =F(0)+\sum_j\left(\sum_{p\in I_j}F(p)+\sum_{p\in I_j}F(-p)\right)
  +\sum_{|m|>J}F(m).
\]

最后一项是原级数在补集上的真实子级数。零频只出现一次，负频仍使用 `-p`；
本次没有丢弃尾项、证明尾项很小，或把正负项视为相同的复数。
共同变量的相位仍是 `k1 / (64 * 2^j)`，没有 level、谱高度或旧 s-frequency 参数。

## 复用来源

原始源码位于提交 `b945f39a1e355ff4fcca9865ab59ffc97f2172c0` 的
`docs/source-only/20261102-resume-30o/medium_spectral_dictionary/Part3OriginalCommonPoissonLanes.lean`，
Git blob 为 `00a797ac77cb444479ce097f4b44c56930489e32`，完整 SHA256 为
`1c15c03a6fa6a1c188e8f5f2498aaee5f14da01b05e48676b263f9f3df1919e4`。
本次接入原第 32–177 行和 185–216 行；两个原片段的哈希及新模块哈希保存在
[SOURCE_INTAKE.json](SOURCE_INTAKE.json)。

原导入链中 `OriginalData` 的定义闭包尚未完整恢复。本次直接使用已经验收的
`Part3PhysicalSmoothReciprocalPoisson` 供应者：它与原供应者的全部数学声明和
证明正文相同，仅文档头不同。没有用新结构替代 `OriginalData`。

已检查的既有验收目录中未找到这些精确声明的验收；因此本次复用已有证明源码，
只为这个此前 source-only 的组件做首次接入验证。现有 80 个基线模块和
P3.1 的六条条件接口定理继续复用，不重写或重新单独回放。

## 范围边界

本组件不包含 `globalCutoff`、原始六族的 `OriginalData` 组装、真实 `PacketData`
构造、`hkernel`、Theorem A/J 在实际谱族上的实例化或最终谱估计。
它不单独解决完整原 carrier 的 `hI`，也不改变 P3.1 整体尚未闭合的状态。
后续恢复完整原模块时，应让它导入此 core 并移除重复声明，不能同时导入两个
未拆分的同名声明集合。

## 验证入口

```bash
python -B verification/verify_part3_continuation.py \
  --group poisson-lanes --expected-head <source-commit> \
  --output-dir .lake/p31-poisson-lanes-verification
```

[CLOSURE.json](CLOSURE.json) 绑定 53 个可达项目模块及 64 个外部导入名。
严格编译与内核回放仅选择新 core；既有完整声明清单、公理白名单、源码与对象
闭包检查继续保留。常规导入环境信任边界不被表述为所有 Mathlib/旧供应者的新回放。

## source68 附件核对

用户本轮提供的附件为 11,898 字节，SHA256 为
`6d47a7fb9a91a67ba330cd6ca519964b03cb81e2da5d358d14e50b010ebe3892`。
其内容与既有 `Part3MediumPrimitiveShiuWindowGate.lean` 完全相同，首行仍导入
`Part3MediumPrimitiveShiuFiniteCover`。因此该附件没有恢复缺失的 FiniteCover
供应者；原 P2/P1 恢复回执继续保留，本组件也不为 source68 补发验收。

P2 原归档/Git 对象任务随后完成，并仅对其明确跳过的五个大 tar 做了补查：
151 次归档目录检查加 59 份相同压缩 tar 的哈希复用，覆盖全部 210 个登记路径，
共 91,395 条归档成员目录记录及五个 Git 数据库的 70,226 个对象条目；未找到
候选。P1 的原大 ZIP 任务结果仍因服务 429 不可读。有限检索不被解释为全局不存在。

完整证据见 [SOURCE68_RECOVERY.json](SOURCE68_RECOVERY.json) 和
[原恢复日志归档](source68-recovery.zip)。P2 已完成的两项任务不得重复运行。
当前所需附件是实际定义 `windowStart`、`windowLength`、`shellBase` 等符号的
`Part3MediumPrimitiveShiuFiniteCover.lean`；已登记版本分别为 13,577 字节和
14,529 字节，均不同于本次 11,898 字节的 WindowGate。

[REUSE_MAP.json](REUSE_MAP.json) 保存本次已找到的原始行、两个 Z 区间的 Fourier
总装、同谱基的 J/A 接口及其来源与未闭合依赖，供后续直接续接而不重做检索。
初始原文接入的独立静态复核见 [REVIEW.json](REVIEW.json)，其有效时间和原证据保持不变；
当前修复范围与失败依据另见 [EXPRESSION_REPAIR.json](EXPRESSION_REPAIR.json)，均不构成修复后的 Lean 验收。
