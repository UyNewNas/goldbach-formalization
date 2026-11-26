# P3.1 原始公共 Poisson 分块：已有源码接入

## 当前状态

源码已提交到 `c5ccf81ce1a55e2dafeca0116cd70177bf169504`。P3 独立工作树
准备成功，52 个已存在的依赖对象全部复用，缺失对象为零。
截至北京时间 **2026-11-26 10:12:39**，严格验证任务
`bfc679557318469381929f9806d79fc7` 仍在排队，尚未开始、没有输出。
因此本轮仍为 **已实现待编译**，新增验收声明数为零。

[RUN.json](RUN.json) 及 [排队与准备回执](queued-run-evidence.zip) 保存实际状态。
后续应直接读取这一原任务；不得重复提交，也不得把准备任务成功等同于 Lean
严格编译、内核回放或公理审计通过。

新模块为 `ImbalancedChen/Part3OriginalCommonPoissonLanesCore.lean`。
它从原 `Part3OriginalCommonPoissonLanes.lean` 精确保留 17 个具名声明：
6 个定义、11 条定理。原命名空间、数学陈述和证明正文全部保留。

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
本次独立源码复核见 [REVIEW.json](REVIEW.json)。
