# P3.1：实际有限源、主分块与公共 Poisson 频率块

## 当前验收阶段

十个接入模块的严格编译探测已通过；五段恢复源码保持原字节。
此源码提交准备运行固定提交上的 kernel replay、完整声明库存、公理闭包及
source/object binding 验收。探测证据本身不替代该正式验收。

首个固定提交 `82db684` 的十模块严格编译和 replay 均通过，但完整库存检查
发现 `nonzeroSource.eq_1` 被 `PrimaryDyadicAssembly` 和新消费者重复序列化，
因此正式验收停止。修正仅在新消费者增加对现有 Assembly 的 import，复用其
已生成展开式；修正后的两个消费者严格编译也已通过。原数学声明、五段恢复
源码和强库存门保持不变，正式验收须以修正提交的新回执为准。

这是 P3.1 的一个实际源接入增量，**不是整个 P3.1 的完成证书**。
上一轮已经验收的四个 Poisson/Shiu 模块，包括 `windowStart`、`windowLength`、
`shellBase` 所在有限覆盖实现，原样复用，未重新实现或重复计算成果。

## 本轮连接的精确公式

令 `S = actualSource e D delta g l Z residueNegative`，
`a = signedResidue residueNegative e.residue`。最终定理
`actual_completedPiece_eq_zero_add_primary_m_lanes` 证明：

\[
\operatorname{completedPiece}
=\sum_{(z,y)\in\operatorname{image}(S_{y=0})}
  \beta_{S_{y=0}}(z,y)K(z,y)
+\sum_{k\in\operatorname{keys}(a,S)}
  \operatorname{sourceMLanes}(\operatorname{block}(a,S,k),J).
\]

其中每个 `sourceMLanes(U,J)` 都使用同一个 `U.image output` 和同一个
`beta U lambda omega`，完整保留零频、正频块、负频块与真实补集尾项：

\[
\sum\beta_U K_{m=0}
+\sum_{j\in\operatorname{blockIndices}(J)}
 \left(\sum\beta_U K_{j,+}+\sum\beta_U K_{j,-}\right)
+\sum\beta_U K_{\mathrm{tail},J}.
\]

这条恒等式只需 `0 < M`。`y=0` 项保留全部整数频率；它不进入主分块，
也没有再次加入该项的零频或尾项。原定义中的 `f ≠ 0` 不能推出 `y ≠ 0`。
所有主块、所有输出 level 和两个 m 符号使用一个显式 `J`。

`actualSource` 的非零筛选与既有 `actualNonzeroSource` 由 `rfl` 连接。
载体保留原 `g*l`、signed residue、整除商像 `baseCarrier`、实际 `H/F` 窗口。
在明确的 `e.Q2 > 0` 前提下，另证非零 beta 的真实源 witness、正 level 与
residue-coprime gate。`q=0`、空载体和 `J=0` 没有被排除或虚构正性。

三个符号仍各自独立：`residueNegative`、主 key 的 y 符号、kernel 的 m 符号。
负 m 的负 Fourier 实参和 `c.Coprime z` gate 由已验收 kernel 原样继承。

## 来源与复用

八个供应模块来自已验收的 P3.4 源提交
`97d5de82f2fd4e3d72fc86347ab40f00cc939a33`，其验收材料提交为
`da576de2c91df467d1865baee9c1b1b84ddc529b`。
其中四个文件原字节接入，四个只做 import/owner 适配：保留当前分支的定义来源，
删除七个重复声明，并以现有供应者提供六个重复小 core 的 API。
全部 109 个保留的具名声明及证明体与上游原文一致；这部分按已有成果复用记录。

两个消费者文件为：

- [Part3ActualCompletedSourceLanes.lean](../../../ImbalancedChen/Part3ActualCompletedSourceLanes.lean)：
  恢复原 `completedPiece`、signed source 和三个推前桥，共 9 个旧声明；
  新增 3 个有限组合声明。
- [Part3ActualModeCommonPoissonLanes.lean](../../../ImbalancedChen/Part3ActualModeCommonPoissonLanes.lean)：
  新增实际载体、非零系数 witness、主分块与公共 m lanes 的 9 个声明。

源码级统计为 130 个具名声明：109 个已有供应者、9 个恢复源码、12 个新组合/支持声明。
生成的方程、辅助证明、结构字段等由正式 Lean 库存另行统计；不把源级声明数当成环境总数。

八个供应者的独立适配审阅见 `SUPPLIER_ADAPTER_REVIEW.json`。
两份消费者的数学审阅及编译表达修正补审见 `MATHEMATICAL_REVIEW*.json` 和
`TASK3_REVIEW_ADDENDUM.json`。初次审阅没有发现的新 sum-binder 表达问题已明确补记，
修正只位于新组合部分；五段恢复源码未改。

## 验证范围

新增 `actual-source-lanes` group，选定八个复用供应者和两个消费者。
完整本地 project import closure 为 72 个模块；其余 62 个供应者绑定实际源码与对象，
保持旧定义和对象，不重新宣称旧证明为本轮成果，也不声称对全部 Mathlib 执行 replay。
现有 verifier 的六个 source/object helper、旧 groups、baseline gate、strict/replay、
库存、公理白名单与最终冻结检查保持不变。既有 15 个回归检查全部通过。

只允许标准传递公理 `Classical.choice`、`Quot.sound`、`propext`；
禁止 sorry/admit、额外 axioms、native_decide、unsafe 等证明逃逸。
十个目标的 strict probe 对应源码哈希和完整历史日志保存在
`STRICT_PROBE_UNION.json` 与 `strict-integration-probe-evidence.zip`。

正式命令（`SOURCE_COMMIT` 必须替换为实际源码提交）：

```sh
python3 -B verification/verify_part3_continuation.py \
  --group actual-source-lanes --expected-head SOURCE_COMMIT \
  --output-dir .lake/p31-actual-source-lanes-final
```

## 1106 稿件边界与剩余工作

稿件固定为 `chen-imbalanced-semiprimes` 的
`a988cba584d803ae2856a0de50efb582f4f3dd6a`，
`paper/release-20261106/en/analytic-appendix.tex`。
本轮对应系数在未来 m 前固定、公共有符号分块，以及公共区间/相位的有限组合步骤。

本轮的 `lambda/omega` 和尺度仍为明确参数；尚未完成：

1. 原 `OriginalData`/`FixedBlock` 与 `smoothMass/sixSmoothMass → completedPiece` 的完整桥。
2. 原始全族公共 J 的选择及其界、零项和尾项估计。
3. 实际谱 `PacketData`、`hkernel`、Theorem J 的 `full_uniform` 与 Theorem A 的 n-side 输入。

Shiu、Theorem J/A、ABL 和 Kim–Sarnak 等外部解析输入仍在原边界内，未以新公理或
额外假设将上述缺项伪装成已证明的结论。下一步应消费这些已验收恒等式，继续连接原式。
