# P3.1 实际有限源接入：正式验收通过

本轮把原 `completedPiece`、实际 medium carrier、计算得到的 primary 分块与
公共 Poisson 频率分解接通。**这一增量已验收；P3.1 整体仍未闭合。**

## 固定源码和验收

- 验收源码提交：`6840a3c4d4f3e67f076e55d70fce9851ab7615c9`。
- 源码 tree：`67f9942143f8c3400abe3748fb3d8432f6cff0ed`。
- P3 成功任务：`94f0edc5f5944c899af23f33ce023221`，exit code `0`。
- 52 个正式检查阶段全部成功。
- 10 个模块分别严格编译并执行 bundled `leanchecker` replay。
- 完整库存为 164 条环境声明，包含私有和自动生成声明。
- 72 个 project 模块的源码与实际对象解析完成绑定；非目标 provider 对象在
  strict 阶段保持冻结，全部 project 对象在 audit 后保持冻结。
- 传递公理仅为 `Classical.choice`、`Quot.sound`、`propext`。

编译器为 Lean 4.33.0-rc1，commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`；Mathlib 固定为
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。
原 verifier 的库存 equality、公理白名单、baseline 保留、source/object
冻结及最终工作树检查均保持原样。

## 成果与已有工作分别记录

| 范围 | 模块数 | 具名源码声明 | 环境声明 |
|---|---:|---:|---:|
| 复用的 P3.4 供应者 | 8 | 109 | 131 |
| `Part3ActualCompletedSourceLanes` | 1 | 12 | 24 |
| `Part3ActualModeCommonPoissonLanes` | 1 | 9 | 9 |
| 本轮接入验收合计 | 10 | 130 | 164 |

130 个具名源码声明由 109 个已有供应者、9 个恢复的原声明、12 个新增组合或
支持声明构成。新增部分是 9 个 theorem 和 3 个 def。其余 34 条是 Lean 自动
生成的环境声明；没有将其算作新的手写定理。

复用的供应者来自已验收源码 `97d5de82f2fd4e3d72fc86347ab40f00cc939a33`，
验收材料为 `da576de2c91df467d1865baee9c1b1b84ddc529b`。
四个源文件逐字接入，四个只做 import/owner 适配。已有 109 条声明的正文保持原文。
上一轮 Poisson/Shiu 的四个已验收模块均未修改；不重复计算旧验收成果。

## 实际证明内容

核心定理 `actual_completedPiece_eq_zero_add_primary_m_lanes` 使用原实际
`baseCarrier`、signed residue、`sharedSmoothFrequencyBound` 和 `scaleF`，证明：

\[
\operatorname{completedPiece}
=\text{保留全部 m 的 y=0 项}
+\sum_{\text{实际 primary keys}}
\bigl(\text{零频}+\text{共同正负频率块}+\text{真实补集尾项}\bigr).
\]

恒等式仅需 `M > 0`，所有块使用同一显式 `J` 和同一原始 `lambda/omega`。
复数权重、output fiber 的重数、互素 gate、负频率的负 Fourier 实参均保留。
residue sign、y sign 与 m sign 各自独立。`J=0` 和空载体自然包括在定理中。

另在明确的 `e.Q2 > 0` 前提下证明：实际商像中的元素为正，非零 beta 有来自
原载体的 witness，输出 level 正并与原 residue 互素。没有为这些结论增加任意
beta 支持假设，也没有从未带正性字段的 `MediumAtom` 暗推尺度正性。

## 曾失败的库存检查与修复

初次固定源码 `82db684` 的十模块 strict 和 replay 通过，但强库存 equality
发现同一 `nonzeroSource.eq_1` 被 Assembly 与新消费者各自序列化。
该次正式验收按失败保留，没有作为成功记录使用。

修复只在新消费者加入现有 `Part3PrimaryDyadicAssembly` 的 import，使其复用
已有生成方程。数学声明、证明正文、五段恢复片段和验证规则均未改。
当前固定提交已通过相同的完整 equality 门，展开式实际 owner 为 Assembly。

编译环境曾出现 Git 拉取认证和 native-cache 路径问题。相同源码提交通过
SHA 校验的 Git bundle 同步；缓存按匹配的源码从已有编译树恢复。恢复过程不
改变数学源码或验收规则。相关失败记录及缓存恢复记录保存在完整证据包中。

## 可复核证据

- [正式报告](verification/report.json)
- [完整声明与公理](verification/declarations.json)
- [完整 theorem 类型](verification/theorem-types.txt)
- [源码到完整环境声明的独立映射](DECLARATION_CLASSIFICATION.json)
- [库存修复的独立终验](FINAL_INVENTORY_FIX_ACCEPTANCE_REVIEW.json)
- [机器可读验收范围](ACCEPTED_SCOPE.json)
- [运行及本地接收复核](RUN.json)
- [证据成员清单](ARCHIVE_MEMBERS.json)
- [完整证据归档](verification-evidence.zip)

归档为 264,303 bytes、157 个成员；SHA256：

```text
44e343e2cc37a2f0ea0d8466e3335f7c4abd383e94393e8c13c63c7a00658644
```

接收端核对了归档 SHA/CRC、全部 stage log 哈希、10 项 strict/replay、完整库存
重新解析、72 模块源码闭包、provider 冻结、生成 audit 的哈希和缓存 build 日志。
原失败运行和 owner-fix probe 均在归档中，不能与本次成功回执混同。

## P3.1 尚未完成的连接

1. `OriginalData`/`FixedBlock` 与 `smoothMass/sixSmoothMass → completedPiece`。
2. 原始全族公共截断 J 的选择及其界，零项和尾项估计。
3. 实际谱 `PacketData`/`hkernel`、Theorem J 的 `full_uniform` 与 Theorem A 的 n-side 输入。

本轮 `lambda/omega` 和尺度仍是明确参数，没有把它们自动认定为缺失的
`OriginalData` 全族。Shiu、Theorem J/A、ABL、Kim–Sarnak 等外部解析输入仍保留
原有边界。看板整体 P3.1 不应仅凭本轮局部验收改为绿色。
