# P3.1：实际单项与六项平滑质量接入公共 Poisson 分块

## 本轮范围与验收阶段

本轮继续已验收的 `6840a3c4` 源码及 `2a6b7b74` 验收提交，补上
`smoothMass/sixSmoothMass → completedPiece → 实际 primary/common-J lanes`。
原平滑完成证明从已有 P3.2 供应者恢复；新增部分仅组合已有端点。
源码与来源检查及既有 15 个 source/object 回归检查通过；三个接入模块的
严格编译与完整声明库存预检通过（环境声明 38 个，按模块为 21、14、3）。
该预检尚不构成固定源码提交的正式验收；正式 strict/replay/完整库存回执另行归档。

这一增量不构造 `OriginalData` 或 `FixedBlock`，不选择或估计原全族截断 J，
不证明零项、尾项估计，不填补实际谱 J/A 输入，也不宣称整个 P3.1 完成。

## 精确数学内容

单项定理 `actual_smoothMass_eq_common_m_lanes` 在 `M > 0` 与 `M ≤ 2*B`
下，将原实际有限 reciprocal row 的完整平滑平方写成：

\[
\text{完整的零 }y\text{ 项}
+\sum_{\text{实际 primary 分块}}
  \bigl(\text{零 }m\text{ 项}+\text{公共正负 }m\text{ 块}+\text{补集尾项}\bigr).
\]

`M ≤ 2*B` 保证原 `Ioc 0 floor(5*B)` 覆盖整个平滑 b 支撑，不能删除。
非零 y 部分才进入频率分解；`f ≠ 0` 不推出 `y ≠ 0`。

六项定理 `actual_sixSmoothMass_eq_common_m_lanes` 只需 `B > 0`，精确处理
原来的六对尺度：

| b 平滑尺度 | c 平滑尺度 |
|---|---|
| B | C、2C、4C |
| 2B | C、2C、4C |

六项保留同一个 `packetBox B C F`、同一个实际源、原始 `lambda/omega`
和同一个显式 J。改变 c 的平滑尺度时，外部 c 载体仍然是原 C 对应的
`Ioc 0 floor(10*C)`。没有额外乘上因子六，没有加入 C/F/载体非空的正性前提。
每个原平滑项内的零 y 项只加入一次，并保留全部整数 m。

实际参数逐项使用 `g*l`、`signedResidue`、`baseCarrier e (D/delta)`、
`sharedSmoothFrequencyBound Z D` 和 `scaleF e D g`；余数符号、y 符号与
m 符号分别保留。这里的系数仍是明确参数，没有认定缺失的原全族能量接口。

## 复用来源与新增声明

P3.2 的源码 `34201be0ca95d465336119fce24b7681c17ab0c6` 及验收提交
`30e2a96b601458d59116517ca478c496a68a39c9` 已包含三份原供应者的源码与冻结
编译对象。历史头注 `SOURCEONLY/UNCOMPILED` 不能替代后来的编译回执。
这些供应者在该次验收中属于正常导入环境信任，不声称它们都被独立 strict/replay。
原报告及三份原源字节保存在 `upstream/`，来源核对见
[EXISTING_WORK_AND_PROVENANCE.json](EXISTING_WORK_AND_PROVENANCE.json)。

| 本轮模块 | 源码声明 | 性质 |
|---|---:|---|
| `Part3ActualPositiveLatticeSmoothCore` | 13 | 恢复原紧支撑、Packet、有限盒与平滑质量定义 |
| `Part3ActualSmoothMassCompletion` | 7 | 恢复原有限行及三个平滑完成恒等式 |
| `Part3ActualSmoothMassCommonLanes` | 3 | 新增 1 个表达式定义和 2 个有限组合定理 |

20 个恢复声明包含 15 个 theorem（其中 2 个 private）、4 个 def 和 1 个 abbrev。
19 个恢复片段逐字保留；唯一适配只把原专门化 b-Poisson 调用接到当前已有的
泛化 b-Poisson API，提供原有限载体和原支撑证明。端点陈述及其余正文保持原样。
完整片段和 owner 记录见 [SOURCE_FRAGMENTS.json](SOURCE_FRAGMENTS.json)。
预检库存中的 38 个环境声明包含 23 个源码声明与 15 个自动生成声明。
正式环境库存及 private 名称映射另行绑定；自动生成声明不计为新增数学证明。

没有重复声明当前已有的 `finiteInnerCarrier`、`scaleF`、`completedPiece`、
平方展开或 Poisson 定理。上一轮两个实际源消费者及 Poisson/Shiu 成果原样复用。
独立数学与复用审阅见 [MATHEMATICAL_REVIEW.json](MATHEMATICAL_REVIEW.json)。

## 验证规则

新增 verifier group `smooth-mass-lanes`，仅将三个接入模块列为 strict/replay
目标。75 个 project 模块的完整源码与实际编译对象闭包均被绑定，其他 72 个
provider 在目标 strict 期间冻结。所有 project 对象在最终 audit 后再次冻结。

新 intake 检查固定原文件的 Git blob、SHA256 和字节数，固定 20 个片段，
逐段对照原字节；唯一允许的调用适配由精确替换规则复核。旧 helper、旧 group、
80 模块 baseline 保留检查、原完整环境库存 equality、三公理白名单以及公共
strict/replay 流程保持不变。允许公理仅为 `Classical.choice`、`Quot.sound`、`propext`。

正式命令需要在固定源码提交的独立干净工作树中执行，使用新的输出目录：

```sh
python3 -B verification/verify_part3_continuation.py \
  --group smooth-mass-lanes --expected-head SOURCE_COMMIT \
  --output-dir .lake/p31-smooth-mass-lanes-final
```

P3 和备用接口在本轮初始连接时返回 HTTP 429；P1 使用相同的固定工具链执行
验证。代码在本地编写，云端工作树仅同步和编译。预检在逐一核对源码后复制
485 个既有模块的缓存，保留 Lake 的原依赖跟踪并通过普通构建校验；捐赠目录
未被修改。三个目标随后单独严格重编译。缓存复用及中断重试记录随回执归档，
不重新把旧证明计为本轮成果。

## 稿件位置与尚未完成部分

1106 英文稿固定为 `chen-imbalanced-semiprimes` 提交
`a988cba584d803ae2856a0de50efb582f4f3dd6a` 的
`paper/release-20261106/en/analytic-appendix.tex`，SHA256 为
`e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`。
本轮对应 689–694 行的完整 b-Poisson 入口及 700–717 行共同有符号区间的
有限组合连接。所选连接没有发现实质证明缺口；发生的适配属于定义 owner
及已有 theorem 参数形式的对接。

尚需继续接通真正 `OriginalData/FixedBlock` 及原始全族能量、全族 J 的选择
与零尾项估计、实际谱 `PacketData/hkernel` 和原生 J/A 输入。
Shiu、Theorem J/A、ABL、Kim–Sarnak 等外部解析输入保持原有边界。
