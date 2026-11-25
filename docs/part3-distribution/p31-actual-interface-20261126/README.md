# P3.1：实际 packet 与共同区间能量接口

## 本轮范围与验收状态

本轮接续 `eac59fac68a389eee5d15c3c44eb9dd487049ab9` 的已验收共同区间接口，
把 P3.2 已有的真实 `PacketData` Fourier producer 接入它。
**本轮接口已通过 P3 云端验收。** 固定源码提交为
`acfa81c6d593276ef50f8af4e4f79b150772d7c8`，成功任务为
`691cc77d9c654ec4954ded0f1b7bc02d`。严格编译、bundled `leanchecker`
重放、完整声明枚举及传递公理审计均通过；新增 10 个声明包含 6 条定理和
4 个定义。验收完成时间为北京时间 2026-11-26 01:03:54。

最终归档提交只更新文档和证据；实际 Lean 源码与验收器固定在上述源码提交。
机器可读的结论见 `ACCEPTANCE.json`，云端任务原始元数据见 `RUN.json`，
完整回执见 `verification.zip`，主要日志另展开在 `verification/` 便于浏览。
独立产物复核 `ARTIFACT_REVIEW.json` 核对了 105 个源码/配置哈希、
35 份阶段日志、完整声明清单及对象冻结证据，未发现问题，也未重复运行 Lean。

正式入口为 `ImbalancedChen.Part3Node31`。本轮新增数学模块只有
`ImbalancedChen.Part3ActualCommonCompletedInterface`，其余七个恢复的 Lean
模块逐字节复用 P3.2 提交 `30e2a96b601458d59116517ca478c496a68a39c9`。
原 80 个基线证明文件和上轮的 `Part3CommonCompletedInterface` 保持不变。

手稿是 1106 英文冻结稿，`analytic-appendix.tex` 的 Git blob 为
`7cf3bbb16cd8924565eb439e474e0674f04631da`；对应 `ana:kernel`、
`ana:packet-coefficient`、两侧谱 Cauchy 段及 `ana:exceptional-average`。

## 六项实际连接

| 新定理 | 准确结论 |
|---|---|
| `fullBlock_weight_sum_eq_mCarrier` | 在实际 `P.mCarrier ⊆ fullBlock j` 支撑证据下，全块加权和与完整原 carrier 上的和精确相等。空区间和反向区间也保留。 |
| `modeCore_eq_fullBlock` | 原 `P.modeCore` 等于共同权重的全块展开；原 `P.kernel` 不改变。 |
| `spectral_mSide_weightedEnergy_le` | 把纯 m-side 的全相位全块界传到实际 `P.completed k`、`P.mCarrier` 和有限 row/height 索引。 |
| `rowPair_eq_nSide_mul_mSide` | 对乘积 Fourier kernel，实际 signed packet 的 m/n 双和精确因式分解为两侧函数。 |
| `modeCore_eq_sum_nSide_mul_mSide` | 由原 kernel 的逐项乘积身份接回原 `modeCore`；没有假设待证的整体估计。 |
| `spectral_pair_norm_sq_le` | 复用有限复数 Cauchy，保留实际 n-side 平方范数，仅用纯 m-side 的解析能量输入。 |

有限谱索引为 `Σ row : P.rows, Height row.1`。`packet` 与 `nCarrier` 只能通过
row 投影读取；Fourier 系数和异常指数可以依赖 height。所有层使用同一个
`P.completed k`，其相位为 `k 1 / (64 * P.V)`。正负 cusp 均使用已有的
`signedCoefficient P.negativeCusp`，保留各自的复数相位。

记实际两侧函数为 A_i、B_i，原乘积 kernel 的双和为 Q_i。新增 Cauchy 消费者给出

\[
\left\|\sum_i\sqrt{W^{\tau_i}}Q_i\right\|^2
\le \left(\sum_i\|A_i\|^2\right)
4(2+\log P_j)^2\max(1,(W/T)^{\mathrm{cap}})\,\mathrm{bound}.
\]

前提是对**同一纯 m-side Fourier 系数数组**、每个共同相位 rho 的全块能量界，
以及 `W,T > 0`、`0 ≤ tau_i ≤ cap` 和实际 carrier 包含关系。
这里没有把含 n 求和的乘积能量假设改称 Theorem J，也没有证明外部 Theorem J。
n-side 的解析估计仍由其对应外部输入支付；本定理保留该侧实际平方范数。

调用方还须将这个**有限 row/height 索引**与外部估计的实际谱族逐项对应。
手稿在固定 packet 参数 nu 后使用 level-average 界；若 rows 同时含多个 nu，
或同一 level 的重复标签，必须先证明相应重数费用，不能把固定 nu 的界直接
用于扩大的联合族。无限谱或连续谱的极限/积分步骤不由本有限消费者支付。
原 `modeCore` 的两侧分解另要求明确的逐项 `hkernel` 身份，不能从
`PacketData` 的一般连续 kernel 字段自动推出。

## 原样复用与实际输入

`REUSE_SOURCES.json` 固定七份恢复源码的 SHA256。Literal producer 的 56 模块
项目闭包中，其余 49 份源文件与当前分支完全相同。已有的 Fourier 重构、
积分交换、beta 单位相位调制及 L2 保持均不重写。

`HISTORICAL_REUSE.json` 与 `history/` 保存真实旧验收来源，区分历史 owned
replay、P3.2 新回执中的对象绑定和本轮新模块的严格复编。旧源码头中的
`SOURCEONLY` 是历史作者状态，不能覆盖后来与同一源字节绑定的实际验收记录。

`Part3Node31` 同时导入已验收的原物理 q1*q2*q3 分组、精确 primitive-coprime
中心和共同平滑链。没有把分解个数丢掉，没有改变原 gamma 的符号，也没有
将物理模数替换为辅助长度。

## 可复核的增量验收

以下命令应在固定源码提交 `acfa81c6d593276ef50f8af4e4f79b150772d7c8`
的干净工作树中运行。`actual-interface` 是显式增量组，旧 `--group all`
不会自动纳入本模块。

```sh
python3 -B verification/verify_part3_continuation.py --source-only \
  --group actual-interface --output-dir .lake/p31-actual-source-check
LEAN_NUM_THREADS=1 python3 -B verification/verify_part3_continuation.py \
  --group actual-interface \
  --expected-head acfa81c6d593276ef50f8af4e4f79b150772d7c8 \
  --output-dir .lake/p31-actual-interface-verification
```

`CLOSURE.json` 固定从正式入口重算的完整项目源码闭包。验收器复用已验收 P3.2
的闭包与对象冻结检查及原完整声明/公理审计；拒绝缺失、额外、重复、改动的源记录，
绑定 Lake 实际解析到的项目对象及 sidecar。只对新数学模块执行 fresh 严格编译和
bundled `leanchecker` replay；已验收 provider 不重复申领 fresh replay 信用。
通常的缺失依赖构建与证明重新验收明确区分。

本次实测完整任务耗时 471.255 秒，峰值内存 8,549,105,664 字节。
验收器的 35 个阶段全部退出码为 0；其中新增模块严格编译 7.948 秒、
内核重放 8.906 秒、声明与公理审计 301.830 秒。实际项目闭包共 64 个模块，
依赖对象在严格编译期间保持不变，全部项目对象在重放和审计后保持不变。
10 个完整声明的传递公理均仅含 `propext`、`Classical.choice` 和 `Quot.sound`。

首次任务在依赖构建阶段超过 10,000 MB 服务内存限制而终止，未形成通过回执。
保持源码不变，将任务限制提高为 13,107 MB 并改为单线程后验收通过。
两次任务的服务状态都如实保存在 `RUN.json`，失败尝试的日志在归档
`prior-memory-attempt/` 中；不会将其未结束的 `RUNNING` 报告算作通过。

证明归档为 77,130 字节、43 个成员，SHA256：
`c292e9bd98bfd7d4e788312054658b924b8dd86e4e5ae0e6c861ac7a47e248ba`。

## 未由本次接口关闭的责任

source68 的 WindowGate/FiniteCover 附件不在本次导入闭包，仍单列为原始源码
恢复及验收问题。`SOURCE68_RECOVERY.json` 记录了已完成的 P1 检索与其边界：
142,456 个普通文件、129 个候选归档路径和 6 个 Git 对象库中，已检查部分未找到
两份已知源字节；一个大 ZIP 的专项补查在该记录冻结时仍排队，P2 和备用环境
未完成源码检查。这不是全局缺源结论。原 `MediumAtom` 到全部实际 automorphic packet 的族构造，
以及 regular/exceptional/Plancherel 完整组装、zero/tail 的物理支付和 7/32
最终返回属于 P3.5 后续责任。本次不声称完整 P3 或最终 1+1.7482 已证明。

当前看板 P3.1 仍将共同接口本体与 source68 历史附件合写；本次证据应按上述
范围逐项阅读，不能自动替历史附件申领编译验收。详细范围裁定见 `SCOPE_REVIEW.md`。
