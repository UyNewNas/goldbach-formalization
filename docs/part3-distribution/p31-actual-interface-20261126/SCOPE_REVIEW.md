# P3.1：接口本体、既有证明与历史附件的范围复核

复核日期：**2026-11-26，Asia/Shanghai**。本文件记录独立的范围、来源和接口审查；新增代码的严格编译、内核重放及完整声明审计由本轮实际验收回执决定。本文件本身不作新的 Lean 验收声明，也不修改看板状态。

## 1. 当前看板记录

只读核对的站点是 [Goldbach 形式化看板](https://goldbach-formalization-board-20261107.slava2333.chatgpt.site/)。Sites 返回的最新已保存版本为 **10**；另从当前在线 HTML 实际读出了 P3.1 节点，以下内容没有从旧截图推断：

| 字段 | 当前在线记录 |
|---|---|
| `id` / `parentId` | `P3.1` / `P3` |
| 标题 | 原始物理模数/共同区间/共同加法相位接口 |
| `status` / `historicalStatus` | `blue` / `blue` |
| `scope` | `internal` |
| `currentVerified` / `reviewPending` | `false` / `true` |
| `latestCommit` | `7f5330cace31383f5626da526b476dd4b0f43376` |
| 直接依赖 | 空数组 |
| 下一步 | 为相同源码、实际输入与完整目标闭包补齐验收记录 |

节点的说明和 blocker 仍描述 source68：给既有 Shiu WindowGate caller 插入原 Cover namespace 的 `open`，静态解析九个同级 provider 名称；该修复没有新定理或编译，不代表 PrimitiveShiu/fullNative6 验收。旧 `565b`、V16/V17 选择及 HOLD 作为历史保留。

这与 [上轮保存的节点记录](../p31-interface-20261125/BOARD_SCOPE.json) 的数学边界一致。当前在线节点尚未纳入 `eac59fac68a389eee5d15c3c44eb9dd487049ab9` 的接口证据或 P3.2 的新验收，不能据此推断这些已有证明不存在，也不能用新接口的回执覆盖 source68 的原来源要求。

## 2. 固定手稿与逐项责任

参考稿为 1106 英文冻结版。此次读取的 `analytic-appendix.tex` 在稿件提交 `a988cba584d803ae2856a0de50efb582f4f3dd6a` 和 P3.2 采用的 `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` 中均为 Git blob `7cf3bbb16cd8924565eb439e474e0674f04631da`，SHA-256 为 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`。

| 稿内责任 | 对应位置 | 已有覆盖和本轮处置 |
|---|---|---|
| 原物理完整模数、分离的 gamma 系数、精确互素中心，符号保留在复数和内 | [受限中区命题 `prop:current-medium`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex) | `Part3DistributionTargets`、`Part3ComplexDispersion`、`Part3FactorFiberDivisor` 已实现相应定义与恒等式。`MediumAtom.signedError_eq_groupedFactorGamma` 按同一实际乘积重组，未把因子长度替换成物理模数。继续复用。 |
| 从实际原始差额进入中心化能量，支付原始 primitive 主项并留下同一非零和 | `ana:variance`、`ana:mean`、`ana:dispersion-bound` | P3.2 已验收的实际父链从 `MediumAtom.signedError` 出发。它保留原 `UniformAuxiliarySW` 假设与先常数后原子的量词；无须另写同义归约。 |
| 归一化 amplitude 的 Fourier 分离；共同区间、共同相位；packet 变换前后保持真实系数 | [附录 `ana:kernel`、`ana:packet-coefficient`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/analytic-appendix.tex) | `Part3ActualLiteralPacketIntegral` 已给出实际 `PacketData`、`completed`、`modePacket`、点态和积分重构；七个 provider 原样恢复。不可重新实现这些证明。 |
| 对同一纯 m 侧函数，以公共 I 和 omega 消费全块、全相位输入 | 附录 `ana:exceptional-average` | `Part3CommonIntervalFourier`、`Part3ExceptionalWeightExtension` 与上轮 `Part3CommonCompletedInterface` 已证明有限 completion。此次增量应应用实际 `P.completed k`，控制原始 `P.mCarrier`，并保留纯 m 侧输入形状。 |
| signed packet 双和的真实乘积核分解与有限 Cauchy 接口 | `ana:packet-coefficient` 及其后的谱估计使用方式 | 此次增量应保留实际 `signedCoefficient`、`modePacket`、n carrier 和共用 m functional；先证明恒等式，再分别使用 m、n 两侧能量。不能将双和的待证总能量当作 Theorem J 输入。 |
| 平移进程化约与 Shiu 有限 cover 的历史来源 | 附录 `ana:shifted-divisor` | source68/FiniteCover 的来源与验收独立保留；它不属于此处 literal producer 或 common-energy 的 import 闭包。 |
| 外部 Theorem J、ABL、Kim–Sarnak 及引用的谱输入 | 附录相应外部引用 | 保留原条件和归一化，作为明确输入。本轮不形式化这些稿外定理。 |
| 原始物理全族到全部 automorphic packets、regular/exceptional/Plancherel 分支与完整费用回收 | 原中区结论的下游谱组装 | 与 P3.5 的实际全族责任相连，尤其 `P3.5.child-3` 的共同 m 与 zero/tail 重组。不能从共同接口验收推出这些组装已完成。 |

## 3. 已有 literal producer 的真实内容

`Part3ActualLiteralPacketIntegral` 的固定源 SHA-256 为：

```text
500b7c1476c8afb777551807f1f737b17d785aeafec401c7b691fd46b0b9aa55
```

它的 `PacketData` 保留有限 rows、每行 `CoprimePacket`、每行 n carrier、共同 `lo`/`hi`、尺度与 kernel。实际 m carrier 是 `Finset.Ico P.lo P.hi`，实际完成变量满足

\[
  (P.\mathrm{completed}(k)).\omega=\frac{k_1}{64P.V}.
\]

已有 `modePacket` 证明调制后的 beta 与 transformed coefficient 的范数保持，保留 `level_pos`、`residue_coprime`、原 beta 参数和 unit phase。signed coefficient 的正支为 `e(-n/z)`，负支为 `e(+n/z)`；二者没有被当作相同复数。`pointwise_hasSum` 与 `hasSum_coefficient_times_modeIntegral` 使用原始 row、carrier、cutoff 和同一个模式分解。

P3.2 六个 fresh replay 终端之一 `Part3ActualKPacketAdapter` 进一步给出 `withKKernel_frozen`、`kModeFunction` 和 `k_hasSum_coefficient_times_modeIntegral`，将同一真实 K/q 积分写成共同 completed weight 与 signed mode packet 的模式积分。该终端是绝对交换及重构接口；它本身不供应谱节省。旧文件头中的 `SOURCEONLY` 说明早期作者状态，当前采用值以固定字节的后续验收回执为准。

## 4. 纯 m 侧 Theorem J 输入与一般 `full_uniform` 的区别

手稿 `ana:exceptional-average` 控制的对象是

\[
 \sum_i X^{\tau_i}
 \left|\sum_{m\in I}e(m\omega)R_{i,\infty}(m)\right|^2,
\]

其中 i 包含 level 和谱指标。共同 I、共同 omega 对所有 level 相同。Fourier 系数 `R` 可以依赖谱指标；独立于 spectral height 的是 packet 的 beta、n carrier 等测试数据，不能把这条限制误施加到 `R` 本身。

上轮一般 transport 的前提允许

\[
 a_i(m)=\sum_{n\in C_{\ell(i)}}b_{\ell(i)}(n)K_i(m,n),
 \qquad
 \forall\rho,\ \mathrm{Energy}_{\mathrm{full}}(\rho,a)\le B.
\]

这个一般命题本身有效，但 **Theorem J 不能直接提供任意已经含 n 求和的数组 a 的上述前提**。把这种前提命名为 `full_uniform` 不能支付 n 侧的谱责任。

本轮应先对实际 `P.completed k` 消费纯 m 侧全块、全相位输入，再对实际 signed packet 的乘积核作精确有限分解。固定 P、k 以及 packet-row 投影后，写

\[
 M_i=\sum_{m\in P.\mathrm{mCarrier}}(P.\mathrm{completed}(k)).\mathrm{weight}(m)u_i(m),
 \qquad
 N_i=\sum_{n\in P.\mathrm{nCarrier}(\ell(i))}
   b_{\ell(i),k}(n)v_i(n),
\]

其中 b 是原 `signedCoefficient` 与原 `modePacket`。乘积核对应的同一双和必须证明等于 `M_i * N_i`，随后有限 Cauchy 分别保留两侧能量。若一侧有复共轭，它也必须原样留在所选函数中。n 侧输入继续明确列出，不假设待证的双和总能量界。

这里的 factorization 是稿内两侧谱估计的有限接口，不声称已构造 Kuznetsov、Maass/Eisenstein 归一化或完整物理谱族。

## 5. 本轮 consumer 的必要验收条件

1. **控制完整原 carrier。** `PacketData` 的归一化盒支撑并不自动给出 `P.mCarrier` 包含于所选 dyadic `fullBlock j`。控制完整 carrier 的定理必须证明或明确携带该包含关系。若只证明交集上的和，须按交集范围报告，不能静默丢弃原 carrier 外部项。
2. **实际相位和符号保持。** 结论使用原 `P.completed k`，包括其 `k 1 / (64 * P.V)`，并保留两个 cusp 分支的原 signed coefficient。区间或相位不重新依赖 level/height。
3. **测试系数的高度独立。** 有限谱族通过实际 row 投影取得 packet 和 n carrier；height 只能进入谱函数／kernel。固定 P、k 和数组以后再量化全相位 rho，不随 rho 重选 beta 或 carrier。
4. **两侧责任分开。** m 侧 Theorem J 输入不含 n 求和；n 侧能量及后续 ABL 等条件保留为独立输入。有限 factorization/Cauchy 不能把目标界藏回假设。
5. **真实增量验收。** 新 consumer 的完整源码、实际项目 import/object 闭包、严格编译、bundled replay、完整 owned 类型及传递公理审计均应绑定同一提交。既有 provider 只沿用其已有验收，不作为新证明计数。

当前候选 `Part3ActualCommonCompletedInterface` 的声明已按上述条件作源码范围核对：`fullBlock_weight_sum_eq_mCarrier` 和 `modeCore_eq_fullBlock` 明示真实包含条件；`spectral_mSide_weightedEnergy_le` 只在纯 `Rinf` 上要求全相位输入；`rowPair_eq_nSide_mul_mSide` 给出有限乘积恒等式；`modeCore_eq_sum_nSide_mul_mSide` 将实际 kernel 的逐点乘积识别保留为明确的 `hkernel`；`spectral_pair_norm_sq_le` 对 `sqrt(W ^ exponent i)` 加权的原双和应用有限 Cauchy，n 侧仍是原能量。这里没有声称已从任意 `P.kernel` 自动构造该乘积识别，也没有把源码范围核对当作编译结果。

## 6. 复用证据的两层范围

[HISTORICAL_REUSE.json](HISTORICAL_REUSE.json) 核对 `REUSE_SOURCES.json` 的七个原样恢复文件。literal producer 的项目闭包为 56 模块：49 个已有源不变，七个恢复源逐字节等于 P3.2 发布提交 `30e2a96b601458d59116517ca478c496a68a39c9` 和其被验源码提交 `34201be0ca95d465336119fce24b7681c17ab0c6`。

| 恢复模块后缀 | 历史完整 owned 声明数 |
|---|---:|
| `Part3ActualLiteralPacketIntegral` | 97 |
| `Part3ActualNormalizedSmoothF` | 53 |
| `Part3ActualSampledFourierLattice` | 56 |
| `Part3ActualWeightedSpectralBudget` | 31 |
| `Part3CompactCoordinateFourier` | 37 |
| `Part3NativePeriod64Reconstruction` | 67 |
| `Part3NativePeriod64Sampling` | 37 |
| **合计** | **378** |

六份不同的原始 receipt 已从固定历史提交 `10b89181754c78c0e77616677295ee2105de0bb6` 读回并原字节保存到 `history/`。每份完整 SHA-256、目标源哈希、前后输入相等、选定模块的 stock replay 成功和完整 inventory/type/axiom 阶段退出码均已核对。receipt 中其他模块不计入本次复用范围。378 个声明的完整类型 canonical 哈希与公理摘要沿用既有 P3.2 compact extraction；本轮没有重新下载或审计十余 MB 的累计声明文件。原累计 census、声明文件和 root acceptance 的不可变 URL 与哈希完整保留在 manifest 中。公理范围仅 `propext`、`Classical.choice`、`Quot.sound`。

较新的 [P3.2 原 report](history/p32-report.json) 与 [ACCEPTANCE](history/p32-ACCEPTANCE.json) 绑定了 **130 个项目模块的构建对象**，新严格编译和重放的是六个终端、138 个声明。七个恢复 provider 不在那六个 fresh 目标中；它们沿用各自历史 owned replay。130 个对象的绑定不等于把全部历史 provider 或全部外部库重新 replay。本轮也不把旧 `.olean` 哈希视为当前工作树对象已经存在或已经通过新 replay。

原 80 模块基线和上轮六声明 common-interface 回执继续按既有路径引用，未复制或重写；[上轮来源清单](../p31-interface-20261125/SOURCE_MANIFEST.json) 保留其精确条件。

## 7. source68 和 P3.5 的独立边界

source68 的 `Part3MediumPrimitiveShiuWindowGate` 导入 `Part3MediumPrimitiveShiuFiniteCover`；这是该历史 caller 的真实依赖。它不在本轮 literal producer 的 56 模块闭包，也不在已验收 common-energy adapter 的闭包。其 namespace 修复和来源恢复要求继续保留，不通过本轮接口回执代为验收。源码未恢复本身不是手稿数学反例，也不是推定新实质性证明缺口的依据。

`Part3ActualLiteralPacketIntegral` 末尾另明确保留：以原始 frozen beta 实例化实际有限 `(nu,z)` 和 n 矩形，以及实际 regular/exceptional/Plancherel kernel。P3.4 新验收的固定高度 cusp Fourier normalization 没有把这些系数识别成 height-independent Maass/Eisenstein 数据；P3.5 新验收的高度 exhaustion 仍保留实际两侧能量与 test-envelope 输入。这些全族构造和费用回收不能从本次共同接口恒等式推出。

因此本轮可验收的结论应准确命名为 **P3.1 literal packet producer 到共同 m 接口、及实际 signed packet 两侧 factorization/Cauchy 的连接**。原物理模数和 primitive center 采用既有已验接口；外部谱输入维持原边界；source68 历史附件与 P3.5 全族组装分别列出。新 consumer 完成后也不自动宣称整个旧看板附件集合、fullNative6、完整 P3 或最终 1+1.7482 已验收。
