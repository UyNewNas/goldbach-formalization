# P3.2：完整实际入口与同源闭包

本轮目标是看板的 **P3.2「CRT→Fourier→Poisson 与零模／原始主项支付」**。正式入口为 `ImbalancedChen.Part3Node32`。它直接导入六个已有终端，不创建同义定理，不改写原始假设或结论。

本页区分数学范围、历史复用和本轮实际验收。**历史源码匹配或 source-only 检查本身不表示节点编译完成。** 正式结果须以本目录收录的同源 CI 回执为准。

## 已有证明的完整入口

| 终端模块 | 本节点的实际职责 | 历史声明数 |
|---|---|---:|
| `Part3ComplexCRTFiniteFourier` | 原系数、原有限 carrier 上完整 CRT／Fourier 恒等式；保留实际 primitive centers | 17 |
| `Part3SharedFirstFactorEnergyNonzeroReduction` | 在实际 `signedError` 上支付共同 Poisson 零协方差及 primitive U/V 误差，保留两个原始外部 L2 因子 | 3 |
| `Part3ActualCompletedZeroDifferencePayment` | 同一个 completed piece 的零差／非零差分解及实际零差支付 | 49 |
| `Part3ActualNonzeroChartEpsilonTagPayment` | 实际非零 chart 与 tag 的计数、系数预算，保留物理及调和因子 | 21 |
| `Part3ActualZeroTagFreeEpsilonPayment` | 实际 Fourier 系数、tag 与除数费用的可选 epsilon 支付 | 26 |
| `Part3ActualKPacketAdapter` | 实际选择的 K/q 核、mode 积分展开与绝对交换预算 | 22 |
| **合计** | **六个历史终端；不计为新证明** | **138** |

`CLOSURE.json` 列出六终端的全部 **130 个项目源码模块**及外部直接 imports。缺少的 **73 个模块**逐字节复用自远端提交 `10b89181754c78c0e77616677295ee2105de0bb6`；56 个当前文件原已相同，另一个 `Part3PhysicalSmoothReciprocalPoisson` 保留已验收基线的文档头变体。没有覆盖原 80 个基线证明文件。

父闭包包括 `complexDispersionW_eq_constructedCRT`、`complexDispersionW_commonSmooth_eq_zero_add_nonzero`、`q1SliceDispersionW_eq_sharedCRT`、`q1SliceDispersionW_eq_sharedPoisson`、`sharedFirstFactor_centered_identity`，以及实际 reciprocal-square Poisson、M2 有限 mode 展开。不能只取三个局部 payment 与 K adapter 的旧回执，省掉这一实际父链。

## 原始主项支付的终端

关键结论是：

```lean
uniformAuxiliarySW_sharedFirstFactor_signedError_sq_le_nonzero_add_log_payment
```

令 `d = F i`，`x = d.scale`，并保持原始表达式：

\[
W(d)=\left(\sum_{n\in d.\mathrm{betaCarrier}}\|d.\beta(n)\|^2\right)
\left(\sum_{p\in d.\mathrm{primitiveFirstFactorCarrier}}\|d.\gamma_1(p)\|^2\right),
\]

\[
N(d)=\sum_{p\in d.\mathrm{primitiveFirstFactorCarrier}}
(d.\mathrm{q1SliceAtom}(p)).\mathrm{transposedAtom.complexCRTSmoothNonzeroPart}.
\]

已有终端证明

\[
\|d.\mathrm{signedError}\|^2
\le W(d)\operatorname{Re}N(d)+C\,x^2/(\log x)^A.
\]

量词顺序是 `∀ A > 0, ∃ C > 0, ∃ x0 > 1, ∀ i, x0 ≤ (F i).scale → ...`。常数与阈值先于具体原子。实际假设为原始 `MediumAdmissible`、`0 < sigma < 1/100`、`0 ≤ kappa ≤ sigma/100`、`c0 > 0`，以及手稿明确列出的原始族 `UniformAuxiliarySW F C0`。没有假设待证的主项界或非零能量界，也没有把任意 transposed atom 当作完全 admissible。

前两个同文件定理先给出原能量减去同一非零和的精确恒等式，再连同 `W(d)` 支付零协方差与 primitive U/V 误差；最后接回原 `signedError`。后续估计 `N(d)` 属于下游工作。

## 手稿与看板范围

冻结手稿：[1106 analytic appendix](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/analytic-appendix.tex)。本地所读文件与该提交及旧 source manifest 的 `a988cba584d803ae2856a0de50efb582f4f3dd6a` 均为同一 Git blob `7cf3bbb16cd8924565eb439e474e0674f04631da`，SHA-256 为 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`。

| 手稿标签 | 本节点实际内容 |
|---|---|
| `ana:variance`、`ana:gram`、`ana:mean`、`ana:cross` | 同一原始中心化能量与 primitive 主项 |
| `ana:principal-variance`、`ana:filtered-BDH` | 初次 CRT／Poisson 零频中必须估计的主协方差 |
| `ana:dispersion-bound` | 支付主项后保留真实非零指数和 |
| `ana:W4-expansion`、`ana:beta-definition`、`ana:off-diagonal-kernel` | 同一完成平方表达式的 `y = 0`／`y ≠ 0` 分解与局部零差支付 |

有限 Fourier 的 sampled 零频与 Poisson 的积分零频不同，连接的是完整 progression 展开。初始 Poisson 零协方差、完成平方的 `y = f(h1*s1-h2*s2) = 0`，以及后段物理 b-Poisson 的 `m = 0` 必须分别识别。

`BOARD_SCOPE.json` 保存已发布看板第 8 版的原节点记录。`P3.5.child-3` 明确拥有原始全族的共同 m 与 zero/tail 重组；`P3.5.child-5` 明确拥有 OriginalData 两个 zero lane 的归一化费用。完整 E2 返回、原始全外层物理支付、统一 7/32 谱估计及 `RestrictedMediumObligation` 不由本节点关闭。

## 本轮验收规则

```bash
python3 -B verification/verify_part3_node32_reuse.py
python3 verification/verify_part3_continuation.py --group node32 \
  --expected-head "$(git rev-parse HEAD)" --output-dir /tmp/p3-node32
```

历史复用检查仅返回 `HISTORY_SOURCE_MATCH_ONLY`；详见 `README-HISTORICAL.md`。它绑定 72 份原 audit、89 个历史 owned 模块、41 个 trusted imports，以及 3615 条旧完整声明记录，不将它们计为本轮新增声明。

实际 continuation gate 保持固定 Lean、Mathlib、goldbach 和干净依赖；从源码重新计算六入口的完整 import 图，拒绝遗漏、多余或重复条目；通过 Lake 构建入口后，逐项绑定全部 130 个项目模块实际解析到的对象及 sidecar 哈希。六终端按 warning-as-error 严格复编、由 bundled `leanchecker` replay，并检查全部声明类型及传递公理。provider 对象在严格复编阶段冻结，全部项目对象在 replay／inventory 后再次核对。

信任范围继续为 `NORMAL_IMPORTED_ENVIRONMENT_TRUST`。完整项目对象绑定不等于重放全部历史 provider，更不表示全 Mathlib／native／external 图已重放。允许的传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`；原稿中显式的 `UniformAuxiliarySW` 是定理假设，不是新增 Lean axiom。

本轮范围核对期间产生的物理零差费用草稿独立保存在 `docs/source-only/20261125-p32-followup/`。它属于 P3.5 后续增量，状态为未编译，不参与本节点完成判断。
