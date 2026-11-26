# 原 singleton 两长的两个次要幂次预算

**状态：source-only，未进行 Lean elaboration、编译或 kernel/full-owned 验收。** 本目录只增加 `P1OriginalSingletonTwoLongSecondaryPowerPayment.lean` 中的一条实际参数定理，不修改任何既有源码。

它对应固定 1106 手稿 `coefficient-appendix.tex` 第 797–821 行中的 `M(U+V)Y` 和 `MY²`。此前 L 的 `P1OriginalSingletonTwoLongPowerPayment` 已支付主导项 `MY²D^(3/2)`；密度项由另一独立的 `ActualBrunDensity` 候选处理。

## 实际合同

输入仍是原 singleton 实际 rectangle：`j ∈ range 3`、同一组互异 occurrence 索引 `i,k`、`ns ∈ rectangle bs`、这个实际 tuple 的 `scalarProfile ≠ 0`、原短位置上界，以及 dictionary 已证明的 `longPositions (originalMediumHigh zeta [cj]) bs = {i,k}`。没有聚合系数非零或整 rectangle 活动性的假设，也没有把目标误差或长块幂下界作为新假设。

全块尺度 `X0 = shortScale bs = MUV`、原 `Z = beforeHBCutoff cutoffOrder [cj]`、`Y = Z^(2*halfOrder X0+1)`、`D = floor(X0^(1199/2000))` 均保留。固定的 accuracy、smooth/frequency/log/cutoff orders 及小参数先于物理 `N` 阈值；profile order、chart、HB row、tuple、`i,k` 和全部历史模数参数均在其后。

结论同时给出以下四条各自的预算：

- `pairCost * M(U+V)Y * log(X0)^extraLog ≤ X0/log(X0)^accuracy`；
- `pairCost * MY² * log(X0)^extraLog ≤ X0/log(X0)^accuracy`；
- `M(U+V)Y * log(X0)^extraLog ≤ X0/log(X0)^accuracy`；
- `MY² * log(X0)^extraLog ≤ X0/log(X0)^accuracy`。

后两条直接对应手稿的裸固定对数项，不依赖任何 `pairCost ≥ 1` 假设。原 `remainingModuli levelB N (trueDDeltaSupport old fresh N cap w z)` 的 `q ≤ D` 结论及 `1 ≤ D`、`1 ≤ log X0` 一并保留；不替换 `Q` 或 `rho`。

## 最小推导与复用

新的独立 `P1OriginalSingletonTwoLongLowerScale` 供应者从原 long-position predicate 给出 `U,V ≥ X0^(1/4)`。本文件只调用它。由真实 `MUV=X0`，正因子消去给 `MU,MV ≤ X0^(3/4)`。原 FixedScaleTransport 取固定 `epsilon=1/16000` 给原 `Y ≤ X0^epsilon`；旧 fixed-log supplier 用 `1/16` 的余量吸收常数 2，得到交叉项至多 `X0^(13001/16000) ≤ X0^(7/8)`。

旧 `eventually_pairCost_power_payment` 以 `eta=1/8` 支付加权交叉项；L 已有主导项付款与 `D ≥ 1` 支付加权平方项。裸项使用同一个阈值中的旧 `eventually_fixed_log_le_power`，次数为 `extraLog+accuracy`、余量为 `1/8`。又有同一实际 `Y ≤ X0^(1/16000) ≤ X0^(1/4) ≤ U ≤ U+V`，故裸平方项由裸交叉项控制。

所有实数阈值均用既有 `N^(1-kap0)/64 < X0` 提到物理 `N` 之前。没有重证 Brun、Rates、P2 或任何外部估计。

## 来源、审查与采用边界

最终 Lean：11,984 bytes，SHA-256 `2b08b61d59f3b50a95df9ad582a2be627104655d4d7ef2ef088f9464a680b182`。直接 imports 只有既有 PowerPayment 和新的 TwoLongLowerScale。后者最终为 5,842 bytes / `a699da3536e0cd339afda18db2876416c29a33b06c8b110b86c002903c090d9e`，当前仍是未发布 scratch 依赖。

`SOURCE_REVIEW.json` 保存唯一声明的精确字节区间、全部直接使用的来源 pins、固定稿件 locator、9 个公开 Git 源码的逐字节回读结果、量词和合同边界。`BARE_LOG_DELTA.patch` 记录对初始加权版本追加两条裸项结论的精确增量；`CANCELLATION_API_DELTA.patch` 记录两处正右因子取消改用匹配 Mathlib 的 `le_of_mul_le_mul_right`。

根代理已独立审阅基本数学链和裸项增量。审查发现的取消 API 问题已按固定 Mathlib 原声明修正；没有执行 Lean，不能据此记编译或验收信用。采用时必须提供新的 LowerScale owner，并继续遵守既有 shared finite geometry / PhysicalSupport 的互补 provider 路由。

本文件不声称完成四项误差的有限恒等式、fixed-m 算术 core、P2/Fourier 总装配或 P1.5 终端；也不恢复已记录的缺失供应。两条裸预算是分别成立的结论，尚未在此合成一个完整 rough-error theorem。
