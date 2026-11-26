# Actual singleton two-long：固定幂次支付

**状态：source-only，未 elaboration，未取得 normal、kernel 或 full-owned 验收。** 原草案在环境恢复后原样回读；本轮没有重建或修改 Lean 文件。根代理与作者均完成了针对该原字节版本的静态合同检查，未发现具体数学或接口阻断。

## 本包新增的连接

唯一新声明 `eventually_actual_singleton_twoLong_power_payment` 将已经固定的实际矩形尺度接到原 `eventually_twoLong_E4_monomial`。它不重证 Brun、P2、Rates 或对数吸收。

保留原始对象：`X0 = shortScale bs` 是所有 block 下端的乘积，`M` 是同一对 occurrence 索引之外的下端积，`U,V` 是那两个原 block 下端。原 `Z = beforeHBCutoff cutoffOrder [cj]`、`Y = Z^(2*halfOrder X0+1)` 不变；`D` 固定为 `floor(X0^(1199/2000))`。

既有 FixedScaleTransport 直接支付 `M <= X0^(40*zeta)`、`Y <= X0^(1/16000)`。正自然下端给出 `M,U,V >= 1`，而原精确恒等式 `X0=M*U*V` 给出 `U,V <= X0`。因此可以在旧 scalar supplier 中合法取 `c=1`，不增加尺度上界假设。

旧 `fixed_margin` 在 `zeta <= 1/400` 下给出

\[
40\zeta+2/16000+\tfrac32(1199/2000)\le1599/1600<1.
\]

其余所有对数和 profile 成本由原 generic theorem 吸收。本包结论为

\[
\operatorname{pairCost}\big((\log X_0)^{-B},U,V,(\log X_0)^K\big)
\,M Y^2 D^{3/2}(\log X_0)^E
\le X_0/(\log X_0)^A.
\]

附带的 `q <= D` 使用原 `remainingModuli levelB N (trueDDeltaSupport old fresh N cap w z)`。本结论没有替换 `Q`，没有对 `rho` 添加条件；它本身也不声称已经取得带 `rho` 的有限分布误差。

## 量词与原稿位置

所有固定精度、平滑、频率、对数与 cutoff 阶数先于物理 `N` 阈值。随后才量化 `kap`、profile 参数、chart、HB row、block 矩形、实际点、原 `i,k` 和历史模数参数。利用旧 `X0 > N^(1-kap0)/64` 与 `kap0<1` 将 scalar 阈值提前；没有点依赖的阈值。

只使用一个真实 `scalarProfile != 0` 点来支付物理尺度；不要求 aggregate 非零或整个矩形活跃。units、重复值、原短位置 carrier 和原索引全部保留。

固定 1106 coefficient appendix：251–270 行规定参数顺序；751–763 行给出 short mass、模数矩与 Brun divisor pairs 的组合；797–821 行列出 `coef:two-rough-error` 四项并支付幂次余量。完整手稿与供应者 commit/path/blob/SHA、声明和证明区间见 `SOURCE_REVIEW.json`。

## 采用路由与剩余边界

直接 imports 为 FixedScaleTransport、TwoLongMellinLogBudget、P4BOriginalTwoLongActualScales。后者只调用原数值 `fixed_margin`，不调用 P4 two-mother 终端或不适用的 factor16 门槛。

由于共享 FiniteGeometry 已拥有从 NoMediumPairRows 提取的原声明，未来采用本包时须选择既已登记的 `p1-singleton-two-long-dictionary/provider-postimages/P4BOriginalNoMediumPairRows.lean` 互补版本；不能同时编译未迁移原 provider。本轮没有新提取，也未修改任何旧 provider。

本包只支付主导幂次项。`M(U+V)Y`、`MY^2`、密度项 `MUV*epsilon_x`、实际 P2 row/Fourier/rough-restoration 的装配仍未在此完成。原 Mellin/FixedM/normalized source 链的已知可用性边界照旧；没有宣称完整可编译闭包。实际 short mass 两声明由独立 ShortMass owner 负责，此处不复制。

## 文件

- `P1OriginalSingletonTwoLongPowerPayment.lean`：7,826 字节，SHA256 `d3ebf151d4b3585d5b2d5d096e5fb6211b23a0fd8c828f2768209a067066f103`。
- `SOURCE_REVIEW.json`：精确来源、量词/合同检查和零 Lean 验收记录。
