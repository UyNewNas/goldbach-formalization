# 固定 singleton rectangle 的常数运输

**SOURCE ONLY：未 elaboration、未编译、未核验 kernel，formal credit = 0。** 本目录只增加一个新候选 owner 与来源记录，不改变旧源、canonical、runner 或任何验收身份。

候选 `P1OriginalSingletonFixedScaleTransport.lean` 保留上一桥的固定完整尺度

\[
X_0=\prod_a\operatorname{lower}(b_a)=MUV.
\]

原 `i,k`、原短位 carrier、unit、重复整数和实际 singleton roughness cutoff 均不改变。它解决的是已明确发现的常数差：真实几何给出 `R ≤ 128*X0`，旧 P4 pair helper 的 `X ≤ 16*x` 不能直接用于这里。

## 三个声明

| 声明 | 本轮连接 |
| --- | --- |
| `scalarProfile_chart_window` | 从同一实际 `scalarProfile ≠ 0` 取出原 `psi ≠ 0`，交给既有 `profile_nonzero_support`，取得 `R/2 ≤ n ≤ 2R`。未重证原 smooth-support 定理。 |
| `eventually_fixed_scalar_transport` | 在固定 `K,eps,zeta` 后，显式支付常数 128 的短积与 cutoff 运输；它保留所需几何前提，供下一实际声明逐项证明。 |
| `eventually_actual_singleton_fixed_scale_transport` | 调用上一 FixedRectangle 桥，从真实 rectangle 活点与原 Dictionary 的 short-position 输出，支付标量 helper 的全部前提。阈值先于 chart、row、tuple 和所选位置。 |

最终实际声明的输入只有上一桥已经使用的 `j ∈ range 3`、`i ≠ k`、原 rectangle membership、同一完整乘积的 `scalarProfile ≠ 0`，以及 Dictionary 原样提供的

```lean
∀ a : ShortPositions i k,
  (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]
```

它没有要求目标短积界、目标 Brun 支撑界、aggregate 非零或整 rectangle 活跃。

### 短积与单个 short block

原 `short_card` 和 `j ∈ range 3` 给出至多四个短位。因每位原 lower 小于 `R^(3*zeta)`，有限乘积直接给出

\[
M\le R^{12\zeta}.
\]

由真 `R ≤ 128X0`，

\[
M\le128^{12\zeta}X_0^{12\zeta}.
\]

取固定参数后的大阈值，使 `128^(12*zeta) ≤ X0^(28*zeta)`，遂得原 two-long 预算所需的

\[
M\le X_0^{40\zeta}.
\]

另一个独立阈值使 `2*128^(3*zeta) ≤ X0^(1-3*zeta)`；这里 `0<zeta≤1/400` 确保正余量。因此每个原 short block 都满足 `2*lower ≤ X0`。两个常数分别由既有 `tendsto_rpow_atTop` 支付，没有把 128 改成 16，也没有重选 `zeta`。

### 原 cutoff 与同一 growing Brun order

singleton 的原定义精确展开为

\[
Z=\operatorname{roughF}(v),\qquad
v=2^{6K+2}(2R).
\]

活点的原 chart 窗口与全 rectangle 窗口给出 `R ≤ 128X0`、`X0 ≤ 2R`。于是

\[
X_0\le v\le (256\cdot2^{6K+2})X_0.
\]

固定 `K` 后取 `X0 ≥ 256*2^(6*K+2)`，即可取得 `v ≤ X0²`。原 canonical `roughF_mono`、`roughF_upper` 已允许任意 `v`，因此直接得到

\[
\operatorname{roughZ}(X_0)\le Z\le\operatorname{roughZ}(X_0)^2.
\]

随后仅调用既有 `ActualHBRoughBrunRates.eventually_support_le_power (eps/2)`。原定义仍为

```lean
halfOrder X0 = Nat.floor ((Real.log (Real.log X0))^2)
nextOrder X0 = 2*halfOrder X0+1
```

对上述平方比较取同一整数次幂，得 `1 ≤ Z` 与

\[
Z^{2\operatorname{halfOrder}(X_0)+1}\le X_0^{\mathrm{eps}}.
\]

这只是原 cutoff 和原 growing order 的支撑上界。未更改 prime alphabet，未重证 factorial density、Mertens 或 P2，未声称 epsilon-density、exact-mean 误差或 rough E3 已支付。

## 阈值次序

`K` 和正 `eps` 固定在 `∀ᶠ N` **之前**；`N` 阈值可以依赖 `K`。前一纯几何桥对 `K` 一致，并不意味着本 roughness 结论对所有 `K` 使用一个阈值。

实际接口继续使用 `kappa>0`、`kappa≤zeta/10000`、`zeta≤1/400` 和 `kap0<kappa/(4(1+kappa))`。原 `manuscript_kappaZero_lt_quarter` 给出 `kap0<1`；固定尺度下界 `N^(1-kap0)/64<X0` 把标量阈值统一运输到物理 `N`，之后才量化 `kap,B,cj,j,bs,ns,i,k`。`m,q,rho,xi` 不参与尺度或阈值。

最终调用可先按精度需求固定 `B`，再固定所需 `K`，最后取本结论允许依赖这些已选参数的 `N` 阈值。这里的局部结论本身对原 profile 参数 `B` 一致；它没有证明外层应如何选择 `B` 或 `K`，也不把 cutoff 中的 `K`、稿中的 `K_mom` 和 `halfOrder X0` 混为一物。

固定 1106 coefficient appendix 的 251–270 行先固定有限族与矩阶再选小参数；514–519 行在 HB 卷积之前固定 common roughness cutoff；535–548 行保留完整乘积尺度；751–763 行使用 `x≈MUV`；811–821 行用严格幂余量支付固定常数。后续 endpoint 精度的 `B` 按 825–850 行在目标 logarithmic accuracy 之后选择。源码没有将最后一个精度选择提前到本地几何假设中。

## 来源与采用路由

新 owner 仅 import：

```lean
ImbalancedChen.P1OriginalSingletonFixedRectangleScale
ImbalancedChen.P5ActualHBRoughBrunRates
```

前者是上一轮已冻结的候选；采用它必须继续遵守其 **PhysicalSupport + PhysicalLevel 唯一互补 postimage** 的原子路由。LogNormalization 与 LongComplement 不变。后者的原 `eventually_support_le_power` statement/proof 可直接读取，使用实数 `x`、原 `halfOrder`、原 `roughZ` 和原 `supportSize`。本轮只使用该旧证明，不把其余 rate 声明或旧 36 条 rough 提取记录视为验收回执。

完整 source pins、statement/proof 字节区间、固定手稿区间、Mathlib API 定位和独立静态审查结论见 `SOURCE_REVIEW.json`。没有新增 source migration 或重复声明 owner。

独立静态审查提出的三处表达风险已作局部修正：实际 dyadic `R` 使用全限定名；反向 `rpow_natCast` 明确只转换目标平方；`supportSize` 的非负性显式投影已有 supplier 结论。它们保持同一数学合同，不是一次 Lean 失败后的验收修复。初稿与修正稿的哈希、精确可逆 diff 保存在 `STATIC_REVIEW_CHANGES.json`。

## 尚未完成

本轮没有读取或重建已登记的七个 Fourier 缺源或 FixedM 源，没有改写 `sharp_fibre_identity`、P2 或 36 条旧 rough 声明。继承的源闭包边界仍在，新增 Rates 链也只按已读来源记录，不声明完整传递闭包或已接受对象。

固定 `X0` 的 elementary 常数运输完成了源码候选。实际 short-sequence 加权求和、rough-to-upper 精确均值装配、sharp endpoint strips、Fourier 重构和外层 Atlas 预算仍需各自的原供应与证明；它们不是本模块的假设或结论。
