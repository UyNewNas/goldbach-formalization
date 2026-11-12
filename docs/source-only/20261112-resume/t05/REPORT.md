# 原乘积截断在最终矩形系数上的有符号费用

源码候选，未经 Lean 编译。本包新增两份源码、零条数值输入。11 月 10 日的两份光滑计数源码沿用原字节。T09 已独审其有限 RealB 上界、互素修正消零和统一光滑质量估计。11 月 12 日的两份新源码另行送审。

## 截断和计数端点

令 `W_s = smoothPhysicalPairOuterRamp b N (2N^(1−κ)) s`、`X_s = ∑ W_s`。原补篇 §2 的独立截断是 `η₀(t) = Real.smoothTransition (t−1)`，令 `V_s(u) = η₀(product(u)/N^(1−κ₀)) W_s(u)`。这两个源在原始有序素数对上取值，保留重复素数。计数使用 `κ=κ₀`。独立的截断等式允许二者分别固定。

- `P4BOriginalFiniteSignedTrim.difference_eq_trim` 把两个原始 `Part3.primeProductSignedError` 的带符号差经实数到复数的嵌入，精确还原为 §2 的 `P5Z.OriginalPrimeAllGroupHBDiscrepancy.trimReserve`。原计数项及 `1_(product,q)=1/φ(q)` 互素均值都使用同一个 q 和同一个系数。
- `P4BOriginalFiniteSignedTrim.eventually_signed_trim` 对任意固定 `0<κ₀<1`、自然数 A、`δ>0`，先给出 N 阈值，继而对所有合法外宽及同年 11 月最终高区／低区共同树的 `Q,ρ` 给出 `|PP(W_s)−PP(V_s)| ≤ δ N/log(N)^A`。它直接读取原物理端点已经供应的 `ρ(q)≠0 ⇒ q<N^(599/1000)`。原系数的单位界在源码中由 `P4AUpperTaggedBetaAttachment.rho_abs_le_one` 给出。
- `P4BOriginalFiniteTrimmedCount.eventually_original_trim_on_fine_rectangles` 用原 `data_physical_range` 解除上述范围前提。阈值仅依赖 `κ₀,A,δ`，先于全部政策参数。对每个原粗网格、`e≥0,ω>0,ℓ<1/1000`，一个正的细宽上限允许每一个满足该上限的已对齐矩形。接 T01/T02 已选择的矩形时可直接读取其严格范围，无须另选 β 或 k。
- `P4BOriginalFiniteTrimmedCount.exists_same_coefficient_trimmed_count` 给出预选的 `s₀,N₀`，对所有 `0<s≤s₀` 和 `N≥N₀` 偶数，在同一物理系数上同时给出 `X_s≥0`、`|X_s/(N/log N)−log(1/b)|<η`，及下式。端点和截断各在 `η/2` 的上限内，最后只出现一项 `ηH_N`。

```text
RealB(b,N) ≤ X_s · physicalDensitySum(Q,ρ)
             + Part3.primeProductSignedError 2 N N Q ρ V_s
             + η · singularNormalization(N).
```

这里的 `Q = moduli N (N^ω)`，`ρ = P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a ω N τ (N^(νβ))`，`ω=νβ²`，`τ=alignedWidth (jointIndex (bank m) (data e q a).m) k`。主项仍乘原来已由四个实际边界估计的质量 `X_s`，所作替换限定在有符号差的绝对费用内。原编译预留和密度预留在本步骤没有新增支出。

## 算术证明

取 `Y = ceil(2N^(1−κ₀))`。原下截断引理给出 `Y<N` 且 `Y≤3N^(1−κ₀)`，故删去部分不含乘积恰等于 N 的项。原 S19 的独立有序词上界给出质量至多 `Y·B N^ε`。若词的乘积为 `x≤Y`，同余计数只收 `q|(N−x)` 的真实模数。除数次幂上界给出 `C N^ε`。互素均值先保持原来的 `ρ(q)/φ(q)`，在取绝对上界时才剔除零系数和实数除法下的零模数项，再用全 `1≤q≤N` 的倒欧拉函数对数上界。合计每词至多 `D N^ε`，两个常数都早于 N 与矩形。取 `ε=κ₀/4` 得 `O(N^(1−κ₀/2))`，进而得到任意固定对数精度。只在实际截断差中作此三角估计。

## 已有来源与余项

原稿固定在 `chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`。补篇 §1 定义原 PP 的绝对有符号估计，§2 给出上述 η 截断、独立 dyadic 分组、Heath–Brown 恒等式及真素数幂更正。原 S19 已有词重数、乘积截断因子和通用行核字典。它的最终费用专用于旧 `attachedUpperCoefficient`。本包保留上述通用引理，并把实际矩形的幅值和支撑代入同余／均值账。Gamma 完整乘积截断的 `rootLabels` 另带实际旧素数对、颜色词和商，本文未将其等同于本秩二载体。

`P4BOriginalFiniteTrimmedCount.eventually_trimmed_exact_atlas` 将真实的 `PP(V_s)` 精确写成所有原 dyadic 标签的 `mediumAtlas + noMediumAtlas − properPowerReserve` 之和。它在原词上采用实际两组 HB 变换，直接使用已有的逐标签 `roughPrimeReserve=0`。每项具有相同 Q、ρ、目标 N、原 ψ 标签与精确互素均值。这个恒等式在未经估计的 `properPowerReserve` 上保留原负号。

- P3 源 `8d15f31906ae8a108336bedb3d0c4b692812a4cb`、交接 `a29bd6b4cba6d1b7e8cd48165f3a0f76f040082b` 给出已分配原分组导数的乘积、分配和的真实求导步骤，尚待 `Fin.cons` 全阶重索引。它涉及 §4 的导数与 Fourier 插入。本包没有重做这些导数。已有各秩二固定外宽导数和反演构造可在后续实际模数与完整系数分解中复用。
- T02 的 `P4AOriginalFiniteFallbackFineJoint.joint` 给出真实的共同 β、对齐序号 k、任意正 `fineTolerance β`、两个全盒预算和同一 ρ 的严格模数范围。这些预算保留到 N 之后。T01 当前的 `exists_cofinal_same_coefficient_density_and_count` 消去旧早期 `lowerEarlyDefect`，把密度上界写成 `(currentK−densityReserve−exactSlack+η)·singularSeries(N)/log(N)−actualCorrection`。现有 T01 普通存在选择与 T02 更细的存在选择仍须在真实内层同一次选参中合并，不能交换两个已得到的存在见证。
- 剩余精确目标是在这个最终 ρ 和原测试 `V_s` 上，对每个固定 A 给出 `|PP(V_s)|=O_A(N/log^A N)`。该式仍要求真实经典低秩卷积分布、中段与一长/两长分支、全盒分组及还原标量和，以及实际 `properPowerReserve` 的带符号总和费用。均匀的真 PRIME 轮廓 BV 端点没有覆盖整个两素数卷积。旧 first-exit rho 下的 Fourier 尾或真幂碰撞总费用也需要同系数转接。完整 K/RealB 端点仍需这些供应及全链审查。

原低乘积截断是稿内可补的形式连接。余下的中段分析等式和算术估计需要实质性供应。最新分组导数与现有 T02 参数资料均未给出该带符号总误差的上界。本轮只作静态源和原始对象字节核对。
