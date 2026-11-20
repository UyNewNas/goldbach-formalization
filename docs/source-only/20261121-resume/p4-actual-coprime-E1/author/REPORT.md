# 原 no-medium E1：真实光滑互素均值与同 Q/rho 接线

SOURCE ONLY / UNCOMPILED / PENDING INDEPENDENT REVIEW。本目录四份新 Lean 候选；source65/source66 的源码、作者 freeze 与旧 AUDIT 不变。没有运行 Lean/Lake/LSP/kernel、项目 helper/fixture/stage/setup/guard、Git/GitHub 写入、CI、artifact 下载、额度查询或子派发。

**这次新增的算术是实际 smooth long 的 fixed-divisor E1 供应。** 原积分、Brun polynomial、q-deleted reciprocal density、短积非单位分支与同一 final rho 均保留。误差价格使用已经形式化的实际 N2 轮廓预算；没有宣称一般 C1 轮廓的最优 N1 版本。E3 twice-mean、sharp endpoints、母积分与 hUpper 不在本包。

## 1. 查重及真正缺少的供应

已核原补篇 `distribution-prime-product-completion-20261010.txt` 265–290 的 P1/P2、298–306 的 E1、308–338 的 E3/E4。E1 要求真实互素 n-sum，不允许把它换成 unrestricted Euler mean。

现成 `P5OriginalPrimitiveCoprimeDensity` 已给有限 Möbius count、原 totient 密度与所有 half-open endpoints 的误差。`P5OriginalOneLongDivisorIntervals` 保留插入除子及非单位 `(m*d,q)>1` 的零均值；`P5OriginalOneLongSmoothAbel` 给原差额的有限 Abel 运输。原 Brun 字母表、B1/B2、正支持与 factorial tail 也已有证明体。本包不重证这些组合或尾界。

沿旧 import 找回了未安装在当前普通源码树的历史 Phase7 冻结文件：

`goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-TwoLong-Phase7/frozen/40b7f83a3de4042038a412eeef71a366c07dedbeeb7e9230ec08bb0c28b2bbd2/Part3BrunExactCoprimeE1Attachment.lean`。

其 `literalE1_from_progression` 的 `hprogression` 正是尚未供应的逐除子光滑互素均值估计。因此不能把这个条件包装器记作现成实际 E1。该文件只作查重证据，本包不依赖其未支付的 hprogression。`P2SameQSeedCoprimeMean` 是 prime receiver 的精确分解，也不能替代这里的长整数光滑均值。

当前可直接复用的解析原件是 `TwoLongActualDoublePeriodization.affine_periodization_poisson`、原 support bijection、`TwoLongN2FourierDecay.norm_fourier_le_N2` 及 `poissonNonzeroDecay_summable_tsum_le`。从它们可完整证明实际 C-infinity compact long family 所需的 E1，而不用引入新解析黑盒。

## 2. 四个新模块

| 模块 | 已写候选供给 |
|---|---|
| `P4BOriginalCoprimeSmoothE1` | 原 affine Poisson 的真实零频积分与非零频误差；所有 positive lattice scales；自然数载体；Möbius 后真实 phi(q)/q coprime mean；任意 short/inserted divisor 的非单位分支 |
| `P4BOriginalBrunCoprimeE1` | 当前 `brunPolynomial` upper/gap 的完整有限 E1；原 compatible B2；真实 Mellin/log profile 的无 hMeanGap 输入误差 |
| `P4BOriginalSameRhoCoprimeE1` | 两长 exact mean 的原 1/phi(q) 因式分解及 UV*phi(q)/q² 主项；原 Q/rho 的 fixed reciprocal moment 与 normalized signed E1 error；gcd(N,q) 非单位模数从 actual support 排除 |
| `P4BOriginalActualChartCoprimeE1` | actual beforeHB Z、halfOrder(x)、retained H(N,A0) cube 与原 .599→local D 的统一 N 阈值；真实 Z 字母表的 B2 factorial tail；同 rho 的实际 profile mean-error 终端 |

最下游终端为 `P4BOriginalActualChartCoprimeE1.eventually_live_same_rho_E1`。

## 3. 主项、误差价与 N1/N2 的明确界限

令 I(F)=原真实积分 `∫x,F(x)`，令

`E(F)=2*fourierDecayConstant*N2(F)`，其中 `N2(F)=∫|F|+∫|F''|` 是已有定义。

新 `poisson_E1` 保留原 `(U/D) • Fourier(F)(0)`，证明其恰为 `(U/D) • I(F)`。全部非零整数频率保留原 Fourier 相位；借原两侧 telescoping decay 得误差≤E(F)，对每个 U,D>0、所有平移 b 一致。无需 D≤U，也没有删掉小尺度或零频。

自然载体仍是 `wideWindow U`，正支撑 `[1/2,5/2]` 的既有自然数/整数 lattice bijection 保证没有漏掉端点。Möbius 展开后得到

`|| sum_(n,q)=1 F(n/U) − U*(phi(q)/q)*I(F) || ≤ E(F)*tau(q)`。

对实际插入除子 d，原换元 n=d*u 给 `F(u/(U/d))`，但 F 本身不改。在原 Mellin/log profile 中仍是 log U，故保留 log(d*u)，不是误改为 log u。若 `(m*d,q)>1`，真实均值和主项同时精确为零；若为单位，应用同一 F、尺度 U/d 的上述估计。

由此，原 Brun bank `S_Z=brunSupport Z (2j+1)` 的 upper/gap coefficient b_d 给

`A_(q,m)=sum_(d in S_Z,(m*d,q)=1) b_d/d`，

`|| mean(F,U,Z,j,gap,q,m) − U*(phi(q)/q)*I(F)*A_(q,m) ||`

`≤ E(F)*tau(q)*Z^(2j+1)`。

左端是真实原 n-sum，含原 upper/gap polynomial 和精确 coprimality。没有给 lower Brun polynomial 假设正性，也没有认为 rough projector 已等于 upper polynomial。

本包是实际 C-infinity family 的 **N2-priced E1**，不是原纸面 N1-optimal 通用结论。轮廓不变；现成 `profile_N2_cube` 给明确价格

`2*C_F*profileConstant*logSize(U)*(1+H)^2/delta²`。

取 delta=log(x)^(-B)、原 retained frequency H 为固定 log 幂后，额外支出仍只是预先固定的 log 幂。它可以放在已经具正 power reserve 的 E1 remainder 中。本包完整陈述并证明这个价格，没有用 N1 名字掩盖 N2，也没有在未证明的最优 primitive 上占位。

## 4. 非单位、重复坐标与归一化

* generic E1 对每个 q>0 成立，无 squarefree、prime 或与 N 互素假设。q=1 有显式 `modulus_one_mean`；q=2 在同一正模数定理中，未加 oddness。
* 短积 m 任意，包括0与含重复 HB 因子的积。`divisorMean_reindex` 明确 `(m*d,q)` 的两个分支；`mean_nonunit` 给 `(m,q)>1` 时原 mean 和 main 同零。q=1 时 m=0 仍按其真实单位判定处理。
* E1 不含 AP 目标 N，所以不能从 E1 宣称非 primitive target 的 AP count 为零。实际 P4 的 target-coprime 性另由原 `support_coprime_target` 证明；`nonprimitive_target_modulus_absent` 显式给 gcd(N,v)>1 时 v 不在原 Q，未把“所有模数都互素”作为假设。
* 所有除子代换的模数仍为原 q。d 只进入 m*d 和 U/d；没有改成 q*d、q*d1*d2 或其它变换模数。
* 两长均值保留 `(1/phi(q))*sum_u sum_v`。`pairMean_factor` 按真实 `(short,q)` 分支分解；`pairMain_exact` 证明主项系数是 `U*V*phi(q)/q²`，不是 UV/q²，也不是带两个 1/phi(q) 的新归一化。这里对应原双 Poisson 中的 UV/q² 与其精确 coprime mean。
* `pairMean_E1_remainder` 只给恒等展开，保留两项一次误差与误差乘积。它没有删除 E3 必需的第二份 mean。

P4 外层是原 `P4BOriginalTwoLongExpandedCore.rho` 的复数嵌入；原有限 Q、目标 N 和系数在每个 summand 不变。`signedError` 在完整 mean−main 成形后才取范数。它不是把 signed rho 或 HB beta 的原均值改成绝对均值。

## 5. 当前 actual Z、B2 与统一阈值

`gap_density_B2` 直接调用现成 `actual_B2`，使用同一个 `smallPrimes Z` 与原 halfOrder，不重建 subset/cardinality 或 factorial 证明。

为避免把 Z 换成较小 roughZ(x)，新 `eventually_gap_density` 使用已有 `eventually_real_chart_harmonic`：它对任意有限 prime alphabet P、所有 p≤x 统一。因此对真实 Z≤x 的 P=`smallPrimes Z`，原 harmonic≤2 loglog x；再用已有真实 `nextOrder_bounds` 和 scalar `factorial_gap_le_exp`，得原 q-deleted、含 nonunit short gate 的 density 对所有 q/short 同时满足

`||density Z (halfOrder x) true q short||≤exp(-(loglog x)²)`。

actual chart 仍取

`Z=beforeHBCutoff K [cj,ck]=roughF(2^(6K+4)*X)`，`X=R cj*R ck`。

source66 的 `eventually_chart_brun` 供应同一 Z 的 `1≤Z`、`y=Z^(2*halfOrder x+1)≤x^(1/16000)`，从中推出 Z≤x；没有为 q、精度或频率另选 alphabet。原 `eventually_live_large` 将固定 x 阈值送到共同 N 阈值；原 `eventually_live_level` 将同一 coefficient 的 .599 support 送到 D=`floor(x^(1199/2000))`；原 `eventually_local_twists` 给 retained `H(N,A0)` cube 的实际单坐标频率。

最终同 rho 终端给归一化真实 mean error

`|| sum_(v in S) rho(v) * (mean_v-main_v)/phi(v) ||`

`≤ profilePrice(delta,U,freq) * x^(1/16000) * [4(1+log(max(1,D)))]^16`。

fixed reciprocal moment 用原 actual Q 的 squarefree/positive/support/|rho|≤1 供应；inactive rho 在 D 外只按真零贡献处理。K、B、A0、zeta/kappa/kap0 及所有 moment/precision 先固定，再取 N 阈值，之后才给动态 chart、row、mode、short 与任意同一 final policy 参数。这个统一界没有 existentially 重新挑选 rho；预先固定的 family 可直接实例化。

声明对 policy 参数给出更强的统一性；实际应用先固定原 family，再取阈值。N 之后只有全称实例化，没有存在性换系数。

## 6. 剩余边界与验收

已付候选范围仅为以上 E1 原 smooth/Brun mean 算术及 actual same-Q/rho 接口。粗糙 projector 与 upper polynomial 的比较仍需 E3；twice-mean、两个 sharp individual endpoints、原母 Fourier 积分、log54 全恢复及 H_N/hUpper 仍保留。原两母 repeated-coordinate 字典继续使用 source66，不重复也不把它换成 singleton。

未发现这里需要新的外部估计或原稿反例。缺步原先是 generic actual smooth primitive 的形式供应与量词接线；现有 Poisson/N2/Möbius 源足以写出上面的 actual-family 版本。精确 N1 泛型最优版本未做，不作为本包依赖。

`SOURCE_RECEIPT.json` 记录新源、现成数学源及旧冻结边界；`STATIC_CHECK.json` 只记录 source/JSON/hash/词法检查；`FREEZE.json` 是作者封存。新源尚无独立数学 AL、elaboration、传递公理或 kernel 验收，不能据此新增蓝/绿或完成整个 P4。
