# n07 后继 — 原 two-long 的实际平方自由 P2 与展开核心

SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED。三个新独立 Lean 文件，旧 AUDIT 与全部 freeze 未改。未运行 Lean/Lake/LSP/kernel 或项目 helper/fixture/stage/setup/guard；未写 Git/GitHub、运行 CI、查询额度或下载 artifact。

**本轮完成的是一份真实原 two-long 展开核心的证明源码候选；它支付原稿 (E4) 的 `M*y²*D^(3/2)` 子项，不是完整 no-medium、hUniformPP 或 hUpper。** 它没有新添 `hWeil`、`hP2`、`hE4`、`hModes` 或 `hUniformPP` 前提。仍有实际尺度与支撑的几何条件，以及完整 rough/端点/母积分恢复义务。未经 elaboration，这些源码不记形式通过。

## 1. 复用边界与本轮实际新增

已读原 `distribution-prime-product-completion-20261010.txt` 250–338、340–399。两长核的原式为

`U V / q² * sum_(j,k) fhat(j U/q) ghat(k V/q) [S(a*m⁻¹*j,k;q) − c_q(j)c_q(k)/phi(q)]`。

这里的 `q` 是进行原同余计数的物理模数。经过 Brun `d1,d2` 代换，它仍然是 `q`，短乘积改为 `m*d1*d2`，尺度改为 `U/d1,V/d2`。因此，本轮从真实 P4 Q 供应的平方自由性适用。本文不把它转用于 medium 里可能出现的 `c²*d` 或其它变换模数。

现成 `Part3TwoLongHBMellinBrunProfiles` 已给实际 Mellin/log 轮廓的 P2 与有限求和，但接受全局 `CompositeWeilInput`。旧 `Part3TwoLongActualLowerCorePayment` 只支付另一条 `lowerQ/lowerRho`，并以短坐标≤6作预算。直接调用这两处不足以给当前 P4 两母付款。

本轮新增：

1. `P4BOriginalSquarefreeWeil.lean`：从已存在素数 `prime_physical_sqrt` 与原相位的 `kloosterman_coprime_crt` 证明原生产 Kloosterman 的平方自由 gcd 界。没有素数幂猜测或全 `CompositeWeilInput`。
2. `P4BOriginalSquarefreeP2.lean`：把旧 centered kernel → absolutely convergent P1 modes → natural fixed-m P2 → actual MellinBrun P2 的证明块局部化到当前平方自由 q。所有成本常数与右端保留；无需外加完整合数 Weil 假设。
3. `P4BOriginalTwoLongExpandedCore.lean`：在 `S⊆P4BOriginalFiniteSmoothCount.Q omega N` 上使用真正 `coefficient m r n e q a omega k N L`，证明实际 P2 模数矩、Brun 双除子和、原 signed `shortSequence` 的展开核心及统一任意对数精度付款。

没有重写原双槽 pushforward、Brun 除子换元或 retained-row 有限字典。原 `Part3TwoLongRetainedRowReindex.rectangle_signed_pushforward`、`Part3TwoLongLiteralBrunSubstitution.pair_divisor_substitution` 可后续原样复用；它们的旧 lower-rho 外层专用包装器不是当前 rho 的同一性证明。

## 2. 平方自由 Weil 的对象与边界

新界对每个 `Squarefree q` 与任意整数 m,n 给

`norm(kloosterman q m n) ≤ tau(q) * sqrt(q) * sqrt(gcd(gcd(|m|,|n|),q))`。

* p=2 由同一个 prime supplier 处理，无奇素数限制。
* 一个零频时使用素数换位与现成非零 mark 界；双零/双可除时保留 gcd=p，并用原平凡 bound，不删零频。
* q=1 保留；下游 natural core 仍有原 `naturalCore_q1` 精确零结论。
* CRT 使用原 `gcdB/gcdA` 的两个局部单位 twist。现成 `primitive_center_gcd` 连用两次说明双频 gcd 不变；并不是只控制首频 gcd 的 fixed-mark majorant。
* 平方自由性只排除 prime-power induction 的指数≥2分支；没有声称一般素数幂 Weil 界已证明。
* `actual_Q_weil` 与 `actual_modulus_class` 从 `P4AUpperTaggedBetaAttachment.support_squarefree` 对原 Q 的成员直接取得平方自由性。当前实际 P4 消费者不要求调用者另供 `Squarefree q`。

ROOT 指定的 `905a...` / `763f...` 是 `P0RamanujanGeneralGcdIdentity` 与 `P0RamanujanMoebiusExpansion`。它们是实际 Ramanujan/互素均值链的既有供给，已记录准确选本，不被冒称 Kloosterman Weil 界。其原 phase/c² 约定不改。

## 3. P2 局部化的明确类型变化

旧 theorem 的解析前提是 `hWeil : CompositeWeilInput`，量化所有正 q 与所有整数双频；随后引入当前 q。

新同名局部 namespace theorem 先引入当前隐式 q，再接受结构条件 `hsq : Squarefree q`，其算术上界由新 `squarefree_weil` 在证明内部产生。`naturalCore_P2`、`mellinBrunCore_internalP2` 的 q 也改为此隐式当前模数。原 q-positive、primitive target、U,V positive、真实 Schwartz 支撑及 profile/频率条件保留。

`naturalCore_P2_refined` 仍先检查真实短乘积 `m` 与 q 是否互素：非互素时原 AP count 与精确 coprime mean 同为零；互素时才取原 `a*inverseResidue(q,m)` 的 primitive center。新证明没有假设全部 HB 短乘积互素，也没有排除重复 HB 素数。

`UV/q²` 与两个频率尺度 `q/U,q/V` 仍作原精确抵消。两轴通过旧 `centeredKernel_left_axis/right_axis` 消失；原 Ramanujan 均值、绝对收敛与 GCD divisor envelope 复用。因此不改变原 1/phi(q) 或 Fourier 归一化。

## 4. 实际 P4 展开核心的已付接口

`brunCore` 使用原 Q 的子集 S、实际 signed rho、原 `brunPairCoefficient`，并保留所有正 Brun 双除子。`rowCore` 再按原 `shortSupport/shortSequence` 汇总实际 HB ordered short tuples；原符号、Mobius 截断、log slots、Mellin phases 与重复位置均在 `shortSequence` 内。

`actual_modulus_moment` 只把实际非零 rho 的模数放入 `[1,D]`；inactive 矩形模数即便超出 D 也按其真零贡献处理。它调用既有 **通用** `squarefree_p2_modulus_moment`，没有拿 U10/U11 的 jointRho 代替 P4 rho。结果保留 `((D sqrt D+1)*(4(1+log max(1,D)))^16)`。

`actual_Brun_P2` 对每个原 v∈S 从实际 Q 取得 v>0、(N,v)=1、Squarefree v 与 |rho(v)|≤1。然后在相同 v、N、原 short*d1*d2、两长原尺度上调用新 P2。只在完整 AP-minus-exact-mean 形成以后使用三角不等式。绝对 `shortSequence` 质量属于原补篇 252–253、289–293 的 P2 error bound，**没有把 medium beta 的 signed mean 改成绝对均值**。

`eventually_actual_upper_core_paid` 的前置固定参数为 B,K,A,c,zeta,theta,epsilon，之后取得一个 x 阈值，之后才给实际政策、目标 N、子集 S、Brun order、HB roles、cutoff、U,V和频率。所需几何条件明确为

* S⊆Q、实际非零 rho 的 v≤D，且 D≤x^theta；
* 原短块乘积尺度 M≤x^(40 zeta)、Brun 支撑 y=Z^(2j+1)≤x^epsilon；
* 原短整数块上端≤x；1≤U,V≤c x；两长频率≤(log x)^K；
* 原严格余量 `40 zeta+2 epsilon+3 theta/2<1`。

它给原定义的 `norm(rowCore)≤x/(log x)^A`。没有把待证误差上界列为前提。

两组 order-three HB 的总原坐标至多12。本轮使用短坐标≤12的安全固定对数预算，覆盖实际去掉两长位置后的≤10坐标；没有沿用旧单母≤6界。原固定16次模数矩加12次角色预算为28次 log，固定常数再吸收一次，得到所调用的 E4 monomial exponent 29。原母/owner恢复若需 log^54，应先对本接口请求 A+54 再按真实 x/N 比较汇总；这里尚未把该外层恢复写成已付 no-medium。

`S=wholeHigh ...` 可用原定义的 `Finset.sdiff_subset` 进入本接口，保留同一个完整 final rho。所有 squarefree 结论来自这个原 Q，未借碰撞后改动模数的平方自由性。

## 5. 尚未闭合与最小下一命题

本轮不声称整个 no-medium branch 完成。下一处实质连接是对实际两母 long profiles 的 rough→upper/gap 比较支付原 (E1)/(E3) 的**精确互素均值**，并将其接回同一真实 row：

`sum_{(n,q)=1} F(n/U) U_Z(n)` 与 `U*phi(q)/q*(integral F)*A_q` 之差，及对应 `G_Z/g_q` 之差，需由实际非负 smooth majorant、原 Brun 支撑与 N1(F) 给 `O(y*tau(q)*N1(F))`；之后逐 q 仍保持原 mean 的 `1/phi(q)`，使用真实 rho 的 fixed-order reciprocal moments。原 E3 的 `count+mean = signed discrepancy + 2*mean` 不能丢掉第二份 mean。

再后是原 sharp individual intervals 的两条真实端点 strip、实际 two-long occurrence 选择（每母至少一长槽，one/log role）、原 normalized mother amplitude 与所有 scalar/碰撞/截频恢复。原稿 298–338 与340–369已有具体路线；现成 E4 assembly 仍接受实际 E1B2/几何字典前提，不能把那些前提当已支付。

这是当前源级未实现/未接合的原数学供给，不是原稿反例。此次没有发现必须引入新的外部估计；尤其 q 为原平方自由物理模数时，素数 Weil＋CRT 足够支付此次 P2 子项。若后续证明实际出现 c²*d，则本候选不适用，须另供该变换模数的真实估计。

## 6. 依赖与验收

依赖包括已存在但未完整编译验收的源。prime supplier 来自 `Part3FixedMarkPrimeWeilBridge` 和 LeanPool `PrimeKloosterman.prime_bound` 的真实证明体；ROOT 的34模块外部闭包尚未全 kernel 通过，最近 FormalAlgebra API 修订不能被本文提前视为验收。原 P4 FineDensity 与 two-long 依赖也保持原 scope。

`SOURCE_RECEIPT.json` 给三个候选、直接数学供应、原selected Ramanujan两源、原文的实际字节哈希；`LOCALIZATION.json` 列旧 proof-block 源与新参数变化；`STATIC_CHECK.json` 仅报告源码扫描/JSON/hash，不是 Lean elaboration。下游应先独立审查本轮平方自由 CRT proof 与实际 q 身份，再由 ROOT 安排精确源选择及远端验证。
