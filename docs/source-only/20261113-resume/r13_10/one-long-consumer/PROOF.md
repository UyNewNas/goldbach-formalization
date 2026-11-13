# 原最终 singleton 的单长槽：实际 E5 consumer

本件只处理冻结基础包定义的 `physicalChannel` 和 `freeChannel`。两者都沿原 `oneLongAtlas`、原 `chartBank (2*N) 1`、原 `firstMedium = none` 与 `longBlocks.length = 1` 选源。原最终矩形的 medium、two-long、两个历史差以及 whole PP 不在结论中。以下是源码推导；本地未运行 Lean 或任何证明程序。

## 精确的有限和

令 r=2(j+1)，j=0,1,2。选择唯一长位置 a，短列 v 的坐标集是 `{i : Fin r // i ≠ a}`，而非不同短积的集合。记 m=∏vᵢ、U=lower(bₐ)，短系数是

`shortCoefficient z y a v = ∏ᵢ actual z y (rowRoles j i) (vᵢ)`。

它保留每一原 Möbius 的符号及同一个真实实数截断 y，也保留短位置的 rough mask 和原 log。相同数值位于不同位置、不同 v 有相同 m，均仍逐项出现。长 Möbius 在共同阈值后逐项为零；其余长角色只能是原 one 或 logarithm，有限证明没有任意长 alpha。

原完整乘积 cap 在每个短列上恰好给出

`U < n ≤ min(2U, floor(2N/m))`。

起点 L=U+1，宽度 Kᵥ=max(0,min(2U,floor(2N/m))−U)，包括空区间和闭右端点。冻结的 `sum_rectangle_capped_short_fibres` 和 `dyadic_fibre_exact` 直接提供这个重排。

`strict_rough_dictionary` 使用原 `smallPrimes z`，其成员是 prime p≤z。因此被保留的实际长 mask 仍是严格 z<p，包含 z 恰为素数时的删除。`actual_count_mean_dictionary` 逐项将原 residueKernel 写成

`actualCount q N m n − actualMean q m n`，

其中 count 是 m*n≡N mod q，mean 是 1_{gcd(m*n,q)=1}/φ(q)。这个恒等式不删非互素 m；两项在需要时一起自动为零。同一个完整模数系数 rho(q) 同乘 count 和 mean。

冻结的 `actual_long_profile` 把完整原 reciprocal group log、ambient、complete trim、psi 和所选长角色的可选 log 原样装入 Fᵥ(n/U)。于是 `longFibre_eq_actual_profileError` 得到原有限长和恰等于

`shortCoefficient(v) * Σq rho(q) profileError(L,Kᵥ,q,N,m,chartDivisor(smallPrimes z),Fᵥ,U)`。

这里是恒等式，E5/profileError 界不是输入。接着对同一个真实 m 用 Mset={m}、alpha=1、M=1、Rwidth=1 调用旧 `actual_chart_one_long_finite`。旧 theorem 的 literal B1/B2、factorial gap、primitiveCoprimeDensity_two_tau、intervalBudget 和固定阶模数矩证明全部复用。

## 真正的总宽与对数恢复

设 L_N=1+log(8N+8)。冻结的实际 B=6 C1 supplier 在 N、m、U、chart、位置和所有原参数前选定常数 C，给全实轴

`sup_x (‖Fᵥ(x)‖ + ‖Fᵥ′(x)‖) ≤ C L_N^73`。

新 consumer 只从这条已证供应器选择一次 `profileConstant`；没有 hAmp/hDer 或抽象 profile class 输入。任何活矩形有一个原几何非零点，故 ∏lower(bᵢ)≤2N。于是盒内任一短值 vᵢ≤2lower(bᵢ)≤4N。每个实际 short role 模至多 L_N；最多五个短位置，保守付 `‖shortCoefficient(v)‖≤L_N^5`。这也覆盖实际上只有一个 log 的更强结构。

短盒精确有 S=∏_{i≠a}lower(bᵢ) 条有序列。每条 Kᵥ≤U，而冻结的实际源支撑给

`Σᵥ Kᵥ ≤ S U ≤ 2N`。

先逐纤维有限 E5，再求和，旧 `physicalBudget_le_common_log` 在 J=0 给出实际一块的界

`2 C Rrho L_N^78 (1+log D)^4 [10 Y D S + 4 epsilon N]`。

只有第一项恢复 S；epsilon 项使用真实 ΣKᵥ≤2N。没有先逐纤维粗估 O(N) 后再乘 S，也没有假设总系数质量或总恢复预算。

唯一长位置来自整块的 filter 长度一。`unique_filter_index` 保留位置重数，故所有其他位置确实是原 short 阈值以下。R=2^cj≥1，短块数≤5，于是

`S ≤ (R^(3*zeta))^5 = R^(15*zeta) ≤ (4N)^(15*zeta)`。

最后一项来自原活 profile 的真实支撑：ambient 给 N^(1−kap)≤b≤2N，psi 给 R/2≤b≤2R，合为 N^(1−kap)/2≤R≤4N。

## 一个共同 N 阈值与原 rough alphabet

单母图的原 cutoff 是 `roughF(2^(6K+3) R)`，未改为包络本身。设 C_K=2^(6K+3)。由 kap<1，N^(1−kap)趋于无穷；上面的活图下界使全部原 cutoff 参数统一进入 roughF 的已证单调区域。再取 N≥4C_K，便有 C_K R≤4C_K N≤N²。旧 `roughF_mono` 和 `roughF_upper` 在同一个 N 给

`actual z ≤ canonicalEnvelope N = N^(2/(loglog N)^3)`。

同一活图下界还使 `(2R)^(1/3) < R^(1/3+zeta/4)` 一致成立。长块下端大于右侧，因而原 long Möbius 的真实截断为零。这条阈值在 cj、整块、长位置和短列之前构造，未作为新假设交给终端。

有限 E5 对任意 Brun 整数阶成立，因此统一选 j_N=floor((loglog N)²)，奇阶 order N=2j_N+1。这个选择只用于证明中的 Brun 上下多项式，不改任何目标行或实际 mask。取旧 canonicalEnvelope 为 support 的数值上界，实际 P 仍是 smallPrimes(actual z)；Z=max(1,floor(actual z))。旧 Mertens theorem 对所有 P⊆[1,N] 给一个共同 H=2 loglog N。故旧 `support_is_subpower` 与 `gap_is_superlog` 直接供应

`Y(N) = canonicalEnvelope(N)^(order N)`，

`epsilon(N) = (2 loglog N)^(order N)/(order N)!`。

对每个固定 δ>0 有 Y≤N^δ；对每个固定 B 和 eta>0 有 epsilon·log(N)^B≤eta，共同阈值均在实际图和短列之前。`selected_Brun_rates` 显式先选 B=A+100。也可固定 δ₁=1/10；对 0<zeta≤1/20000，`15*zeta + 599/1000 + δ₁ < 1`。

## 全图与两个原通道

设 d=log2(8N)，G=d+4。完整 chartBank 的 singleton 标签数≤G；其标签 cj 的 hbCap≤8N。旧 `blockWords_card` 逐位置给每阶块图数≤G⁶。三个原 HB 标量分别为 3、−3、1，模均≤3，所以全体原行的恢复费用≤9G⁷。

这不是以 N^eta 代替对数：`graphHeight_le_profileHeight` 从 2^d≤8N 及取 log 得到 G≤(4+1/log2)L_N。D=floor(N^(599/1000))，有 1≤D≤N^(599/1000)≤N，故 1+log D≤2L_N。乘回之后恰付 L_N^(73+5+4+7)=L_N^89。最后用明确的 L_N≤(2+log16)log N，保守提升到固定 log 次数 100。

将 4^(15*zeta)、profileConstant、graphConstant、Rrho 等固定常数收在 N 前。旧 `eventually_one_long_E5_budget` 对 theta=15*zeta+599/1000<1 直接支付

`C [N epsilon(N) + N^(15*zeta) Y(N) D] log(N)^100`。

长 support 只出现在具有严格幂余量的项中；epsilon 始终只乘 N 和固定 log 幂。所有 polylog 费用都按固定幂明确支付。

终端 `original_one_long_two_channels` 先固定 kap、omega、zeta、K≥2 和 A，再构造同一个 N₀。对所有 N≥N₀ 及满足原参数条件的 Params，physicalChannel 和 freeChannel 各自都≤N/log(N)^A。physical 用原 live 去零恒等式再返回原 P.S；free 用原 products(P) 上的整个模数记录和，Rrho=J0(omega)!，其中有序记录重数及真实小因子已经由冻结基础中的 fibre_card 和 freeRecord 界支付。它不是任意长 alpha，也没有新 rho licence。

整个证明仅闭合上述实际单长子和。中段其他分支及历史 duties 不由这个终端推出。四份基础源保持逐字冻结；新增源仍需独立源码审查和 GitHub 的编译、kernel、完整类型与公理验收，不能据此标绿。
