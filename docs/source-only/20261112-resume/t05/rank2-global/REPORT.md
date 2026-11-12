# 全部原双素数标签在剩余粗秩二模数上的付款

九份 Lean 源已冻结。结论是源级候选。未运行 Lean、Lake、LSP、guard、CI 或数值证明。新增数值输入为零。所选数据和原稿版本见 `REGISTRY.json`。

## 同一物理系数上的三个结论

Q 与 c 由已冻结的 `P4BOriginalFiniteSmoothCount.Q/coefficient` 给出。令 S 为 `remaining omega N ∩ activeLow ... tau ell`，其中 tau 是原有限高区回退、完整有序第三层及新旧第五层数据的同一 k 对齐宽度。物理参数取 omega = nu·beta²、ell = nu·beta。设 W 为真实四门光滑权乘额外整乘积截断 η。D(U) 表示 U 上两个原标记素数的完整同余计数减精确互素均值。H(U) 是原 `chartBank N 2` 全部 js 上的 `mediumAtlas + noMediumAtlas` 带原符号总和。

| 源终端 | 在所有充分大 N 上的结论 |
| --- | --- |
| `P4BOriginalRankTwoGlobalPayment.eventually_original_prime_rank_two` | `abs(D(S)) ≤ δ N / log(N)^A` |
| `P4BOriginalRankTwoGlobalPayment.eventually_original_atlases_rank_two` | `norm(H(S)) ≤ δ N / log(N)^A` |
| `P4BOriginalRankTwoHigherRemainder.eventually_only_higher_ranks` | `norm(D(Q) − H(remaining ∖ S)) ≤ δ N / log(N)^A` |

原素数终端先给任意自然数 A、δ>0 选择 N 阈值，再取任意 b>0、κ>0、合法 s、任意实数 κ₀、任意实际政策与 ell<1/1000。合法 s 满足 `0<s, 2s≤baseline b κ−19/96`，包括随 N 任意趋零的选择。第一式直接在 S 收费。后两式对固定原 K_HB≥2、b、κ 先取阈值，再给全部合法外宽及 ζ，使用 T01/T02 同见证已经给出的物理全支撑指数 599/1000 恢复原全表真幂项。矩形样本、包络、截断与算术使用同一个实际 c；绝对估计中的 |c| 仅出现在正算术包络与绝对互素均值中。

`actual_rank_at_least_three` 验证余集每个真实非零小/粗分解的粗素数个数至少为三。之前小完整模数及粗秩零、一使用 5d1786aa 的付款。之前 51859a24 的单原标签已包含在第二式，使用全式时只计一次。

## 宽度一致的矩形化

原稿 `distribution-prime-product-completion-20261010.txt` §§2–4 给出原标签、额外截断和两个 HB 分支，§10 单独在 HB 前处理低粗秩双素数。`low-rank-convolution-bv-20261010.txt` §§1、7 要求整局部乘积尺度、两边正幂范围、真正独立于模数的互补行及可求和的预选分离成本。本文在这一处补入具体的有限矩形划分。

1. 第一素数 p 与第二素数 t 按共同的右闭二进窗口 `P<p≤2P, V<t≤2V` 分组，末窗在 N 截止。原顺序、平方及所有重复标签均在原带权双槽中。固定 t，额外乘积 η 和四个原仿射门沿 p 单调或反单调，取值均在 [0,1]。一个头窗 Iᵢ 的 Δᵢ(t) 取五个原因子在两端的绝对差之和。每个 t 的全部 Δᵢ(t) 之和至多 5，且窗内实际 W 与左端样本的绝对差至多 Δᵢ(t)。该界同时适用于全部 s>0，证明没有用导数除以 s。
2. 以 W 在同一窗左端的值作互补素数行，并以 Δᵢ(t) 作第二个非负互补素数行。真实头系数是常数轮廓乘素数指示，删除参数取 1。进程的目标仍是 N，字符端取 (N mod d)⁻¹。头窗沿用原 `primeSWInterval` 的整数 Ioc，单个头格可短至空。头行平方能量至多 2P。互补行绝对值≤5、平方能量≤50V、一范数≤10V。两补零长度为 2P 和 2V。真实 d 与 N 互素；非单位素数的贡献按原进程与互素均值逐项处理。
3. 包络算术恒等地保留同余和互素两部分。一次现有局部导子定理用于 c 及样本行，一次用于 |c| 及包络行。取绝对值后额外出现两倍正互素均值。对 d 的支出使用实际 `abs(c d)≤1` 及既有 `sum_reciprocal_totient_subset_le_log`，得到 M≤4(1+log N)。在一个有效宏窗中所有头格的均值合计至多 `20 M PV / J`。因 P≥J，短窗的整数舍入 +1 由 `P/J+1≤2P/J` 吸收。
4. 令 x=PV。x≤N^(9/10) 时，任一真实乘积 pt≤4x<N，因此可用旧的离目标 signedRow 次幂界。一个宏窗至多 PV 对，取旧界指数 1/50 后，每窗支出至多 C N^(23/25)。这一步不要求 κ₀ 很小。较大窗只在有非零实际素数对时付导子费用。原粗糙门给出 N^(19/96)<2P,2V，原物理上乘积门给 x≤exp(1)N。最终 P,V≥x^(1/10)，全部实际 d<N^(2/5)≤x^(9/20)。
5. 总精度为 A 时，每宏窗先请求 A′=A+2。取 B=A′+2、D=B+A′+1、J=ceil(log(N)^B)。每窗导子代价为 `2 J K₀ x / log(x)^D`，加上上述 `20 M x / J`。所有窗共用导子常数与阈值，原宏窗个数至多 `bankLogConstant² log(N)²`。全族和由同一 N 阈值吸收，未另选 β 或 k。原 js 的 HB 标量、ψ、截断及真幂恢复直接使用 5d1786aa 的 `eventually_subset_atlases`，本次不重复加单标签或 FFT 截尾费用。

## 尚余的数学

对于 `remaining ∖ S` 上真实粗秩至少三的系数，原 medium 与 no-medium 两个分支的合计仍待实际算术支付。精确余式保留这些原标签、系数、同余和互素均值。这里的两个全族估计涉及联合带符号量，分别对两张表取绝对值的估计仍未建立。完整 PP 和最终 K/RealB 计数仍待该余项与后续链条核验。

T06 的原精细 Fourier 桥使用真实宽度并显式记录 s 的负幂。此次低粗秩通过逐头窗原五因子的总变差完成全部外宽的支付。未把 T06 的分辨率增长条件施加到 s，也未把一般导子 BV、其他 Γ 源或高秩谱返回作为本次证明前提。
