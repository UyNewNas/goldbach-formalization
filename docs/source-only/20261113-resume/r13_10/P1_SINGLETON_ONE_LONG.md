# 最终矩形单素数中段的一个长槽

**结论。** 原稿的单长槽 Brun 有限估计确有现成证明源码。在最终矩形的真实 singleton atlas 上，固定短元后可使用该估计，得到 no-medium 中“恰一个长槽”全体行的 \(O_A(N/(\log N)^A)\) 书面推导。下文分别核对原高秩物理系数 \((P.S,P.rho)\) 和 T03 张量使用的 \((products(P),free(P))\)。识别这部分行、接入有限估计和恢复总费用的组合尚无本次验收的 Lean 声明。两个历史差和最终矩形的完整中段均待支付。

## 原问题和范围

原稿正文第 256–349 行给出同一移动剩余类、同一计数和均值系数及各个 HB 分支。10 月 10 日配套原件 distribution-prime-product-completion-20261010.txt 的 §§2、4、6–9 给出实际 trim、每组恰一个 log、一个长槽的 E5 和两个长槽的 E4。T03 的 P1OriginalSingletonRectangleSchedule.original_single_prime 在所选的同一 β、k 上给出 \(\omega=\nu\beta^2>0\)、平滑参数 \(\lambda=\mathrm{kap}\in(0,1)\) 和 singletonAtlas P kap K kap zeta。下文以 λ 表示这里两个位置共用的 kap，以 \(R=2^c\) 表示测试素数的唯一母尺度。

在 noMediumAtlas 中对原 atlasEval 的每一项保留 longBlocks (originalMediumHigh ζ [c]) bs 长度为 1 的项，沿用 typeIValue 的 firstMedium = none 以及原有的 HB 标量。这定义了本文所估的实际有限子和 \(\mathcal L_1\)。采用预先固定的原正 ζ，同时满足稿内上限，例如再要求 \(0<\zeta\le1/20000\)。T03 的恒等式对任意实 ζ 成立。这里的解析界仅针对上述正 ζ。沿用完整的 chartBank (2*N) 1、原 \(K\ge2\) 和原 ω。最终阈值可以依赖这些固定数据、λ、ζ、A。

## 原系数和精确的核

令 \(D=\lfloor N^{599/1000}\rfloor\)。以下两种模数输入都满足有限 E5 的 \(\mathcal Q\subseteq(0,D]\)、\((q,N)=1\) 和 \(|c(q)|\le R_\rho\)，可取除数阶 \(J=0\)。

1. 在 \((P.S,P.rho)\) 上去掉系数为零的模数。T03 的 read_live、live_data 及 P4BOriginalCollisionPhysical.supported_physical 给出去零前后逐项不变、正性、目标互素、严格高度和 \(R_\rho=1\)。P.S 是同一次选择的 wholeHigh。若直接保留原 Q P.omega N 的 middle 子集，按原上下界筛模数也保持有限 E5 的这三条前提。
2. 对 \((products(P),free(P))\)，每个 \(q=h\prod p_i\) 来自原 P.records。小 Rosser 支撑给 \(h>0,(h,N)=1\)。原 crop 把每个粗素数放在排除了 \(N\) 的素因子的集合中，因此 \((q,N)=1,q>0\)，重复粗素数也成立。Params.full_cap 逐记录给 \(q<N^{599/1000}\)，用的是原 \(\ell+T J_0(\omega)<1/1000\)。每条 freeRecord 的模至多 1，这是 scalar_bound、真实 Rosser 系数的一界及词长符号的直接乘积。fibre_card 给每一完整模数上的记录数至多 \(J_0(\omega)!\)，故 \(R_\rho=J_0(\omega)!\) 在 \(N\) 前固定。真实带号词、排序重数和小因子都已收进 free，随后按整个 \(q\) 求和。

P5IndependentPrimeSourceWordDictionary.wordKernel 及 residueKernel_real 给出的核是

\[
 K_q(b)=\mathbf1_{b\equiv N\ (q)}-\mathbf1_{(b,q)=1}/\varphi(q).
\]

OriginalOneLongFiniteBrun.actualCount 和 actualMean 的 \(b\) 正是 \(mn\)。若 \((m,q)>1\)，两项自动为零。短元取值、区间、平滑函数均独立于 \(q\)。被删除的 \(q\) 的素因子只出现在 Brun 定理自己的精确互素均值与 compatibleGapDensity。两版可各自估计。T03 对完整平滑差额已支付一次碰撞，本文无需逐分支转移那笔预算。

## 一套原短元的有限 E5

原 atlasEval 对 \(j=0,1,2\) 使用 \(s=2(j+1)\) 个有序位置和标量 \((-1)^j\binom3{j+1}\)。粗筛水平为 \(z=f(2^{6K+3}R)\)，\(f(t)=t^{1/(\log\log t)^3}\)，Möbius 截断为 \((2R)^{1/3}\)。唯一长位置由整块决定，记其整数下端为 \(U>R^{1/3+\zeta/4}\)。其余块的下端皆 \(<R^{3\zeta}\)。每个非零几何块有一点 \(b\) 满足 \(N^{1-\lambda}<b\le2N\) 且 \(R/2\le b\le2R\)。故 \(R\to\infty\) 一致成立，\(U>(2R)^{1/3}\) 最终成立。长位置如果是 Möbius，其所有值都因原截断而为零。其余角色为 one 或 logarithm。长位置严格粗投影为 \(\mathbf1_{(n,\prod_{p\le z}p)=1}\)，包括 \(z\) 恰为素数时的删去。

按原槽序逐个固定 \(s-1\le5\) 个短元 \(\mathbf v\)，记 \(m=\prod v_i\)。其系数 \(a_{\mathbf v}\) 是原 blockValue 的乘积，保留 unit、Möbius 的带号值及实截断、每槽自身的严格粗筛和可能落在短元的唯一 log。其模为 \(O(1+\log N)\)，包括 log(1)=0。允许不同短元列有相同的 \(m\)，下式逐列相加。外层原整数由 \(b=mn\) 唯一恢复。反向把 \(n\) 插入原位置即恢复唯一 factorTuples s b 的成员，后者递归按表头和尾积取 divisorsAntidiagonal，包含每个正整数列恰一次。因此每个有序槽的重数均获保留。

长块原整数区间为 \(U<n\le2U\)。外层 integerWords (2*N) 1 要求 \(mn\le2N\)。固定 \(m\) 后取

\[
 L=U+1,\qquad K_I=\max(0,\min(2U,\lfloor2N/m\rfloor)-U).
\]

于是 \([L,L+K_I)\) 精确枚举原整数，\(K_I\le U\)。整个短元纤维的几何权恒零时直接删去。此判据只用 \(m,n,N,R\) 及原 profile。其余纤维各有一点满足上述几何支撑。

令 \(W_N(t)\) 为 actualLicence λ 6 N 的实数一维 ambient，即下端的 \(\eta(t/N^{1-\lambda})\) 和宽度 \(\delta=(\log 2/\log(N+2))^6\) 的上端对数 collar 的乘积。取固定 \(C^\infty_c((1/2,5/2))\) 函数 \(\chi_0\)，在 \([1,2]\) 为 1。再取光滑 \(J_*(t)\)，在 \(t\ge3\) 等于 \(1/\log t\)，在 \(t\le2\) 为零，中间用固定平滑过渡。这使 \(J_*\) 和 \(tJ_*'(t)\) 在正半轴有界。对 \(y=mUv\)，设

\[
 F_{\mathbf v}(v)=\chi_0(v)W_N(y)\,\eta(y/N^{1-\lambda})\,\psi(y/R)\,
                    J_*(y)g(Uv),\qquad g(t)=1\text{ 或 }\log t .
\]

其中 \(\mathbf v\) 是短元列，\(v\) 是长槽的归一化实自变量，函数在 \(\chi_0\) 的正支撑外光滑延拓为零。第二个 \(\eta\) 是 atlas 的原 complete trim。唯一 log 在长槽时取 \(g=\log\)，否则该 log 已在 \(a_{\mathbf v}\) 中。几何非零的原 \(b\) 最终都 \(>3\)，故延拓在原整数处精确。\(F_{\mathbf v}(n/U)\) 乘上 \(a_{\mathbf v}\)、长槽粗指示和 \(K_q(mn)\) 正是原行，包括 \(\psi/\log(mn)\)。这是原傅里叶分离前的有限母和，完整几何 profile 只剩一个实变量，故无需引入截频或其误差。

logWidth_mixedEuler 取阶数 1 与宽度指数 6 给 \(|W_N|\le1,\ |yW_N'(y)|\ll(1+\log N)^6\)。\(\eta,\psi\) 的零阶及一阶 Euler 导数有固定上界。长槽对数在 \(\chi_0\) 支撑上为 \(O(1+\log N)\)，其 Euler 导数为 1。利用 \(v\in[1/2,5/2]\) 从 Euler 导数转成普通导数，得到全实轴上的

\[
 \|F_{\mathbf v}\|_\infty+\|F_{\mathbf v}'\|_\infty\ll(1+\log N)^7.
\]

常数与 \(m,U,q\) 无关。固定 \(m\) 后，链式法则给 \(d/dv=v^{-1}y\,d/dy\)，故没有 \(m\) 或 \(U\) 的损失。

对 OriginalOneLongActualChartE5.actual_chart_one_long_finite 代入上述 \(L,K_I\)、移动剩余 \(a=N\)、完整模数上界 \(D\)、\(J=0\)、\(\mathcal Q,c,R_\rho\)，以及 \(u=U,Rwidth=1\)。对每一短元列单独用 \(Mset=\{m\},\alpha(m)=1,M=1\)，将 \(a_{\mathbf v}\) 在外面乘回。取 \(P_z=\{p\text{ prime}:p\le z\},Z=\lfloor z\rfloor\)。活母图上 \(Z\ge1\)。令 \(M_b\) 为短积 \(m\) 的原 dyadic owner 下端，unit 时取 1。置 \(x=UM_b\)。同纤维有 \(b\in[x,4x]\)，故 \(N^{1-\lambda}/4<x\le2N\)，而 \(x/2\le R\le8x\)。在同一原 \(K\ge2\) 下 \(x\le 2^{6K+3}R\le x^2\) 最终一致成立。roughF_upper 因此给 \(z\le x^{2/(\log\log x)^3}\le x\)。\(x\) 为正整数。eventually_all_chart_harmonic_le_two_L2 在这个 \(x\) 上适用于全部 \(P_z\)。

保持原 Brun 次序 \(j_B=\lfloor(\log\log x)^2\rfloor\)，向有限 E5 传 \(j_B,z,H=2\log\log x\)。写 \(r_B=2j_B+1,\ Y=z^{r_B},\epsilon=H^{r_B}/r_B!\)。actual_B1、actual_B2 来自有限层交错和、删除 \(q\) 的素因子后的差及 reciprocalGap_le_B2_epsilon。前缀界调用有证明体的 primitiveCoprimeDensity_two_tau 及除数整除区间变换；模数求和调用 physical_intervalBudget_sum 中实际 \(\tau,\varphi\) 的固定阶均值。有限 E5 的调用中没有作为前提的 E5、PP 或 \(\mathcal L_1\) 界。因 \(r_B\le3(\log\log x)^2\)，有 \(Y\le x^{6/\log\log x}\)。gap_le_exp_neg_L2_sq 给 \(\epsilon\le\exp[-(\log\log x)^2]\)。于是对事先固定的 \(\delta_1>0,B>0\)，所有活纤维在共同的 \(N\) 阈值后满足 \(Y\le N^{\delta_1},\epsilon\le(1+\log N)^{-B}\)。

## 收回所有短元和所有原行

有限预算经 physicalBudget_le_common_log 在 \(J=0\) 给

\[
 R_\rho(1+\log D)^4(10 YD+2\epsilon K_I).
\]

这仍保留各自的 \(K_I\)。对一套固定 HB 块，写 \(S=\prod_{i\ne i_0}\operatorname{lower}(b_i)\)。每个正 dyadic \((V,2V]\) 恰有 \(V\) 个整数，unit 恰有 1 个，故整盒短元列总数为 \(S\)，即使出现重复块也是逐位置相乘。对每个有几何非零点的整块，\(SU\le mn\le2N\)。因所有短块下端 \(<R^{3\zeta}\)、短块至多 5 个且 \(R\le4N\)，有 \(S\le(4N)^{15\zeta}\)。因此

\[
 \sum_{\mathbf v}K_{I,\mathbf v}\le SU\le2N.
\]

原程序的 HB 标量至多 3，母标签数为 \(O(1+\log N)\)，三个阶各有 \(O((1+\log N)^6)\) 个块向量，这是 blockWords_card 和 hbCap(c)=2R 的直接结果。置 \(\mathscr L=1+\log N\)，将各短系数的 \(\mathscr L\)、profile 的 \(\mathscr L^7\)、模数预算的 \(\mathscr L^4\) 和全部原行的 \(\mathscr L^7\) 同时恢复，得到

\[
 |\mathcal L_1|\ll R_\rho\mathscr L^{19}
 \big[(4N)^{15\zeta}D N^{\delta_1}+2N\mathscr L^{-B}\big].
\]

选 \(0<\delta_1<(1-.599-15\zeta)/2\) 和 \(B>A+20\)。两项合计 \(O_{A,K,\lambda,\zeta,\omega}(N/\mathscr L^A)\)。这里只让 \(\epsilon\) 承担 \(2N\) 的真实长槽总宽度。若先把每套短元的两项都粗写为 \(O_A(N/\mathscr L^A)\)，再乘 \(S\)，则推不出这个结论。

## 源码接入和判定

- 最短形式化入口是 T03 的 singletonAtlas 与旧 noMediumAtlas。按原 firstMedium 和 longBlocks.length 做有限分拆，给出上述固定短元的 profileError 恒等，将有限 E5 接到已推导的 \(SU\) 恢复界。两种系数各有上述实例。物理版还可沿 eventually_smooth 接回同一矩形的 sharp-to-smooth 总余量。本件未增加 Lean 或验收结果。
- 全 middle 仍需要它自己的真实 medium signed convolution、two-long 及其余原 reserves 的同源恢复。T05 的两组 HB 中槽尺度和恢复不能自动供应单组 signed 算术估计。原两项 comparisonMiddle 和 savingMiddle 另有各自差权、物理门和量词。T09 既有外部适用审查与本轮 r13_07.md 中 Q01–Q08 的复用范围均未含这三项的直接终端。这里的补充属于稿内一长槽接线，本次范围中没有证据表明这一子项的原结论有误。
- 主要入口为 P1OriginalSingletonMiddleTensor.lean 的 singletonAtlas、P5PerGroupIntegerHBAtlasPushforward.lean 的 atlasEval、P5OriginalOneLongActualChartE5.lean 的 actual_chart_one_long_finite 和 physicalBudget_le_common_log。旧 E5、literal B1/B2、阶乘缺口、原始互素前缀和固定阶模数均值均有源码证明体。历史 hb_rough_one/REGISTRY.json 和 REPORT.md 记录了曾未装入生产路径的依赖及其字节。当前证据支持源码复用，完整编译、内核和传递公理检查仍需 GitHub 验收。

| 已读锚点 | SHA-256 |
|---|---|
| 原稿 paper/source/manuscript-body.tex | ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd |
| 稿内 distribution-prime-product-completion-20261010.txt | a953b3233c1249b4791830da33b76a58b19ca110a5e1b5b6172b3248a00053e1 |
| T09 P1_SINGLE_MIDDLE_APPLICABILITY_REVIEW.md | 26670a102ed3cf1ead2f11ba33de14100ab70ecc0cbb630106d2edd8b87d5ca9 |
| T03 P1OriginalSingletonMiddleTensor.lean | 18c8beeb835b6c10b1907afeb06bfddef08def3b668b553183b3fd0f2bef303b |
| T03 P1OriginalSingletonRectangleSchedule.lean | da9c50e548e61898b1ee4fe499ec0093fad50706930e54fce835ad8be10d2dcc |
| 旧 cohort04/primeproducts/sources/(sha)/P5OriginalOneLongActualChartE5.lean | 33890d7db29af4d6edbb74f2e45ff395345b4f1f9acda4c42589b11b5963cb89 |
| 旧 20261102-resume-30p/hb_rough_one/REGISTRY.json | 1c45e5a1b58821295fe35e99a588956e2b16f535dbf6950d669be7472278746b |
