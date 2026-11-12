# 原单素数中段与最终矩形系数

最终矩形在同一次选参下满足原 87 项密度上界，以及下列单素数回收式。

$$
\left|\operatorname{literal}(N,Q,\rho)-\pi(N)D(Q,\rho)-\mathcal T_{\rm prime}\right|
   \leq \eta_{\rm sharp} H_N .
$$

\(\mathcal T_{\rm prime}\) 是三个真实模数序列作用在原单素数上的带符号和。它精确等于一组原 Heath–Brown 分解的实部。尚待估计的是 \(\mathcal T_{\rm prime}\) 本身。四份 Lean 已作静态核对。[同选参声明](P1OriginalSingletonRectangleSchedule.lean) [此前的原 87 项与物理计数终端](https://github.com/UyNewNas/goldbach-formalization/blob/4733b07d186b2b6aad89e5b9b782c35cc27ebd37/docs/source-only/20261112-resume/t03/physical-reserve-next/P1OriginalFinite87PhysicalReserve.lean#L63)

## 完整模数与原权重

1. \(\lfloor N^{9/20}\rfloor<d<N^{599/1000}\) 中的每个真实非零系数都在整高粗秩载体 `wholeHigh` 内。粗秩至二的完整活跃模数（含小筛）小于 \(N^{2/5}\)。`middle_on_rank` 逐个模数证明原两端的等价，含端点正好为整数的情形。对高粗秩载体，先用已有普通素数 BV 补回 \(d\le\lfloor N^{9/20}\rfloor\) 的精确互素余项，再用已证的平方对数界转换剩余模数的素因子均值。在所得整和上分组三个槽时，已经没有施加于 \(q_1q_2q_3\) 的人为高度截割。[中段与原粗秩](P1OriginalSingletonMiddleRank.lean) [短秩水准](https://github.com/UyNewNas/goldbach-formalization/blob/32d541884c85748e3fb18f7a83801b2f8b16e359/docs/source-only/20261112-resume/t05/high-remainder-next/P4BOriginalAllRankClassicalRange.lean#L40)
2. `smoothNatural kap 6 N` 是既有的独立单素数权。它取值于 \([0,1]\)，在 \(2N^{1-\kappa_0}\) 的原下裁切之外直到 \(N\) 等于一，上过渡窗宽至多 \(\lceil N/\log^6 N\rceil\)。整数载体是 `chenPrimePrefix (2*N)`。原公开有限除数界允许任意一界系数，而以前的合成渐近定理写在另一棵下筛系数上。本次直接用有限界支付非零矩形系数的两个过渡，保留计数与均值中相同的权重。小素数部分严格有 \(N-p>0\)，大偶 \(N\) 的过渡窗内没有素数 \(p=N\)。[原素数权的实际转接](P1OriginalSingletonMiddleWeight.lean) [原光滑测试定义](https://github.com/UyNewNas/goldbach-formalization/blob/32d541884c85748e3fb18f7a83801b2f8b16e359/docs/source-only/20261028-resume-30f/transfer_lambda/P5CanonicalTentNarrowSingletonTransfer.lean#L22)
3. 给定完整素数 \(p\)，原单素数纤维只有一个取值，总绝对权至多一。对模数使用原 `full_difference` 的 \(Y/d+1+Y/\varphi(d)\) 界，其中 \(2N\le Y\ll N\)。差只来自至少可被一个 \(\ell^2\) 整除的模数，\(\ell\ge N^\omega\)。固定 \(\omega>0\) 后费用为 \(O_\omega(N^{1-\omega/2})\)。三个分开的序列都一界。先保留各原标签的重复阶乘，再在原槽系数上恢复三组阶乘。原小筛因子进入第三组。物理密度仍用原平方自由的 \(\rho\)。整个论证直接测试一个素数。[单素数平方碰撞与三因子等式](P1OriginalSingletonMiddleTensor.lean) [原完整模数核](https://github.com/UyNewNas/goldbach-formalization/blob/32d541884c85748e3fb18f7a83801b2f8b16e359/docs/source-only/20261112-resume/t05/collision-next/P4BOriginalCollisionKernel.lean#L111)
4. 调用一次 `original_archive_and_physical_reserves`，传入 \(\min(\mathrm{budget},1/2000)\)。保留其原 \(r,n,e,q,a,m\) 量词，在 \(a\) 之后选择一次 \(\beta,k\)。用 \(\omega=\nu\beta^2\)、\(\ell=\nu\beta\) 和原 `fine_budget` 得到 \(\ell+\tau J_0(\omega)<1/1000\)。在 \(\omega\) 固定后才与新的碰撞阈值取最大值，之后对每个充分大偶 \(N\) 成立。物理回收与中段转接各用 \(\eta_{\rm sharp}/2\)。密度上界 `numericUpper` 沿用原 87 个数值、真实六层前驱及第八层修正。分组读原 \(x,U,\zeta\)，代数等式对每次读数均成立。[同一矩形的真接收器](P1OriginalSingletonRectangleSchedule.lean)

## 原 PP 的适用条件

原稿包括一个原素数的情形。它要求预先固定政策、正粗筛指数、粗秩上限与平滑精度，逐充分大偶目标控制一个带符号的完整误差。每个有中变量的长度层都需整盒固定的三分组、全平方以及所选补平方或严格 \(W\) 许可。低秩用的是完整模数在局部尺度上的半级以下水准。[原对象和量词，第 15–46 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-prime-product-insertion-assembly-20261009.txt#L15) [精确互素均值和全部插入条件，第 23–70 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/distribution-prime-product-completion-20261010.txt#L23)

Lichtman 命题 5.2 的上确界确实包括近线性移动余类。它还要求带粗支撑和辅助 Siegel–Walfisz 条件的单变量、一界补卷积、三个分离的一界模数系数，以及下列四个不等式。这里 \(\theta=7/32\)，余类是目标 \(N\)，中变量长度是 \(U\)，完整局部尺度是 \(x\asymp UV\)。

$$
 Q_1<Ux^{-\sigma},\quad U^2 Q_2 Q_3^2<x^{1-8\sigma},\quad
 N^\theta UQ_1Q_2^5Q_3^2<x^{2-15\sigma},\quad
 U^{1+2\theta}Q_1Q_2^{5-2\theta}Q_3^{2+2\theta}<x^{2-15\sigma}.
$$

本包给出了作用于原单素数的实际序列及其卷积恒等式。整盒的四条长度关系仍须在实际局部参数验证。原 HB 补卷积有固定约数函数界，原稿另作一界截断扩展，并在该余类范围保留互反相位。[Lichtman 命题 5.2](https://arxiv.org/html/2309.08522v1#S5) [原稿保留相位的证明](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-prop52-retained-phase-bridge-20261009.tex#L5)

在 \(a\asymp x\) 时，Lichtman 定理 1.7 的大余类分支整体水准为 \(153/256-\varepsilon\)。它还要求模数权对于指定的每种长度分解都三重良可分解。原稿有更细的逐节点上限，粗秩至三时启动真实第三门，此后的高秩节点各有带缓冲的局部许可。只知总支撑 \(d<N^{.599}\) 不提供这些结构。命题 6.6 的对象是特定 Iwaniec 筛权与其前缀盒。Maynard 定理 1.1 和 Pascadi 的素数 \(5/8\) 定理所印的隐常数可以依赖 \(a\)。所核外部定理均不能直接支付本矩形的整段。[Lichtman 定理 1.7 与命题 6.6](https://arxiv.org/html/2309.08522v1) [Maynard 定理 1.1](https://arxiv.org/pdf/2006.07088v1) [Pascadi 定理 1.3](https://arxiv.org/html/2505.00653v1#S1) [原高秩的局部上限](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/current-eighth-distribution-interface-audit-20261009.tex#L92)

## 尚欠的付款

- **最终矩形。** 需要在相同的固定选择下证明 \(\left|\operatorname{Re}\mathrm{singletonAtlas}\right|=o(H_N)\)。原稿的任意对数节省更强。新端点保留 `trim + Σ(medium + noMedium − properPower + roughPrime)`。每个原素数最多展开成六个 HB 槽。对有中变量的单组 chart，需为真实 \(x,U,Z\) 接入低首全部活跃词的整盒四条与受限近线性余类算术估计。已有高首 \(>\mu\) 的几何和一般一维粗 HB 槽的辅助 SW 可复用。无中变量时，同一原素数组可能有一个长变量，也可能有两个，分别走原单长原始进展/Brun 与双长 Poisson/Weil。双原素数乘积 `RealB` 的无中变量计数不能支付这里的单长支路。内部完整乘积 trim、proper power 与 rough-prime 修正仍按原符号留在等式里，相关既有估计须按其具体权重与作用域接回。[原 HB 的全部项](P1OriginalSingletonMiddleTensor.lean) [原单长及双长计算](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/distribution-prime-product-completion-20261010.txt#L250)
- **历史 `comparisonMiddle`。** 系数是 `eventPolicy true` 的实际粗筛系数减去 `eventPolicy false` 的实际粗筛系数。还须在相同的偶目标及参数上支付此差的中段，或支付其两个原系数的单素数余项。\(d\ge N^{.599}\) 两个系数逐点相等的结论对中段不提供相消，也没有识别任何一棵树的系数与新矩形 `Params.rho` 相等。
- **历史 `savingMiddle`。** `full87PhysicalRhoChange` 按原 87 个拥有者和完整后继子树取第六前驱减第八更新。此系数还需自己的单素数中段估计。旧 `exists_original_reserves` 的已付低段/中心转接对后选的 `cap,w,z,ell` 一致，其中 \(w\) 只有上界。应用原 PP 时必须先固定一个正 \(\omega\)、各族、细网与恢复权，再令 \(N\) 增大。新结果并未给出对任意随 \(N\) 变化的 \(w\) 的分布界。[历史两项原定义](https://github.com/UyNewNas/goldbach-formalization/blob/4733b07d186b2b6aad89e5b9b782c35cc27ebd37/docs/source-only/20261112-resume/t03/physical-reserve-next/P1Original87SharpMiddleReserve.lean#L28)

## 复现选择

T09 核对锁定 Mathlib 后发现两份已发前件有三处使用了错误的引理名。本包的安装补丁将两参数的 `abs_sub_le` 改成 `abs_sub`，适配 \(|x-y|\le |x|+|y|\)。新代码中的三参数三角不等式仍使用 `abs_sub_le`。登记绑定已发原件和安装后像的字节，四个新模块和旧前件的公开类型不变。整依赖的 Lean 内核验收须另行执行。本包补上最终矩形的对象对应、单素数碰撞费用及共同选参，三项的完整 PP 付款仍待证明。[补丁](SHARP_ABS_API.patch) [来源登记](REGISTRY.json)
