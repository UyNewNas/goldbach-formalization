# T23 · 原 Program 的离散素数盒与算术 Θ

固定原 Program 网格和 $\varepsilon>0$。七份 Lean 源候选给出一个 $T$，对每个 $n\ge T$ 给出 $N_0(n)$。当 $N\ge N_0(n)$ 时，同一阈值适用于深度 0 至 440 的每个完整 Program（包括所有原物理 cells）、两个原根、两种极性、全部 401 个终端原子。在同一原生素数词上，先对每一项取绝对值再相加，得到

$$
\sum_{\mathbf p}|m_N(\mathbf p)|
\left|{\bf1}_{I}(\mathbf p)\frac{\Theta_{Q_0}(N,B)}{H(N)}
     -{\bf1}_{S_n}(\mathbf p)\frac{\Theta_{Q_n}(N,B)}{H(N)}\right|<\varepsilon .
$$

$B$ 是该原整数词之积。两侧均施原根的整数 prime band，所有前缀坐标是真素数且不整除 $N$。指标 $I,S_n$ 含完整原几何 Member 及终端表格原子。$Q_0$ 是同根理想总 level 得出的模参数；$Q_n$ 是同一根在精度 $n$ 的冻结总 level，已和该根整数 RootKey 的 cellQ 逐项识别。$|m_N|\le1$ 可随 $N$、原词及冻结数据改变，两侧须用同一个标记。这里用原稿的绝对 $H(N)$ 尺度，零质量片也服从同一结论。

## 从完整实数门到真素数盒

1. **有限精度的门。** PrimeRegularGerms 对非零多元多项式按维数归纳，从一个非零系数和一元有限根集证明全乘积空间的零集为零测。若某一局部分式的分子恒零，就保留其原等号以及严格、弱比较的原值。对总化除法用独立恒零分支。FixedPrimeScreen 从源根、全部累计 rootCode 的阶梯、实际 perform、全部 LocalDomain、真实 cellMember 和终端 tableAtomSet 递推，证明指定原 Program 的布尔筛几乎处处在某个邻域恒定。这一结论对每个固定的有限 $n$ 成立，包括钳位区、计算时读到的结点、retain 和两种 W2 双点公式。
2. **由连续测试得到算术阈值。** SharpPrimeBox 把原对称差与原区域取交，按真实原生 slot 的任一双射重排到固定维数，证明其 Lebesgue 体积准确保持。对这个集合显式取厚度 $1/(j+1)$ 的连续上包。上包在集合上为 1，在几乎处处的邻域稳定点收敛至原指标，故普通体积控制真上包的极限积分。正盒 $[b,1)^r$ 上 $\prod_i 1/x_i\le b^{-r}$。先固定上包，再用 ActualPrimeBoxTestFunctions 的正盒连续测试和原 Mertens 极限；算术权精确为 $\prod_i1/(p_i-1)$。把这个上界接到已审的 all_fixed_program_threshold，就有先 $n$、后 $N$ 的 fixed_screen_primebox。它不预设素数边界误差，也不从抽象 $L^1$ 直接推出离散点的结论。
3. **同一整数词和两个真 Θ。** PrimeProgramWord 从指定 code 和真实槽位恢复 integerWord，实际 W2 双点按 [较大, 较小] 追加。word_product 证明对任何可交换乘积均与原坐标重排相符。literal_word、literal_level 逐侧把同一词的对数、原 residual 和该侧真实 $Q$ 识别。DiscreteThetaTransport 用既有逐词 singular/totient 插入公式，把两侧 $\Theta/H(N)$ 写成 $\ell_N\,\mathrm{wordFactor}(1,\mathbf p)\prod_i\log_Np_i$ 乘本侧真物理权。公共因子保留每次重复素数，且在真盒上被 $2\cdot2^r\prod_i1/(p_i-1)$ 控制。两侧均通过时用已审物理密度位移估计；仅一侧通过时使用该侧自身的残量下界与物理权界。实际 originalBand 在点上过滤。frozenQ_is_original_fibre 识别该点已有的 cellQ。
4. **完整支持与共同阈值。** FullPrimeTheta 沿已通过的原 Member 用每个新增坐标的 $x\ge L/6$、原终端残量下界及前缀残量递减性，得到固定正下界 bottom。根坐标使用原根带下端。对于每个素数且不整除 $N$ 的输入，若有一侧通过，则所有坐标都进入 $[\mathrm{bottom},1)$。上端等号将迫使某个 $p_i=N$。full_sum_eq 把所有 $p_i<N,\ p_i\nmid N$ 的真实素数词求和精确缩到这一正盒，两侧均失败的项保持零。all_program_arithmetic_threshold 对有限的全部字、根、极性和原子取共同的两层最终事件。顺序为网格与误差、冻结精度、算术目标；不要求全体精度共用同一个 $N_0$。对固定网格累计有限多个绝对损失时，还可按原预算先缩小每项 $\varepsilon$。

## 同余与原收据的范围

SingleReceiptTheta 对一个指定的加法素数编号 $\ell$，沿实际 rootHistory 的列表位置逐项读取原 mark，仅保留指定 shape 与实际整数词一致且属于 T17 原 frozenCarrier 的位置。该筛直接测试原 $B\mid N-\ell$、原 rootMask 中的 $\mathrm{ChenPrimeRough}(N^a,(N-\ell)/p_{\rm root})$，以及当前 occurrence 的 memberCutoff 和子商粗糙条件。用 T23 上轮已审的同 shape/词位置重数读出 $0\le m_{N,\ell}\le1$。all_single_receipt_threshold 对所有 $\ell$ 及所有 rootKey 查询精度 $m$ 共用阈值。这里比较的是施加同一实际收据谓词后的两个几何 Θ。

T17 的原计数还对所有满足条件的 $\ell$ 求和。原词本身不能决定 $\ell$，同一词可对应许多加法素数。逐个 $\ell$ 的统一小误差和每词至多一个已发出路径位置，均未给出累计收据的归一化总质量。将本结论用于整项原 receiver 计数，仍需要对这个真实同余/粗筛族的总系数给出相应的正筛平均或同源质量估计。更换理想与冻结图的 winner、adopted 标记或合并其他 11 个 occurrence 也需各自的比较。

## 核验记录

原稿 manuscript-body.tex 的有限缺陷与实际后继部分给出同一 $Q$ 下正标记族的 $\Theta_Q$、实际 residual、全和 selected square 和继承上界；共同近似与零质量绝对误差见同节结尾。本文只处理上述原前缀几何 Θ 后果。源码基准为 212cbdcbdaf9ce267febd21bdfbc6d1f7fb0dc6f，手稿基准为 9731290e8f53cffda44129906cde6a965eaa869b，具体固定源和本轮 SHA-256 见同目录 REGISTRY.json。

本轮仅交付未编译的 Lean 源和静态源核，未运行 Lean、Lake、LSP、本地 proof、数值 producer、证书或远端任务，kernel credit 为零。完整 Y24、adopted 计数、联合 430+11 和 H34 保持待证。
