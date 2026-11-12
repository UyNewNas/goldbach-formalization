# T18 独审 T23 原 Member 的离散素数盒与 Θ

**限定通过。** 固定网格和绝对误差 $\varepsilon>0$ 后，可先取冻结精度下界 $T$。对每个 $n\ge T$，再取 $N_0(n)$，对全部 $N\ge N_0(n)$、两个根、深度 $0,\ldots,440$ 的指定 Program、两种极性及 401 个原终端原子，有

$$
\sum_{\mathbf p}|m_{N,n}(\mathbf p)|\,
  \big|1_I(\mathbf p)\Theta_{Q_I}(B)/\mathcal H_N
      -1_{S_n}(\mathbf p)\Theta_{Q_{S_n}}(B)/\mathcal H_N\big|
<\varepsilon .
$$

这里逐坐标取素数 $p_i<N$、$p_i\nmid N$。$B$ 是该 Program 的原有序整数词之积。$I$ 与 $S_n$ 各自测试原整数根带与全部 QueryMember。两侧使用同一个标记，允许它随 $N,n$ 和词变化，且 $|m_{N,n}|\le1$。总和使用绝对误差尺度 $\mathcal H_N=C(N)N/\log^2N$。对所有 Program 的共同阈值按各自原生槽的固定排列给出，其结论对每个 Program 成立。

## 离散筛误差的来源

固定 $n$ 时，原根的累计有限台阶、$L,s,\chi$、各步的真实归一化坐标和末端查表，都在有限族有理函数中局部实现。PrimeRegularGerms 对非零多项式按维数归纳。固定其余变量后，排除一个非零系数消失的零测集合，一元多项式只有有限个实根，再用 Fubini。若某分支的分子恒零，则保留其等号判定及总化倒数 $0^{-1}=0$。因此继承参数、钳位、单点查表和半开 cell 的端点可在正测区域成立。FixedPrimeScreen 将这些比较通过原九类 shape、两种根的逐步更新与指定 code 递归到真实终端，得到固定 $n$ 的差集指示几乎处处在邻域内恒定。

设 $D_n$ 为原根带、原生立方体和两侧完整 Member 对称差的交。固定 $n$ 后，SharpPrimeBox 使用连续厚化函数 $\phi_j$，在 $D_n$ 的**每个点**均等于 1，且 $0\le\phi_j\le1$。其极限为闭包指标，而局部恒定性给出该指标与 $1_{D_n}$ 几乎处处相等。对固定正盒 $[\alpha,1)^r$，极限密度 $K(x)=\prod_i1/x_i\le\alpha^{-r}$ 可积。先选厚化宽度得到所需的积分上界，再将已存在的 tendsto_actualPrimeBoxTestSum_cube 应用于这个连续函数。真实元组的非负权 $\prod_i(p_i-1)^{-1}$ 始终按原 prime-box 定义求和，故对充分大 $N$ 有
$$
\sum_{\mathbf p:\ \log_N\mathbf p\in D_n}\prod_i(p_i-1)^{-1}
   < \alpha^{-r}\operatorname{vol}(D_n)+\eta .
$$
前一冻结包的 all_fixed_program_threshold 已证明右端的体积随 $n$ 趋零。这里实际建立了离散估计，覆盖恰好落在边界上的素数元组。

## 每个元组的原算术权

PrimeProgramWord 把根和每步真实读取的槽填入原 integerWord。空槽填 1 后不向词中追加任何字母。W2 对按 $[大,小]$ 追加，保留相等或重复素数的重数。literal_word、literal_level 和 log_product 分别识别实际已读指数词、$\log_N(Q/B)$ 与这些指数之积。理想侧用 sourceRoot 的 $Q_I$，冻结侧用 frozenRoot 的 $Q_{S_n}$。frozenQ_is_original_fibre 在原整数根带上把后者识别为同一 keyAt 的 cellQ，整条后代词保留本侧根总量。

对真实元组令 $J=\prod_i\log_N p_i$。DiscreteThetaTransport 的 common_factor 由逐素数插入的恒等式和真实 $\log(Q/B)$ 分母得到
$$
\Theta_Q(B)/\mathcal H_N
  = \operatorname{literalScale}(N)\ \operatorname{wordFactor}(1,\mathrm{word})\
    J\,\frac4{J\,L},\qquad L=\log_N(Q/B).
$$
其中 wordFactor 逐个使用局部算术因子，包含重复字母。两侧共享前三因子。固定正盒内，当 $N^\alpha\ge4$ 时，wordFactor 至多为 $2^r\prod_i(p_i-1)^{-1}$，另有 $0<J\le1$ 且最终 $|\operatorname{literalScale}(N)|\le2$。共同准入时使用已审的同词物理密度位移界 rate$(n)\to0$。只有一侧准入时只用该侧的 residual 下界与 envelope。两侧拒绝时通过定义取零。据此求和的上界只含有界的原素数盒总质量乘 rate$(n)$，以及上述真实离散差集质量乘 envelope。逐元组取绝对值后，共同有界标记可同时纳入估计。

FullPrimeTheta 从每个已准入的真实词本身取得固定正盒。终端 residual 至少为 $F=(11/384)/101^{440}$，沿原词往回每个活动槽至少为 $F/6$，根槽至少为原下端点 $a$。采用 $\alpha=\min(1,a,F/6)/2$。各槽的几何上端为 1，若实际指数等于 1，则 $p_i=N$，与 $p_i\nmid N$ 矛盾。full_sum_eq 由此将全范围素数元组的和精确化为这一张正盒上的和，分别处理只在一侧通过的情形。此覆盖的输入逐槽要求真实素数且不整除 $N$。最后对固定网格上有限的 Programs、根、极性、原子，两次取有限共同阈值。emitted_prime_threshold 代入由固定根历史、shape 和实际词得到的 selectedWordMark，消费前包同词位置的系数绝对值至多 1。U3/U4 仍各带自己的根标签。

SingleReceiptTheta 还检验了一个具体的余类收据。probe 在同一 rootHistory 中按完整 shape 和原整数词匹配位置，再测试给定 $\ell$ 是否属于原 frozenCarrier。该测试保留原 $B$、原 rootMask 对 $(N-\ell)/p$ 的粗糙性条件，以及对应位置的 memberCutoff、真实 cellQ。每个位置的非负标记只可能减少，故同词带测试的位置总权仍至多 1。all_single_receipt_threshold 的 $T,N_0(n)$ 同时适用于每个 $\ell$ 与辅助分区精度 $m$，两侧采用同一冻结位置标记。若把所有 $\ell$ 的指标相加，系数成为收据基数，可超出该上界。

## 未结范围

原稿正文第 795–817 行将缺陷估计放在同一 $Q$ 的正标记族上，并保留原物理后代。insertion-chain 第 222–234、345–353、509–520 行规定固定正盒、整词 $\mathcal H_N$ 尺度、有限深度的正指数下界及先精度后大 $N$。本包支付其中两侧几何筛作用在真实前缀素数和 $\Theta/\mathcal H_N$ 上的绝对误差。标记若在两侧各自重选，差分还含两套标记之差。对所有接收者 $\ell$ 求和后的真实加法筛计数及余项、adopted/q430 的重选、每个集中子族自身 $\Theta$ 的相对误差，以及 430+11 共同实现，仍须另付。各 $n$ 的整数阈值可不同。Y24、Y28 和整体 h34 保持黄色。

七份冻结 Lean 源共 63,310 字节。对照作者登记核验字节数、SHA-256、模块、imports、行数与公开定理，另以本地 Git 对象逐条核验 64 条依赖、4 条上一轮冻结记录及 1 条原稿记录的 commit/path、blob、字节数和 SHA-256。原稿 insertion-chain 在同一手稿提交的 blob 为 560d2a05d752f0b03e09a18c2028e6bb1c0c18db。源快照 212cbdcbdaf9ce267febd21bdfbc6d1f7fb0dc6f，手稿 9731290e8f53cffda44129906cde6a965eaa869b。静态数学与源码审查通过。本包未编译，kernel 信用为 0。
