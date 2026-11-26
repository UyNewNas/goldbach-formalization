# P3.6 原始 U5 的归一化密度误差

三个源码增量把冻结稿的下筛密度投影接到原始 U5 外素数对上。在所有原始外标上求和后，完整模数的舍入物理密度至多比同一策略的完整原始密度少一次指定的误差。稿件采用 2026-11-06 冻结版，路径为 `paper/release-20261106/en/`，固定提交为 `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`。三个新模块均已通过严格编译、独立核重放、完整声明／类型／传递公理审计，以及归档的本地内容复核；范围与原始证据见[验收记录](ACCEPTANCE.json)。P3.6 整节点仍未闭合，[待证边界](../NEXT_DENSITY_BOUNDARY.json)已据本轮结果更新。

## 逐行支付粗舍入与 beta 误差

对每个粗网格 `mesh` 和任意正数 $\kappa,\epsilon_{\max}$，`exists_rounded_U5_normalized_density_reserve` 先选出 $0<\epsilon<\min(1/8,1/272,\epsilon_{\max})$、$\tau_0>0$ 和 $N_0\ge2$。它们统一适用于每个偶数 $N\ge N_0$、每个原始 `PairRange R` 和 `CandidateBank mesh`、每个 $t\in\texttt{pairSupport}\ N$，以及每个 $0<\tau\le\tau_0$。记 $P_t=\texttt{selectedPolicy}\ R\ \texttt{bank}\ (1/1000)\ \texttt{false}\ N\ t$，$F_t=\texttt{fullDensity}\ N\ P_t$，$D_t$ 为同一行 `roundedRho N ε τ P_t` 在 `roundedSupport N ε` 上的 `physicalDensitySum`。逐行结论为

$$
F_t-\kappa\frac{\mathfrak S(N)}{\log N}\le D_t.
$$

令 $\nu=34/125$、$w=N^{\nu\epsilon^2}$、$z=N^{417/5000}$，枚举上界取 $\lceil z\rceil$。`fullDensity_sub_roundingLoss_sub_betaGap_le` 使用该上界、同一策略和同一粗素数载体。若 $A,C$ 分别为舍入前后的粗密度，$V$ 为实际小素数 Euler 乘积，则下筛投影给出 $F_t\le VA$。结合精确恒等式 $A-C=\texttt{roundingLoss}$ 和 $VC-D_t=\texttt{betaGap}$，得到 $F_t-V\,\texttt{roundingLoss}-\texttt{betaGap}\le D_t$。这个方向允许原始及舍入密度取任意符号。

先取统一 Euler 上界常数 $B>0$，再按目标尺度上的 beta 预算 $\kappa/2$ 选 $\epsilon$。随后指定粗舍入预算 $\eta_{\rm box}=\kappa\nu\epsilon^2/(2B)$。当 $4\le w\le z\le\lceil z\rceil$ 时，$V\le B\mathfrak S(N)/\log w$ 及 $\log w=\nu\epsilon^2\log N$ 将粗舍入误差控制在另一半预算内。取两个细网格宽度上界的最小值，再取 beta、粗舍入及 $w\ge4$ 三个阈值的最大值。相同 $\epsilon,\tau$ 同时保证每个非零舍入系数的完整模数严格小于 $N^{599/1000}$。[逐行归一化源码](../../../../ImbalancedChen/P3OriginalU5NormalizedDensityReserve.lean) · [冻结稿 `sv:lower-projection`、`sv:physical-lower`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex#L445-L481)

## 在完整模数上对原始素数对求和

对每个原始外标 $t=(p_1,p_2)$，记 $b_t=p_1p_2$，$K=\texttt{roundedSupport}\ N\ \epsilon$。`pair_coprime_of_mem_roundedSupport` 证明每个 $k\in K$ 都与 $b_t$ 互素，包含舍入扩充的载体。由欧拉函数的积性，`fullModulus_density_eq` 对任意有符号函数 $\rho:\mathbb N\to\mathbb R$ 给出

$$
\sum_{k\in K}\frac{\rho(k)}{\varphi(b_tk)}=
\frac{1}{\varphi(b_t)}\sum_{k\in K}\frac{\rho(k)}{\varphi(k)}.
$$

`roundedRho_fullModulus_density_eq` 取实际行系数 $\rho_t=\texttt{roundedRho}\ N\ \epsilon\ \tau\ P_t$。完整模数始终为 $\texttt{fullModulus}\ t\ k=b_tk$。[完整模数与互素性源码](../../../../ImbalancedChen/P3OriginalU5RoundedPairDensity.lean)

令 $T_N=\texttt{pairSupport}\ N$。其外标满足 $N^{417/5000}\le p_1<p_2<N^{19/125}$，两个素数均与 $N$ 互素。在这一选择器的既有调和极限中取连续测试函数 $f=1$，`exists_pairSupport_harmonic_mass_bound` 得到固定 $H_0>0$，使充分大 $N$ 满足 $\sum_{t\in T_N}1/\varphi(b_t)\le H_0$。`exists_rounded_U5_pair_normalized_density_reserve` 以 $\kappa/H_0$ 作为逐行预算，合并调和阈值与逐行阈值。对同一 $R$、候选库和细网格，沿非负权 $1/\varphi(b_t)$ 相加得

$$
\sum_{t\in T_N}\frac{F_t}{\varphi(b_t)}-\kappa\frac{\mathfrak S(N)}{\log N}
\;\le\;\sum_{t\in T_N}\sum_{k\in K}\frac{\rho_t(k)}{\varphi(b_tk)}.
$$

等于同一整数模数的不同外标仍按原有重数求和。完整模数的严格支撑界对这组参数和每个非零 $\rho_t(k)$ 同时成立。[外标合并源码](../../../../ImbalancedChen/P3OriginalU5PairNormalizedDensityReserve.lean) · [原始调和极限](../../../../ImbalancedChen/CurrentChenPairHarmonicMean.lean)

## 仍须供应的结论

- **正主项与稀疏族。** 对稿内实际选定并在 $N$ 之前固定的 `mesh/R/bank`，仍须证明原始有符号加权和 $\sum_t F_t/\varphi(b_t)$ 有固定正下界 $c\mathfrak S(N)/\log N$，其中 $c>0$。本次传递允许直接使用求和后的下界，无需逐行证明正性。各稀疏族和具体查询所需的正质量也须在各自的载体上证明。[冻结稿正标族归一化](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/argument.tex#L633-L649)
- **物理共同层与高秩准入。** 仍须在实际族上构造物理共同 $Q=N^\lambda$ 的覆盖，支付筛选补集，并在子节点沿用同一 $Q$，按子节点的标记乘积重新计算 $Q/B$，保留素数上界和正余量。U5/WT 高秩族的完整 (S)/(F) 包括全部平方条件、所选补集平方条件及适用的整原子分解分支。最后的 `eq:current-PP` 需要同一有符号系数的分布估计。[冻结稿共同层与准入](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex#L494-L531) · [整原子分解](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex#L128-L221) · [同系数 PP](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/argument.tex#L98-L126)
- **计数的精确均值。** `rowExactMean` 的每项分子另含取决于完整模数 $b_tk$ 的 `finiteCoprimeMass`。将上述密度估计接入计数时，还须保留或估计该项及相应的有符号修正。[实际计数与精确均值源码](../../../../ImbalancedChen/P3OriginalU5RoundedCountInsertion.lean)

若上述实际正主项日后给出常数 $c>0$，即可在已证的求和定理中取全局预算 $\kappa=c/2$，将舍入后的完整模数调和密度下界传递为 $(c/2)\mathfrak S(N)/\log N$。内部逐行预算由定理自动选为 $\kappa/H_0$。这一条件性推论说明下一个解析输入应是什么，并不提供尚缺的正主项。
