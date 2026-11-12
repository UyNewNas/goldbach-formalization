# Γ9–21 的径向闭壳与真实标记秩

四份冻结源码给出原经典夹持根的秩分解、临界乘积墙 $M=N$ 两侧的普通整数质量，以及该质量在原密度尺度上的价格。四源通过这一范围的静态审查。加法素数测试壳仍缺实际系数上的分布估计。

## 双端点与边界

取 $z=N^{1/96}$。任意固定 $c>0$ 后，最终 $z\le cN\le z^{100}$ 且 $z\ge\mathrm{primeErrorStart}$。上端用 $z^{100}=N^{1+1/24}$，所以允许固定 $c>1$。`roughCount_buchstab_band_100` 给原 $\Phi(cN,z)$ 的双侧绝对误差。乘 $\log N/N$ 后，误差受 $96C(c\,\mathrm{buchstabRemainder}(z)+z/N)$ 控制并趋零。由 $\log(cN)/\log z\to96$ 和 Buchstab 函数在 96 连续，`endpoint` 的极限为 $96c\,\omega(96)$。

`shell_limit` 在固定 $0<b\le c$ 上从同一 $z$ 的两个真极限相减，对应集合差正好是 $bN<M\le cN$ 的 $z$-粗整数。它的归一化极限为 $96(c-b)\omega(96)$，包括 $b=c$ 的空壳。取 $0<h\le1/8$ 后，用 $((1-2h)N,(1+2h)N]$ 覆盖 $[(1-h)N,(1+h)N]$，两端等号都覆盖，$M=N$ 也在壳中。该相减没有对原种子的两个单侧上界作差。

## 标记纤维与原目标

`native_rank_count` 用 $\mathrm{range}(201)$ 遍历原秩。对已固定的颜色字，从完整坐标的前 $1+|cs|$ 位可恢复 $p,q_1,\ldots,q_s$，由乘积和正的前缀积恢复尾整数 $m$。其余坐标是原规范非降素因子表。相等尾素数和倒数第二颗指定素数处的等号均保留。不同颜色及重复出现的 112、122 在外层逐次求和。该字典给出原两种计数；测试时读取 $M<N$ 且 $N-M$ 为素数，普通计数保留等于 $N$ 的边界。$2N$ 只扩大坐标类型 `Fin (2*N+1)` 以容纳外壳，模加法目标仍为 $N$。在原实际支撑每一坐标都不超过 $N$，`min` 截断正好给原坐标。对仅接受 `Fin (N+1)` 的快捷接口，仍需在安装调用处明示转换。

`prime_floor` 从真实 $p\ge N^{833/2500}$、$R\ge N^{7/128}$、$q\ge R^{50/227}$ 以及尾数原粗糙条件推出所有实际槽 $\ge N^{1/90}$。`transition_floor` 保证充分大 $N$ 上，因子二的外过渡仍在 $N^{1/96}$ 以上。`bandTuples` 允许所有 $k$ 维有序素数向量与重复因子。原 `p5z_marked_prime_product_fibre_card_le` 对每个真实完整乘积给 $k^k$ 个向量的上界，因而全壳可用固定 $20\sum_{k=0}^{200}k^k$ 倍粗整数壳控制。无需乘积单射。原目标删素数的掩码只作用于 $p$ 和指定 $q_i$；上包采用前包所审的无掩码族，普通删素数损失已单列，此处不再扣费。

## 误差次序与价格

`absolute_radial_payment` 在给定 $\delta>0$ 时先选固定 $h$，再令 $N$ 趋大，得到 $\mathrm{boundaryCount}\le\delta N/\log N$。固定倍数和 $\omega(96)\le1$ 进入宽度选择。该界可覆盖此处每字不超过 1 的非负权重；若用其他固定幅值，须按该幅值选择宽度。

`ambient_boundary_price` 令 $I=\mathrm{intervalMass}(833/2500,1/3,1/2)>0$，取 $K_0=8452171/1250000$ 和 $\delta=\varepsilon(I/2)/K_0$。原 `uniform_clamp_witness` 先固定一个阈值，随后对所有 $0\le\tau\le1/12$、$1/(n+1)\le11/384$ 有 $(I/2)H_N\le\Theta_{\rm clamp}$。与壳阈值取交后得到 $K_0(\mathcal C(N)/\log N)\mathrm{boundaryCount}\le\varepsilon\Theta_{\rm clamp}$。故 $h$ 同时先于 $N,n,\tau$。普通壳本身在 $N/\log N$ 尺度；乘密度后才到 $H_N$ 尺度。对真素数 $N-M$ 的稀疏，仍需在一个实际光滑外族上使用原 U* 或同一物理 $\rho$ 的精确互素均值分布。这四源不提供这项估计。非径向仿射墙、较小径向区、整族光滑算子和完整 H430 各保留原职责。

核对 29 个不同登记路径的字节、SHA256、Git blob，包括原生 Buchstab 带、秩纤维界和八份稿源。另在正式前驱 78ae6ad15 逐字核对 `uniform_clamp_witness` 的阈值次序。新增四源共 26 条声明、7 条直接导入边，其中 4 个为外部直依赖。作者 REGISTRY 为 `f22e2b93c550233f69c07a5d02b961b74b77558ce57485817dbfd5ff84131225`。未运行 Lean、守卫、数值或 CI。
