# 经典 U3 夹持根的 Γ9–21 固定几何族与种子价

本包处理原夹持区间上全 20 个长字的正项。七个 Lean 文件给出真实标记几何、目标互素删除费用、普通整数质量的单侧上界以及原物理种子价的共同极限。将这些事实代入手稿的全局固定族定理 U*，在手稿层面得到所需的保守正项价。将 U* 所需的同一系数分布估计搬到本族的 Lean 实现仍然 OPEN。本包为 SOURCE ONLY，未本地编译、执行守卫或重放数值。

## 直接入口与量词

固定网格精度 n，取 0<τ≤1/12，1/(n+1)≤11/384。令 ν = frozenLevel n (1/2−τ)。在每个原夹持素数 p 的位置，原 rootQ 精确等于 N^ν，原 frozenQuery 精确等于 2。取 0<κ≤1/112，再让 N 经偶数趋于无穷。普通整数上界在全体充分大的整数上成立。固定族 U* 的阈值可以依赖 n、τ、κ 及误差。前一包的逐标记普通 Buchstab 估计有更强的一致性，不能把这种一致性转用到不同的几何族上。

写 H_N = 𝒞(N)N/log²N，Θ = clampMass N n τ，C = ∑_{j<13} switchedMass j。这里 C 是原种子的 13 个保守 switchedMass，含 112、122 各两次出现的整数计数所对应的原分组。已独立付过的坏 Γ5 不进入 C。主终端为以下四项。

1. FixedClampPrimeGeometry.tuple_mem 与 count_tuples 给出全字几何族及秩、排序和所有权重。FixedClampCredit.original_balance_at_sharp_family 将原 5(Θ−∑(E_p+S_p)) 的右侧改写为原其余种子项减去旧 longPrime、已付 Γ5 坏项价以及此正几何族的实际测试计数，误差仍为一次 εΘ。
2. FixedClampCredit.actual_untested_upper 给出每个 ε>0 最终 X_geo ≤ (J+ε)N/log N，其中 I_ν=∫_[833/2500,1/3) 4/[t(ν−t)]dt，J=C I_ν/4。整个族共用这个 J。
3. FixedClampSeedPrice.original_price_common_limit 给出 switchCost·Θ/H_N → K_seed J，switchCost=(K_seed/4)C，K_seed=681/100。使用原 θAtom 及其 Richert418.logarithmicIntegral 的原归一化。两处使用完全相同的 I_ν。上一包已付款的 BV 真实对数积分中心差在此没有再次扣取。
4. FixedClampCredit.paper_upper_price_fits 给出对每个 ε>0，先选 δ=ε I_ν/2>0，最终 (K₀J+δ)H_N ≤ switchCost·Θ+εΘ。手稿全局系数 K₀=8452171/1250000。原夹持区间具有固定正宽度。对逐格变化的稀薄子族没有这样的相对费用结论。

## 全部原标记与边界

外层 p 是模数前缀，也是完整 M 的首个已标记素因子。对第 j 个 Γ 里的每个颜色字 cs，从原窗口取严格递增 q₁,…,q_s，保留所有颜色，令 m 的规范素因子 r₁≤⋯≤r_k。尾因子满足 r_i≥q_{s−1}，等号保留。完整乘积 M=p·∏q_i·∏r_i 落在 N^(1−κ)<M≤N。未测试侧保留 M=N，原正项只在 M<N 且 N−M 为素数时给权 1。没有额外的尾素因子互素条件。固定 cs 和 M 时，保留 p 与整条 q 可以精确恢复 m。当尾素数相等、与已指定素数相等时，排序仍给出唯一规范尾。不同 Γ 中相同颜色的两次出现仍贡献两次。

sharp 是一个精确的充要条件。窗下端闭，上端开，原颜色判定保持其严格比较。ν 固定后，q≥(N^ν/p)^v 恰为 vν≤v log_Np+log_Nq；取补给严格上端。原五个 v 是 1/s₀、1/φ₁、1/φ₂、1/φ₃、1/s。顺序、颜色分支及总乘积条件因此是有限的几何比较。每个位点至少 N^(1/200)，原全乘积保证总秩至多 200。κ≤1/112 时 m=1 落在小产物侧，所以保留域中的每个元至少有五个真素数位点。

原标签仍要求 p∤N 及每个 q_i∤N。geo 将旧 primeWindow 的掩码由 N 改为 1，未改真实 Q、m、颜色字或加性素数检测。原测试计数由几何计数逐标记支配。对未测试侧，差集的每个输出 M 是满足 gcd(M,N)>1 的 N^(1/200)-粗整数。原 p5U7ActualBadRough_card_le_log 给出输出数 ≤(log N/log 2)N/N^(1/200)。在每个 M 的一个字纤维里，把 p 及 q 的全坐标交给原 omega3_labels_card_le_outputs，可恢复 m。纤维不超过 200^(1+length cs)≤200^7。20 个字总费用至多 20·200^7 (log N/log 2)N/N^(1/200)。它在 N/log N 归一化下趋零。此处的输出集合是覆盖，未将尾中恰有目标素因子的合法整数一并从原载体剔除。

## 积分付价

对每个原 p，平台 R=N^ν/p≥N^(7/128)。因 ν≤1/2 且 p 为正素数，trueAlpha=log(N/p)/log R≥2。旧 original_word_upper 已给在该实际 α 处的非单位 Buchstab 积分及统一阈值。新的汇总保留 Γ9–15 原七个并域，Γ16–19 原四行，以及 Γ20、Γ21 各自的原末行；后两行的单位积分非负，允许在上界中沿用原保守成本。每个字使用 ε/20，原 20 重求和只产生一次 ε。余整数 m=1 在大乘积侧确实被排除。

乘 log N/N 后，每个 p 的质量系数是 1/[p(ν−log_Np)]，以原 reciprocalMass 的 1/[(p−1)(ν−log_Np)] 从上控制。对原目标互素 p 区间取原 reciprocal_mass_limit，得到 J。此前的目标删除费用给无掩码几何族的同一上界。没有从两个上极限估计相减得到随 N 的未测试差值；原固定族 U* 只要求一个上质量 J。

## 稿内与形式化的剩余边界

- 固定几何、原常数、相对 Θ、全部目标删除与原整数上界属于本包给出的可补省略。ba6ec11d 的 global-positive-upper-completion-20261010.txt §1、§6–8 先给固定几何未测试质量假设，再用同一 ρ 的带号误差导出测试侧 limsup ≤K₀J。以当前 sharp、I_ν、J 和绝对误差 δ 实例化，该处没有附加种子/前代表前提。
- U* 的硬解析输入是原完整 M≈N 上同一实际 ρ 的带号分布，主项使用 X_W^(q)/φ(q)。实际五个以上素数位点、原 K₀ 密度、真几何与普通质量不能各自推出这条分布式。已有 P5zMixedMarkedPrimeFamilyActualBridge 的 p5z_eventually_mixedMarkedFamily_upper_of_actual_rho 入口要求同一系数的 hPP、密度和许可，并按两个固定秩接受输入。已有 all-rank 光滑类要求构造实际 ambient 权重。对本族接正式路线仍需把 5 至 200 的有限秩与原颜色标记同时送进同一实现，并付完整外逼近误差。sharp 的纯总乘积墙 M=N 应按 y=M/N 平滑。其余非恒定仿射墙按指数变量，薄径向尾用原 prime-product-radial-boundary-repair 的绝对质量估计。上述三项原稿有明确证明路线，本包并未形式化这次全族平滑或 P3 的谱、F、同 ρ 估计。
- 此边界只涉及同一经典 U3 正宽夹持根 Γ9–21。其余真实 ordinary seed terms、其他根/父字、原负项与前代反馈、1/50 和四轮完整 adopted generation、430+11 全细胞、row12 以及 7/2 根加权职责仍各自独立。没有把外 p 放进 Wu 因子窗或 β 所有者索引，也没有新设 hCells、hUpperInvoice 或测试计数前提。

注册表按安装顺序列出全部源码、原稿与直接入口的字节/散列来源。此前七源的 T09 独审采用另一份不可变白名单，此包单独送审。
