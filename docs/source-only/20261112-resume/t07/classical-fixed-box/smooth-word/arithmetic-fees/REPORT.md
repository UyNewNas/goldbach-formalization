# 经典 U3 原夹持种子的同系数算术费用

六份源码把整族 Γ9–21 的原 20 次出现接到实际 Fine 筛程。入口为 `Part5OriginalH430ClassicalSmoothFineSelected.selected_signed_only`。对固定原 root、t₀、κ 和任意 ε>0，先选整族外宽 h、δ、c，再按原 cofinal 次序选 m、r、n、e、a、q 和 Fine 的 β、k。最终原偶目标 N 上得到

$$
  C_{\mathrm{tested}}(N) \le
  (\mathrm{switchCost}+\varepsilon)\,\Theta_{\mathrm{clamp}}(N)
  +\sum_{\mathrm{原词出现}\;c_s}\sum_{r\in\mathrm{tails}(|c_s|)}
   \mathrm{primeProductSignedError}(k_{c_s,r},2N,N,D,\rho,W_{c_s,r}).
$$

右端公用 Fine 选中的 D、ρ。ρ 的参数是 canonical bank m、round r、分辨率 n、原 e/q/a、ω=νβ²、N、对齐宽度 τ 及 L=N^(νβ)。真测试为 M<N 且 N−M 为素数，模数、同余均值和互素中心在完整 M 支撑上求和。根的冻结指数是独立的 μ=clampLevel(root,t₀)。同一个完整元组按 p、原带色 q、非降尾素数排列。原子积 M 含 p。原字列表中的相同词仍分别求和，系数符号保留在最后一项。

## 全显示模数上的互素修正

原 `moduli N (N^ω)` 保留 beta-small 支撑与 rough primorial 全约数的乘积，显示集合可含零系数的大模数。原 `compiled_modulus_dvd` 证明每个显示 d 整除同一筛积，`rho_abs_le_one` 给原 tagged beta 的单位幅值。设 z=ceil(N^(19/96))。偶 N≥2 上有 2≤z≤N。P4BPrimorialDivisorEnvelope 的 `prime_divisible_reciprocalTotient_le_divisor_mass` 与 `exists_sievePrimorial_divisor_mass_le_log` 给单个素数槽 p 的总费用 ≤C log N/(p−1)。对实际 W 非零的每个槽均有 p≥N^(1/96)，真完整 M≤2N。从乘积不互素推出某一原槽整除 d，故 k 个槽的并包费用 ≤2Ck log N/N^(1/96)。该步保留相等素数出现在不同位置时的费用上界。

原 `p5z_markedCoprimeCorrection_eq_neg_sum` 在同一组 D、ρ 上给出负的非互素总和，取绝对值后使用这个槽费用。为了求普通质量的粗界，只删除 W=0 的元组。按原完整 M 的带标记推前，逐个纤维的原界为 k^k。每秩 W≤1 且 M≤2N，故普通质量 ≤3N k^k。得到共同的每秩修正 O(N^(95/96)log N)。这个估计不依赖全部显示 d 具有多项式上限，也不使用正在证明的 H430 计数。

## 原小素数费用及物理 Θ

T24 revision-02 的 `smallPrimeMass_le` 将 cap P=2N 与目标 N 区分，原小素数测试仍要求 M<N。每秩费用 ≤k^k ceil(N^(19/96))。原 20 次出现、每词至多 201 个尾秩，全部 k≤200。两项合并前固定公用的有限秩常数；取两个 ε/2 并使用已有的 `eventually_powerLog_le_singularNormalization`，一次吸收整族绝对费用。阈值同时适用于全部满足几何界的宽度以及全部实际策略、beta 参数。原 `uniform_clamp_witness` 的正区间质量把 H_N 转回同一个 Θ_clamp。没有逐小格或逐素数假设正质量。

## 原种子价与实际 Fine 选本

上一组选本的 `original_positive_family` 给普通质量的上极限 J+η、归一化余量 γ>0 以及旧种子价。普通原权非负，故同一 ρ 下的真实物理密度上界可乘以实际普通质量。取普通极限精度 γ/currentK，再用 `sourceMassScale_mul_densityScale` 将 N/log N 与 singularSeries/log N 的积精确化成 H_N。两份 ε/2 分别支付原价和上述算术费用。currentK=8452171/1250000 与原保守种子内 K_seed=681/100 角色各自沿用此前选本。

T01 的 `exists_fine_same_rho_hdensity` 是实际共同选择。其原 cofinal m/r/n，原 q 的下界、正性、256 整除和 refinedMesh 下界，原 etaPP、βMax、extra、fineTolerance 的选择，以及 β、k 三个宽度费用均在本终端保留。同一目标 N 还保留 HighAtoms、compilerExpense、真实非零模数 d<N^(599/1000) 以及 physicalDensitySum≤currentK·singularSeries/log N。所有这些输出与末项的 ρ 来自同一次选择。这里的密度上界和整数算术费用均已接入，不需要另选系数或把整个目标表达式列作前提。

## 仍须支付的原始估计

要把这 20 次 tested 正项计到原种子价，仍须对上述实际同一 D、ρ、全部原 W 证明上向的带号 PP 总和 ≤任意小的 Θ_clamp 误差。原词的实际 M>N 外延也须保留在同余与互素均值中。其它种子项、增强根、前代反馈、完整 430+11 细胞与 row12、7/2 根系数仍从各自的原前提接入。本包使用了前 15 源的第二选版，以及 T24 和 T01 的独审选版。六份新源仅经静态核对，未执行 Lean、守卫、数值证书或 CI。

