# Γ9–21 全部 20 个原标记的算术费用、同一物理密度和剩余分布项

**裁定。** 六份冻结源给出真正的单系数结论 selected_signed_only：对经典夹持根的大乘积 tested 计数，原保守 seed 价加任意 εΘ_clamp，再加一个未估的整族带符号 primeProductSignedError，是上界。之前的光滑外权、纠偏、小素数费和密度的身份在这个端点均已实例化。不需要额外假设 switched count 或 H430；该式本身不能去掉最后的 signedPP。

**全部显示模数。** 令 z=ceil(N^(19/96))。偶 N≥2 时 2≤z≤N。compiled_modulus_dvd 将每个显示的 d（包括零系数项）送入同一 sieveProduct(N,z) 的约数，不假定整个 Q 位于某个较小幂次内。原 divisor-mass/Mertens 估计在 p|d 上给总和 ≤C log N/(p−1)。物理空标签 beta 的单位幅值对同一个 R=rho 成立。每个非零 W 的真实位置 p≥N^(1/96)，完整 M≤2N；若 gcd(M,d)>1，至少一个实际位置 p 整除 d。对共有 k 个位置作上界并保留同值位置，得到单词单秩纠偏绝对值 O(N^(95/96) log N)。其中普通质量按 M 的 k^k 标记纤维给 ≤3N k^k，删除的仅是 W=0；没有将 M≥N 的外权删除，也没有把 ρ 替换成其正部来计密度或分布。

**真正的小素数。** T24 修订版的 smallPrimeMass_le 在 P=2N 的素数元组环境、目标 N 上使用，只对 M<N 且 N−M 为小素数的纤维计费。每秩至多 k^k ceil(N^(19/96))。先固定有限的 k≤200 常数，再计原词列表的 20 次出现及每词至多 201 个尾秩。绝对纠偏和小素数费在分 dyadic 矩形前一起支付：两种幂次都严格小于 1；给相应两个半预算后，以原原子区间正质量 (I/2)H_N≤Θ_clamp 对同一个夹持量付账。N 的阈值统一，未按素数或标签另假设 Θ 下界、亦未将普通壳的价格重复加入。

**密度与参数。** 几何选择先固定原 root,t₀,κ 和误差，再定正 h,δ,c。original_positive_family 的普通质量余量 γ/currentK 与原固定 J、η 属同一外权，利用普通质量非负，可乘实际密度上界。N/log N 与 singularSeries/log N 的积恰为 H_N。global currentK=8452171/1250000；保守的原 seed constant=681/100 只在此前已证的 switchCost 价格比较内。二者未混用。tested 价格和绝对费用分别取 ε/2。

Fine 终端只调用一次已有 exists_fine_same_rho_hdensity。m/r/n/e/a/q 及正、256|q、mesh 下界保留；etaPP、nu,v、betaMax、extra、任意正 fineTolerance 之后，先选同一个 β，再选 k。νβ²≤νβ 且 νβ²<νv=19/96 给 hL、hwL、hwz，故同一次 eventual even N 上有 HighAtoms、原 compiler 扣账、非零系数范围和 currentK 密度。分布项与密度均使用原 D=modulusFamily nu beta 0 N，R=coefficientFamily … 0 N。几何 μ=clampLevel root t₀ 是另一个量，不与当前 presieve ν 混同。

剩余端点是该 D、R 上全部原 20 个出现和尾秩的同一有符号误差，保持 2N 素数环境和 N 加性目标，含 M≥N 在同余及精确互素均值中的贡献。要由上式得到原 tested 纯价格，一个充分条件是对全部原词合计给任意小的上向 Θ 误差。这里没有证明这个估计，也不支付其它 Γ、整个 H430 或所有 430+11。源级独立验了六份数学源码、16 个声明、9 条直接 import 及四个外部直接来源，作者所列 44 个不同源/证据对象的 SHA、字节数、Git blob 均相符。未运行 Lean/Lake、guard、数值或 CI。
