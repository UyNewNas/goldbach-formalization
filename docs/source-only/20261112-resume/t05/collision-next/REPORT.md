# 完整粗模数的平方碰撞

原稿 `distribution-prime-product-completion-20261010.txt` 第 3 节第 119–149 行先在原系数中保留全局平方自由条件，再为分布误差移除此条件。第 1、2、4 和 10 节确定原同余与互素均值、局部长度、频带及计数次序。本包给出这一移除步骤在当前真实模数上的源代码。没有新增数值输入。本次核对限于源码与字节，Lean 尚未经编译。

## 同一物理系数

`Params.rho` 就是有限高低区策略 `P4BOriginalFiniteSmoothCount.coefficient`，采用既有 `bank m`、当前 `data e q a`、原 `omega` 与同一对 β、k。分布侧从 `wholeHigh = Q ∖ activeLow` 出发。原低模数的绝对费用、低粗秩费用和取消人为完整模数切割已由前件支付。这里的一切分组作用于完整原子。

`P4BOriginalCollisionPhysical.physical` 对任意实值算术试验严格相等。每个非零粗项经 ALL/ANY 的原始代表落入一个半开词；每个小部分用原 Rosser 正、负两种 β 中相应的一种。粗项的降序素数列唯一决定词，原物理模数具有唯一的小、粗分解。`supported_physical` 从这一等式恢复非零高秩模数的真实记录并用其原完整端点，再以原短粗秩界处理其余非零物理模数，得到严格的 `d < N^(599/1000)`。

`P4BOriginalCollisionTensor.grouped_eq_free` 以未施加平方自由限制的有序素数组表达粗部，保留整词标量 `boxScalar/M_J` 和奇偶号。原三组由 `slots` 在每个整词及给定长度参数 x、U、η 上选定。`ownerHead_at` 核对真代表的标签键。实现复用已有 `actualNormalizedPrimeTupleCoefficient`，以每组总槽数的阶乘作除数，再将三者原数乘回外部标量。原稿写成每组内各标签出现次数的阶乘乘积。两个归一化给出同一未归一化整数卷积，本实现对较大的外部恢复标量提供独立上界。`P4BOriginalCollisionThirdFactor.gamma_one` 以小、粗素数支撑互斥将 β 并入第三组，适用于每个整数。`gamma_range` 保留真实第三组端点和小因子费用。`row_tensor` 直接给出完整复同余行与这三个独立算术因子的相等式，保留原 (N\bmod d) 和互素均值。对固定 ω、τ，`restored_mass` 的上界是 `#master(omega,tau) * (J0(omega)!)^3`，独立于 N、长度选择、各 HB 角色、频率及试验函数。

## 全局平方碰撞的实际费用

- `P4BOriginalCollisionWords.Params.full_cap` 用同词原 raw 代表的严格 `N^0.598`、每一槽上端点的最大膨胀及真实小因子 `h<N^ell`，为包含重素数的每个不受限完整记录给出 `h·prod(ps)<N^0.599`。
- `P4BOriginalCollisionTensor.error_support` 与 `error_bound` 按完整模数聚合。所有非零差项都满足某个粗素数 `p≥N^omega` 的平方整除完整模数；涵盖同组及跨组碰撞。同一完整模数确定唯一小因子和唯一粗素数多重集。其全部词、全部原记录的总差绝对值至多 `J0(omega)!`。
- `P4BOriginalCollisionKernel.full_difference` 先按完整 HB 整数乘积收集绝对量，再用每模数的 `Y/d + 1 + Y/φ(d)`，其中 `Y=⌊6·countingScale(N)⌋`。同余纤维按整除商注入，完整乘积恰等于 N 计入中间的 1。互素指示符保留到取绝对上界时。这里只使用原有粗平方预算及正幂支付。
- `P4BOriginalCollisionModes.exists_mode_cost` 对每个真实 HB 角色和每个实频率成立。至多 12 个槽产生 `L^12`，其中 `L=logScale(countingScale N)`；真实整数乘积纤维由固定阶除数幂控制。空补纤维按既有完整反演规约删除，活纤维的一个整数给出全纤维完整尺度。
- `P4BOriginalCollisionRetained.exists_band_power` 对真实截留频带积分，支付原混合导数 `s^-24`、全部母图表/角色 `L^14` 及补纤维 `L`。沿 `s=1/(⌊log N⌋+1)`，两个完整有符号频带之差的范数至多 `C(omega,epsilon) N^(1-omega+epsilon) L^51`。频率积分的次数与同余均值的次数都保留于原位置。

## 计数出口及次序

`P4BOriginalCollisionPayment.eventually_collision_paid` 取任意固定 `omega>0` 及任意 `eta>0`，对全频带一次支付至多 `eta·singularNormalization(N)`。N 的阈值可依赖预先固定的 ω。形式中保留每个合法 K、A、κ₀、ζ 和每套符合预算的物理参数。

`P4BOriginalCollisionPayment.exists_RealB_le_free_band` 先由原稿条件选一次正 κ₀，再固定 K、η、ν、β，其中 ω=νβ²。对最终偶 N、同一组 m,r,n,e,q,a,k 及实际细度，所得为

```text
RealB(b,N) ≤ X_s · physicalDensitySum(Q, rho)
            + Re band(b, kappa0, N, K, 0, kappa0, zeta, products, free)
            + eta · singularNormalization(N).
```

同时保留 (X_s\ge0) 和 (X_s/(N/\log N)\to\log(1/b)) 的同一精度形式。原计数及新碰撞各用 η/2。Fine 原接口的 `extraPPMargin=1/2000` 放在 β、k 之前，产生 `nu·beta < (1/2000)/32` 及 `tau·(J0+1)≤1/2000`；`fine_budget` 从这两项导出完整模数需要的预算。终端自行导出非零物理支撑。既有同一系数的密度、编译开销和原 22 槽付款仍由 Fine 原接口提供。这里的 ω 固定早于最终 N，原外宽沿指定序列随 N 变化。

## 余项

`band(products,free)` 仍是实质算术项。它含两张实际图表、所有角色及完整频带上的原测试。中档分支须对每个有贡献的整原子补足真实 (M) 三因子尺度和适用的辅助 SW 输入，低首坐标的第五、第六层及第八层局部所有者的资料仅覆盖其已证明区域。P3 的绝对 7/32 同源积分估计仍待供给。无中档的一或两个长槽还需相应粗投影、合数均值与端点付款。本包只处理最终物理矩形上界系数；原稿其他带标记的原始卷积族仍需其自身标记重数。尚不能由此给出全 PP 或最终 1+1.7482。

`REGISTRY.json` 登记八个候选源、逐一直接导入、稿本与原算术入口，以及上次已经审查的 Fourier 行选版。
