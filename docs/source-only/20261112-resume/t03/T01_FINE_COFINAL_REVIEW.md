# 精细网格与 All22 同系数端点独审

**使用端的源码数学通过。** 选定 T01 的 `P4AOriginalFiniteAll22FineCofinalCoefficient.lean`，SHA256 为 `74f2d4dc15e059f9ab197157ee9172808ddb34d2547dc85733eec878e1fbc3b6`。其中第 36 行的 `exists_fine_cofinal_same_coefficient_density_and_count` 同时给出调用方指定的五个精度约束、同一系数的高区几何、All22 密度和保留分布误差的计数界。T02 的精细网格供应已由 T09 独立审过，本次核对的是调用参数、真实系数以及每个结论所用的阈值。

## 一次精度选择

从 `Nineteen.exists_final_raw_upper_with_early_defect` 取正的晚截断上限 `h` 和十九槽 raw 估计，从 `EarlyFinitePayment.cofinal_actual_early_defect` 取前三槽付款。分别使用 `eta/2`。在同一 `m,r` 上取两个 `n` 下限的最大值，再取两个正的缓冲上限之最小值作为 `E`。给定正有理 `e<E` 和 `0<a≤1/800`，早期端点在十九槽的 `q0` 之后选单个 `q`，满足 `256∣q` 以及任意预定 `qMin,mMin` 的两个约束。这时已有早期目标阈值 `NE`，对所有 `omega≤a` 统一成立。

随后才输入 `0<etaPP≤gap m (data e q a)`、`0<nu,v`、`nu*v=19/96`、`betaMax>0`、`extraPPMargin>0`，以及在正实数上处处为正的 `fineTolerance`。实际 `gap` 是 `min (slack m) (e/32)`，对所选正 `e` 有原有正性定理。第 98 行调用一次 T02 的 `FinePPSchedule.joined`，传入原 `bank m`、它的有界性证明、`min etaPP extraPPMargin`、`min betaMax (h/nu)`、原 `compilerReserve` 和真正的 `fineTolerance`。普通合流源只提供原物理上界 `upper` 的定义。

对这一对 `beta,k`，令 `ell=nu*beta`、`omega=nu*beta²`、`tau=alignedWidth (jointIndex (bank m) (data e q a).m) k`。由这一次选择的两个最小值得到

- `ell<etaPP/32` 且 `ell<extraPPMargin/32`。
- `tau≤fineTolerance beta`。
- `tau*(J0 omega+1)≤etaPP` 且 `tau*(J0 omega+1)≤extraPPMargin`。

同时有 `0<beta<1/8`、`beta<betaMax`、`beta²<v`、`omega<a`、`ell<1/1000`。`beta<h/nu` 与 `beta<1` 给 `omega≤ell<h`，`beta²<v` 与 `nu*v=19/96` 给 `0<omega<thirdPrefixRho`。这些是十九槽 raw 导出的全部晚截断前提。固定该 `omega` 后才取得 `NR`，最终 `N0=max NC (max NR NE)`。此后只量化 `N≥N0` 的偶目标。

## 同一个系数的付款与几何

第 137 行的干净 raw 界由该 `N` 的十九槽误差 `eta/2` 和实际 `lowerEarlyDefect<eta/2` 推出。第 144 行使用 `N≥2` 的手稿归一化等价。第 148 行的 `reserve_raw_is_actual_final` 识别最终 `F`、`cap=N`、`z=N^(19/96)` 上的原 raw 系数。原精确预算恒等式只加入一份 `compilerReserve`，得到与普通合流相同的 `upper`，其中保持 `densityReserve`、`exactSlack` 和同一 `F,N,N,N^omega,z` 的真实预筛修正。

第 161 行直接调用已有 `high_atoms`。其所需的正 `width r`、非负 `e`、`N>1`、正 `omega,tau,etaPP` 和 `etaPP≤gap` 均在这组参数成立。`ell≥0`，且 `ell<etaPP/32` 给 `2*ell≤etaPP/16`。`tau*(J0 omega+1)≤etaPP` 用的是同一个 `k`。展开 `HighAtoms` 和 `FiniteFallbackPolicy.rho`，二者均取相同 `F`、空标签、`N,N,N^omega,z,tau,N^ell`。每个非零模数有原始代表与分解，几何不等式另带原定义中的前三素数、高于 `mu`、局部尺度及 `U` 假设。

编译费、非零支持 `d<N^(599/1000)`、整数计数均来自这一系数。真实 `RealB` 的上界在原 `b,T` 门下乘以非负的源基数，原样加上 `realPhysicalDistributionError b N T Q rho`、`ceil z` 与 `T+1`。各精度约束给未来的 PP 估计提供同一系数的参数，整体有符号分布误差仍需付款。

此次核对了作者登记、三个直接导入、原 raw 与 early 端点、实际 `rho` 和 `HighAtoms` 定义、预算与归一化接口。两个固定公开树 `eea9486f` 与 `2798513f` 均未含 T04 的 `HIGH_PP_REGISTRY.json` 所列 14 个同名模块。新使用端和 `FinePPSchedule` 在这份原作者清单的导入链中触及 12 个模块。白名单逐件给出这 12 个已有源的原件指纹和安装目标，另两个是 `GroupedAtoms` 和 `JointHigh`。安装还需沿用已审 R17、FullPolicy 和两处 List 记号选择。所有结论均为源码范围，整图安装、实际守卫、Lean 核验和传递公理审计尚待执行。[精确选择清单](T01_FINE_COFINAL_ALLOWLIST.json)
