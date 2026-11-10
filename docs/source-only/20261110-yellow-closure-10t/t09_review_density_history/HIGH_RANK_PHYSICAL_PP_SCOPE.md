# 同一物理系数的高秩模数与 moving-residue 接口

第 11 项和第 12 项合计的两个有限 `RealB` 上界都保留了 `realPhysicalDistributionError`。以下复核指出，当前已冻结 `d₊` 的整个非零系数支持不能直接交给原第 2 段「所有至少三个 rough 槽均已经压帽」的理由。这里审的是指定策略及分支接口。要判定最终误差估计，仍需实际外层族与完整求和上的分析。

## 最终目标、筛界与模数的量纲

`P4AOriginalNewFifthCounting.tree/coefficient` 明确用偶目标 `N` 作为 `DataPolicy` 的源尺度；`rho` 和枚举载体用 `N,N,w,N^(19/96),tau,L`，其中 `w=N^(nu*beta^2)`、`L=N^(nu*beta)`。`P4AOriginalNewFifthPaidDensity.exists_paid_density_and_count` 令 `v=(19/96)/nu`。`nu*v=19/96 < (1−kappa)b/(1+b)` 对应末端的 `ceil(N^(19/96))` 筛界，限制单个粗素数及 outer receiver 的最小素因子。`moduli N w` 是小素数支持与 rough 整数支持的乘积，粗部分可含许多小于筛界的素数。完整支持源码 `P4AFull87UnionPhysicalSupport.data_physical_range` 给出的上界为 `N^(599/1000)`。

`realPhysicalDistributionError` 在同一 `Q,rho` 上取 `m≡N (mod d)` 的 half-product 质量减去同源 coprime 质量除以 `φ(d)`。`manuscriptHalfProductCutoff κ N = 2 N^(1−κ)`，而 `mem_realHalfProductSource` 给出 `2N^(1−κ)≤m≤N` 及真实有序坏半乘积条件。原 distribution 稿中的移动余类 `T` 对应正式目标 `N`；PP 的 `x` 是此 `m` 的 dyadic 局部积尺度，`x≪N` 且有相应下截断。两个 `T` 记号在原稿与 Lean 中角色不同。

## 单个 M 分支的必要界

原 `current-eighth-distribution-interface-audit-20261009.tex` 第 1 段有四个 L23 不等式。将第一个写为 `Q₁/U < x^(−ε)` 并取七次，第二个 `U²Q₂Q₃² < x^(1−8ε)` 取三次，第三个 `|T|^σ UQ₁Q₂⁵Q₃² < x^(2−15ε)` 取一次。相乘后精确抵消 `U`，得到

\[
|T|^\sigma(Q_1Q_2Q_3)^8<x^{5-46\epsilon}.
\]

故任何由该分支一次分组覆盖的实际 `d≲Q₁Q₂Q₃`，在上述尺度都有 `d≪N^((5−σ)/8)`，其中 `σ=7/32`，上界指数等于 `Λ=153/256`。对固定 `δ>0`，`d>N^(Λ+δ)` 时 dyadic 常数对足够大 `N` 无济于事。此结论用的是 `x≪N` 和真的余类 `N`，对任意有效 `U` 及分组成立。

## 原料级系数能否为零

以下是按已冻结的原构造及原文给出的数学见证路线。没有对某个有限 `N` 作筛或数值试验。

1. 在最终 pre-`N` 顺序中，`a>0` 是先定的 coarse 第三激活指数，`e>0` 可以有理地取得足够小，使 `D=Θ−2e>Λ`，`Θ=299/500`。取最终允许的细网格，使第一个正宽半开第一槽的上端 `h₁≤19/96−4e`。给定这些量，选一个充分大的偶数 `m`，再选 `t` 使 `Λ/m<t<D/(m+1)` 且 `t<min(a,1/100,h₁)`；这可由 `m(D−Λ)>Λ` 及 `m` 任意大实现。取一个围绕 `t` 的开区间留出正余量，使 `m(t−s)>Λ+δ`、`(m+1)(t+s)<D`，并保持上述三个上界。最后的 `betaMax` 允许取得 `omega=nu*beta²<t−s`。`J0(omega)=ceil((599/1000)/omega)+3` 允许这个有限秩。
2. 沿偶目标 `N=2^n`，在该开区间内安排 `m` 个严格下降的互不交素数指数小区间。每个对应的自然数区间上下端比趋于无穷，Bertrand 定理即给足够大 `N` 下的互异奇素数。它们不整除目标，且全位于 `[N^omega,N^(19/96))`。第一前缀位于已通过的第一 coarse 格。第三素数小于 `N^a`，`HistoricalThirdCoarse.rawLevel_small_third` 给 `N^D`。`P1OriginalVariableFourthContinuation.seedExponent` 在自己的第三祖先上冻结；`P1ThirdFallbackSupport.supported` 要求这次粗激活。故 `DataPolicy.active` 为假，第四、第五分别走 `exponent4/5`，第六走 `currentSixthExponent`。`lambda3` 取 max，第四、第五 `finiteMax` 含继承 seed，`DataPolicy.fifth_le_current` 保留它，第六实际帽至少为 `D`。八阶候选原 source 要求 `t₃>1/100`，这里没有选中新八阶。`common3` 包含 `old3`；在不超过第三秩时原初始帽允许各自前缀。
3. 每个前缀的总 log 积至多 `m(t+s)`；任意上筛奇数位置 `j≤m−1` 的立方检验至多 `(j+2)(t+s)≤(m+1)(t+s)<D`。因此递减词的所有选中祖先（包括继承旧立方）均通过。原始 complete rough 积 `d` 平方自由、偶数个不同素因子，原保留系数是 `+1`。对任何给定 tag/τ，`P4AUpperTaggedParityCompiler.raw_le_coefficient` 与 `coefficient_abs_le_one` 迫使实际正 ANY 编译值为 `1`。取小因子为 `1`，它属于非零 small prime product 的因子集。`P4AUpperTaggedBetaAttachment.rho_at_product` 与 `SmallRosser.upperWeight_one`（`L>1`）给出同一物理 `rho(1*d)=1`；唯一 small/rough 分解排除了求和抵消。也就有 `d∈moduli N w` 与 `d>N^(Λ+δ)`。这是物理系数支持层的见证，与证明某个产品计数误差有多大是两项不同的事。

原 distribution 稿第 2 段把第三 activation 阈值取为实际 presieve `w`，以便所有至少三个 rough 槽都受 `Γ_B−2e≤Λ−2e` 或后续被选中且低于 tent 的 cap；低 rough rank 自有 BV 路线。冻结 formal 构造的 coarse `a` 和后来可任降的物理 `omega` 形成上述严格的内部区间，因而仅改半开边界约定不能处理它。

## 可得结论与仍需证的范围

这给出对「已冻结 d₊ 的所有完整非零模均可按该高秩 M 条件分组」的源级反例路线。原第 6 段还按实际 HB 外层分解选择 medium 槽或一长/两长的其他分支。`W_N` 受原正光滑几何族、原 group support、roughness、radial gate 和 SW 条件限制。`rho(d)≠0` 没有单独证明某个特定 Geometric `W_N` 的 medium 图块一定有非零最终贡献，亦没有排除其它估计、重组或独立的总量支付。没有由此获得 `realPhysicalDistributionError` 的下界、原筛定理或原论文的反例，亦未证明对任意事先指定的一套最终政策参数必发生这一见证。结论适用于当前 cofinal 接口允许上述 `betaMax` 选择的策略族。

恢复原 PP 消费者须在真实第四/第五/六/八及第一/第三历史上给出满足原分组许可的共同构造，或证明未许可组在同一权和、同一可用 reserve 上可忽略，或提供其真实替代估计。两种有限 counting terminal 继续以其显式 distribution 项为有效的部分结论。本次为独立原文与源码审查，无构建、有限 guard 或算例执行。
