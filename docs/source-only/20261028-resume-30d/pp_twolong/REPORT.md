# pp_twolong 第四批：真实定量条带与未供应内部 P2 的条件接收器

交付三份源码，第三批保持冻结。完整任务仍开放；本地必要步骤闭合，未编译，正式信用 0。

先纠正一个定量推断边界：第三批的变量半径 `ContDiffBump` 能给真实 C∞ 支集/夹逼，但其 `rOut/rIn` 随 delta 变化，Mathlib bump 类没有提供该参数族的统一导数界。因此没有把第三批 C∞ 自动升级成 `N2=O(delta^-2)`。本次改用项目中已经存在的 `P4BSmoothStepDerivativeBudget`：其真实固定 `Real.smoothTransition` 在每阶给出先选常数、后变宽度的 `width^-k` 估计。

新 upper 是两份 affine smooth upper step 的乘积，新 endpoint gap 是端点两侧的同类固定 transition。代码证明实际一、二阶 jets、`(1,2]` 的严格左端点夹逼、rectangle error、统一 `[1/2,5/2]` 支集，并由固定长度支集和真实二阶导数界推出：

`D=2B2+2B1²`，`N2(upper_delta) <= (2+2D)/delta²`，`N2(gap_delta) <= (4+4D)/delta²`，对所有 `0<delta<=1/4`。

第二份 `FixedMP2 constant` 是原稿尚未形式化完成的**内部**逐固定 m P2 的精确 universal 接口：它对所有紧支 C² f/g、正 U/V、primitive a、q>0、任意固定复振幅 alpha 断言原始 complete-product AP count 与 exact coprime mean 的差，代价是 `C |alpha| N2(f)N2(g)[sqrt(q)tau(q)+tau(q)^2/phi(q)]`。该接口没有 HB/rho/E4 字段，源码没有新增 axiom，也没有构造该经典定理的证明。P2 是原稿由 P1 double periodization、composite Weil/Ramanujan 输入实际推出的内部结论，必须继续保留在当前内部证明链，不能外置或延后。本文件仅把这个未供应内部接口作为条件定理参数，没有消除 P2 证明义务。

在此未供应内部 P2 接口的显式条件下，代码实际构造并核查 upper-upper、gap-upper、upper-gap 三 profile 的 C²/支集/N2，代入正 Brun 尺度 U/d1、V/d2，写出有限 same-rho Brun E4 型条件推论：常数 `C gapCost²/delta^4` 乘 Brun 系数/short amplitude 的 L1 质量及物理 rho 的 composite-P2 模数预算。这只说明在内部 P2 已证明后如何调用实际 profile；不能把该条件推论计为 P2 或原 E4 完成，也不应通过同一 hP2 接口重复包装来增加完成信用。

第三份 `Part3TwoLongInternalP2FrequencySums.lean` 继续实际证明 P2 内部所需步骤，全文件没有 `hP2`。复用项目已有真实 Poisson telescoping 供应，而不是重造证明；经精确 `d/H` 换元，得到所有 `H>0`（含 `H<1`）的非零 d-倍频总质量 `<=2H/d` 和双坐标质量 `<=4HK/d²`。还证明 composite Weil 的 sqrt-gcd 因子可由实际共同除数 sqrt 权重有限和控制，`sqrt(d)/d²=d^(-3/2)` 的 Mathlib p-series 收敛给出与 q 无关的固定 Weil 常数，totient 除数质量 `<=tau(q)` 及双 Ramanujan 频率质量 `<=4HK tau(q)^2`。这些是真正消除的内部 elementary 义务，没有把 P2 作为前提。

内部 P2 本体仍需 exact P1、两条频率轴抵消、filtered 整数频率到 `j=d*k` 的重索引、实际 Fourier decay 和 UV/q² 尺度装配。已证 elementary 预算不能被直接叫作 P2 完成。

尚未把这三份新 profile 与原始 HB Fourier 模态在扩大支集上完整识别；当前 P2 实例化覆盖这些实际未扭曲平滑轮廓。它们乘 retained Mellin twists 的统一频率成本、连续模态重构、实际 rho/Brun 外壳到 x-dependent E4、原稿内部 P2 推导、N1/条带 L1 量化与最终 PP 转移均准确保留。未发现新的原稿缺口。

精确 source/import SHA、常数及所有剩余义务见 `REGISTRY.json`。未运行编译、checker 或额度检查。
