# medium_s1 源码交付

新增 `Part3OriginalMediumS1SeparatedDivisorMean.lean`，424 行，17 个 theorem 与 1 个定义。文件文本闭合；未编译、未执行 checker、正式证明增量为 0。原分配任务仍有实际家族实例绑定，故 task_complete=false。

证明主线是保留原稿两份不同的物理 totient：`phi(q*d*r)` 与 `phi(q*d*s)`。复用既有有限 reciprocal-totient 对数预算后，真实正核逐点成为

`4*A²*L_P² * (tau(d)^3/d²) * (tau(q)/q²) * (tau(r)^2/r) * (tau(s)^2/s)`。

这一步使用的是原稿 pointwise `|Lambda_d(w)|<=tau(d*w)`、`|psi(q/Q)|<=1`、两份实际 alpha coprime mass<=A。它们不是 S1 remainder 或 aggregate moment 前提。`actual_alpha_mean_bound` 已直接从原始 `MediumAdmissible` 取 `A=2U`，没有更换 alpha 区间。

随后保留实际 `q>=q0>=Q` 与 `d>=D`，再扩大剩余均值。复用当前外部库中已经可达的 `fouvryTau_two`、`fouvryTau_mul_le`、`sum_fouvryTau_div_totient_le_real`，得到 tau_2/tau_4/tau_8 的普通全整数均值支付；不把它们改成 squarefree 版本，也不使用 pointwise x^epsilon。结论 `S1DivisorKernel_family_le_log` 是整个有限 d-block 的

`Σ_d K_d <= 4*A²*L_P²*L_Q^4*L_R^16*L_D^16/(Q*D)`。

`S1ActualRemainder_family_le_kernel` 把上游 common-m 的同一个绝对常数带入整块真实 signed remainder。将两条结论组合后就是明确的 ordinary divisor-mean 支付；从未对每个 d 调用一个任意对数精度的黑盒 remainder。

尚缺原稿的实际 `d -> FixedBlock` 构造、literal Lambda 定义到 pointwise bound 的实例、q cutoff 一界性实例，以及将 P/Qcap/Rcap/Dcap 的固定多项式界和 Y=QD 接回 log(x)^C。这里已消除多变量除数均值本身的推导义务，尚未声称原稿完整 S1 或 medium 已闭合。没有发现新的原稿数学反例；剩余属于接口/实例形式化。

依赖精确 SHA、导入安装对应与原稿行锚点均在 REGISTRY.json。唯一 held 导入 `Part3OriginalMediumS1WeightedRemainder` 必须按其原注册依赖安装；生产路径上的 P5RoughSquareWeightedBudget 本身标有 source-only，不能把路径存在解释为已验收。
