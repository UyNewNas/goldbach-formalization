# pp_twolong：实际 Mellin 长变量模态

已交付 `Part3TwoLongLiteralMellinModes.lean`（闭合源码，未编译，正式验收信用 0）。分配的大任务仍未全部完成。

核原稿后的关键修正：原稿 §4 用在整个 dyadic rectangle 上等于 1 的紧支集 cutoff；§7 明确长变量 C² profile 支持 `[1/2,5/2]`。前稿 `Part3TwoLongSelectedModeWindow.Mode` 仅允许支持 `[1,2]`，其条件定理可用，但不能构造在闭 `[1,2]` 两端仍等 1 的连续 cutoff。本次沿原稿正确的扩大支持构造实际 profile，属于接收器限制的修正，没有发现原稿证明缺口。

采用 Mathlib `ContDiffBump`（中心 `3/2`、内半径 `1/2`、外半径 `1`）直接构造固定 cutoff，避免重造 bump 基础理论。证明它在 `[1,2]` 等 1、支持 `[1/2,5/2]`；`twist(t,x)=cutoff(x) exp(i t log x)` 全局 C∞。零点附近 cutoff 恒零，所以没有越过 log 的奇点。代码导出实际一、二阶导数，并得到

`N2(twist t) ≤ L0 + L2 + 4 L1 |t| + 4 L0 (|t|²+|t|)`，

其中 `Lj` 是固定 bump 的真实 L1 导数积分。频率 `|t|≤H` 时给出固定 `C(1+H)²`，两个长模态的有限加权总质量至多 `C²(1+H)^4 Σ|alpha|`。没有以频率点个数或 cube 体积收费。

同时给出正确的 `ceil(5A/2)` 有限长窗口、literal AP count 与 `1/phi(q)` exact coprime mean 的同系数恒等式。实际 HB 的 `Owns b (d*u)` 推出 `u/(lower(b)/d)∈[1,2]`，因此实际 owned 点上新 cutoff 不改变模态，端点也保留。`selected_fourier_mode_exact` 把任意实际 Fourier 系数和短坐标相位，精确拆成同一个 q 无关短 amplitude 与这两个实际 smooth profiles；`selectedAmplitude_norm` 证明短相位不增加幅度。

未声称这些点值恒等式等于完整 sharp/upper/gap core 的全域重构。全 Family 的实际 compact log-chart、连续 Fourier 积分换序及 N2 质量、smooth sandwich、三种 Brun core equality、外部 P1/P2、same-rho PP/HB 完整绑定与 full E4 都仍开放。尤其没有把每个 core 的 P2 上界当作新假设来冒充已完成的内部推导。

精确导入及前驱 SHA256、原稿锚点和全部剩余项见 `REGISTRY.json`。源码审阅仅限静态逻辑；按任务要求未编译、未做数值检查，也未做额度检查。
