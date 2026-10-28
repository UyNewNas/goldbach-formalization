# 第二批 medium_s1

新增 `Part3OriginalMediumS1ActualCoefficientBinding.lean`，254 行。只新增本目录文件；第一批与既有生产/草稿未改。没有运行编译、Lean、lake 或 checker。

本次完成第一批的真实系数实例义务。复用 medium_s3 已写的 canonical smooth/rough split 与真实固定窗 allowed 选择，证明每个 choice 的物理 `q2*q3=d*w`。同一个 `q2` 与完整 `d*w` 唯一确定 `q3`，canonical split 再唯一确定全部四个标记因子，故 choices 注入 `(d*w).divisors`。原始 `MediumAdmissible` 的 `gamma2` 和 `gamma3` 一界性给出 `|Lambda_d(w)|<=tau(d*w)`。没有把该目标界添加为假设，也没有丢弃重复素因子。

严格 small 与 inclusive rough 支持证明每个 occupied fibre 的 `coprime(d,w)`。由此可构造 `bindBlock`：保留原几何 FixedBlock 的 d/q/rough/alpha 载体，把 lambda 安装为真实 literal lambdaAt，把 q 平滑函数及其 Fourier 安装为已构造 `paperPsi`。实际 lambda 与原 `gamma2(q2)*gamma3(q3)` 的物理 slice 精确相等。q-majorant 一界性直接来自已有 `paperPsi_nonneg` 与 `paperPsi_le_one`。

有限支撑 cap 也从载体定义直接给出：`qCap=max(1,qHi)`，`roughCap=max(1,floor(2R))`，`physicalCap=qHi*d*floor(2R)`。最终 `bound_actual_boundBlock_kernel` 把第一批的固定 d 核预算接到这个实际绑定对象，消除了其所有系数与有限 cap 前提；alpha 质量仍直接取原始 admissibility 的 `2U`。

新明确的实现接口：第一批上游 `commonMCount` 用的是 `CommonSmoothCutoff.scaledDyadicCutoff`，原稿则要求 q 与 m 使用同一个 Gevrey psi。当前结果覆盖实际 literal lambda、q paperPsi 和正核预算；不能把旧 common-m 计数自动称作原稿 same-psi S1。下一步应补 paperPsi 的 common-m coprime counting，再与本次核预算连接。全局 dyadic atlas/ownership 和物理多项式 cap 到 log(x)^C 也仍待绑定。该差异属于实现未接通，没有发现新的原稿数学反例。

`complete_module=true`、`local_step_complete=true`、`task_complete=false`、`compiled=false`、`formal_credit=0`。精确导入路径与 SHA 在 REGISTRY.json；全部 held 源码依赖均不冒充已编译/已安装。
