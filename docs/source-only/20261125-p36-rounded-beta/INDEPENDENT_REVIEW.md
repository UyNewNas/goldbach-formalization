# Independent static review — rounded beta density reserve

**限定源码审查未发现数学范围或符号方向上的阻断。** 该候选仍未编译、未 kernel replay；本报告不构成形式化验收。审核对象为 `P3OriginalU5RoundedBetaReserve.lean`，11,370 bytes，SHA-256 `ee90e39b70a236142d602b9bff008d3ef6ddb3a4a13652d8ec6fae57e73ff17b`。

已独立重算 checkpoint 内所有文件的 bytes/SHA，并从固定 Git 对象及固定稿件原字节核对全部 20 条来源的 bytes、SHA-256 和 Git blob。源记录不是集成闭包；实际 main 选择与这些引用之间的字节差异另存 `INDEPENDENT_REVIEW_BINDINGS.json`，后续集成不得用较旧引用覆盖现有兼容修复。

## 三个定理的实际含义

第一定理只把已有 `coefficient_abs_le_one` 除以非负 totient 后求和，再调用既有 `P2ActualResidualUniverseMass.exists_mass_logRatio_bound`。完整 universe 的 Euler 展开和 Mertens 区间估计没有重复证明。`epsilon²≤r` 给实际 cutoff 次序，`2≤D^(epsilon²)` 给原区间界阈值；换底保留 `r/epsilon²` 与 `Krough/(epsilon² log D)`。

第二定理控制实际 signed attachment 的损失

\[
0\le V R_{\rm rounded}-D_{\rm rounded}
\le\eta\,\mathfrak S(N)/\log D.
\]

它调用旧 `physicalDensitySum_smallRoughRho_lower_error`，传入 beta-minus、beta-plus 的原顺序；物理 `smallRoughRho` 定义中的顺序也一致。对于负 rough coefficient，接 beta-plus 仍使该损失非负。证明没有假设 rough coefficient 或 beta-minus 非负。绝对质量只在误差项中使用，没有改变 signed 主项。

参数顺序正确：先根据固定常数、r、eta 和 `epsilonMax` 选 epsilon，再合并 scalar 与 sieve 的 D 阈值，之后才量化 D、N、enumeration cap、policy 和 tau。原 scalar 吸收定理先将指数 floor 选到 eta 以下，再令 D 增大；没有把固定 epsilon 时的正 floor 错说成零。Euler normalization 的阈值、正性和 covering cap 输入均明确保留。

第三定理令 `D=N^nu`，使用 `nu>0` 选择 N 阈值，以 `eta*nu` 调用第二定理，再用 `log(N^nu)=nu log N` 消去 nu。`epsilon²≤r` 与 `N^(nu*r)≤cap` 内部推出 small cutoff 的 cap 条件。声明中的三种幂、同一系数、rough density 和 physical density在该变换中保持一致。

## 范围与剩余义务

该文件给可用于原 U5 的一般参数接口。`nu=34/125`、`r=417/1360` 的数值说明与原 cutoff 一致，但本文件没有另写这个实际 U5 行实例，也没有声称已完成原 U5 density supplier。

这里仅支付 beta attachment error。`roundingLoss`、原 raw/full policy density 的定量识别、实际 mixed warm fibres 的 proper-wall 覆盖、outer-pair 平均、完整物理 family、tensor、(F) 与 PP 都未由这三个结论获得。普通 raw-policy 的 normalized error 定理没有被误当作 rounded rho 定理直接套用。

新增源码的有限比较与 scalar 实例化对应稿件 `sv:physical-lower` 的 absolute beta error。它没有新增数论输入、最终密度/PP 假设或证明捷径。实际形式化表达是否完全兼容当前 Lean API，仍须同源依赖选择下的严格编译、官方 replay、完整类型与传递公理清单确认。

本次审核未修改候选、checkpoint、canonical 源码、manifest 或远程状态；仅写本报告及对应独立来源绑定记录。
