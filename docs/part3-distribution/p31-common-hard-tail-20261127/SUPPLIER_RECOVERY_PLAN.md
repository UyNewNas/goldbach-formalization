# P3.1 共同 J 硬尾：原供应者恢复接口方案

固定基线：`UyNewNas/goldbach-formalization`，`092d7b48f470c2733308853e5ec42bf46463fc3c`。此方案只恢复供应者，不修改已有源文件、consumer、verifier 或 Git 分支；不运行 Lean、云端编译或推送。

1106 冻结稿来源为 `UyNewNas/chen-imbalanced-semiprimes` 提交 `a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en/analytic-appendix.tex`，SHA256 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`，对应 700–703 行共同截断及普通光滑 Fourier 尾估计。

## 1. 当前 owner 核对

恢复前已在当前源码中检索下面 21 个声明，未发现已有同名声明。已有的 `frequency`、`kloosterman_norm_le`、Schwartz cutoff 及其 rapid-decay 定理、`completedKernel`、`Source`、`weight`、`output`、`weighted_pushforward` 一律使用当前 owner，不重新声明。

当前 owner 入口：

- `Part3PhysicalSmoothReciprocalPoisson.lean`：实际完成频率与 Kloosterman 平凡界。
- `Part3CommonSmoothCutoff.lean`：实际 Schwartz cutoff 及衰减。
- `Part3OriginalCommonPoissonKernelLanesCore.lean`：`ActualCompletedSquarePushforwardSourceOnly.completedKernel`。
- `Part3LiteralReciprocalSource.lean`：实际有限源、权重、output 及 weighted pushforward；该模块已导入当前 completedKernel owner。

## 2. 拟新增模块、imports 与声明

### 2.1 `ImbalancedChen/Part3PoissonNonzeroDecayCore.lean`

Import：`ImbalancedChen.Part3CommonPoisson`。

保持原 namespace `ImbalancedChen.Part3.CommonSmoothCutoff`，恢复六条：

1. `poisson_decay_step`
2. `poisson_decay_sum_range_le`
3. `poisson_decay_summable_nat`
4. `poisson_decay_tsum_nat_le`
5. `poissonNonzeroDecay`
6. `poissonNonzeroDecay_summable_tsum_le`

原来源 `Part3SmoothProgressionError.lean`，blob `292a7bddc202d6c4c3795de288b053df0b55ca5c`。不恢复该文件后面无关的 progression-error 结论。

### 2.2 `ImbalancedChen/Part3PhysicalCompletedFrequencyDecay.lean`

Imports：`ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson`、`ImbalancedChen.Part3PoissonNonzeroDecayCore`。

保持原 namespace `ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b`，恢复：

1. `frequency_norm_rapidDecay`
2. `frequency_summable_norm`
3. `frequency_summable`

原同名文件 blob `626e6417fbf7505307e958201f933b15eb672d82`。原 import `Part3SmoothProgressionError` 替换为最小六声明 core，声明与证明正文保持原字节。

### 2.3 `ImbalancedChen/Part3PhysicalHardSchwartzTail.lean`

Import：`ImbalancedChen.Part3PhysicalCompletedFrequencyDecay`。

保持上一模块相同原 namespace，恢复：

1. `hardOmitted`
2. `frequency_hard_window_tail`

原同名文件 blob `a32af63a6fc6d2ca67c35256b0c533214aef04a0`。

### 2.4 `ImbalancedChen/Part3PhysicalCommonHardFrequencyWindow.lean`

Import：`ImbalancedChen.Part3PhysicalHardSchwartzTail`。

保持相同原 namespace，恢复：

1. `commonHardWindow`
2. `zero_mem_commonHardWindow`
3. `outside_commonHardWindow_frequency`
4. `frequency_common_hard_window_tail`
5. `frequency_common_hard_window_tail_cap`

原同名文件 blob `a5d68cef6f7b9fded140b687e8de75f29b3239c4`。

### 2.5 `ImbalancedChen/Part3ActualCompletedHardTailCore.lean`

Imports：`ImbalancedChen.Part3PhysicalCommonHardFrequencyWindow`、`ImbalancedChen.Part3LiteralReciprocalSource`。

保持原 namespace `ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b`，恢复原文件前三个定义及前两个定理：

1. `hardCompletedKernel`
2. `hardSourcePiece`
3. `sourceAbsMass`
4. `completedKernel_common_hard_tail`
5. `source_common_hard_tail`

原来源 `Part3ActualCompletedHardTailMass.lean`，blob `b23e2e000301008244372e076411750ad4daa2bb`。不用原文件的 `ActualBetaNativeSource`、`ActualModeJointBetaPositiveCount` import，也不恢复实际 mode 系数范数和 rawLabelBudget 结论。删去只服务于后半文件的 namespace opens，使用当前 Source/completedKernel owner。

## 3. consumer 可依赖的精确契约

`commonHardWindow C M R` 是闭整数窗口，半径为 `Nat.ceil (10*C*R/M)`，包含 m=0；不额外引入 eta。

`source_common_hard_tail (r : ℕ) (hr : 2 ≤ r)` 先给出一个正实常数 A，然后对所有 C>0、M>0、R>0、任意 N、a、有限源 U 和系数 lambda/omega，结论为：

```text
‖(∑ s ∈ U, weight lambda omega s * completedKernel M N C a (output s))
    - hardSourcePiece U lambda omega M N C R a‖
  ≤ (A*C^2/R^(r-1)) * sourceAbsMass U lambda omega.
```

`sourceAbsMass U lambda omega = ∑ s ∈ U, ‖weight lambda omega s‖`。N 没有正性假设；此供应者不需要对任意 lambda/omega 添加范数上界。

对六个 smooth scales 可先固定同一 A，再三次使用 (M,R)=(B,R)、三次使用 (2*B,2*R)。二者窗口半径相同，都是 ceil(10*C*R/B)。共同 J 的窗口识别、primary 尾有限合并、六项误差及保持 y=0 完整核由 consumer 负责，不在这五个恢复供应者中另做。

## 4. 来源与验收等级

五份原完整字节保存到本 intake 的 `upstream/`。`SOURCE_FRAGMENTS.json` 将记录原 blob、完整文件 SHA256、每个原片段字节 offset/长度/行号、marker 内字节 hash、完整声明名和必要适配。

每个恢复片段采用唯一的 `-- BEGIN recovered <label>` / `-- END recovered <label>`，末尾换行计入 SHA。预期 21 条具名恢复声明，15 theorem、6 definition；不新增数学声明。恢复时若出现必须改变证明正文的 API 适配，将单列原/新字节及原因，不把它混写为 byte-exact。

`SmoothProgressionError` 原完整文件已在 P3.2 来源 `34201be0ca95d465336119fce24b7681c17ab0c6` 的 provider 闭包绑定，源码 SHA256 `e85a63019bab532bd2f34996e9e1e59e71def841bde54c8404a637ebb1b17b52`，原对象 SHA256 `dc19446481153c5e394c9a32f0147ca2fdf3e6b982a4bc8b8e8d31c554032fab`。这不是本次新 core 的编译证据。其余四份原源身份已验证，已知缓存中没有其 strict/replay 验收证据；旧 header 不能单独判定现状。五个本轮恢复模块均等待 root 统一编译验收。

本轮供应者只提供普通光滑尾及有限质量提升，不宣称 OriginalData/FixedBlock 识别、全族 x 预算、Poisson m=0 估计、源 y=0 支付、谱 J/A 或整个 P3.1 已闭合。

## Probe1–Probe3 后的固定机械修复记录

初始恢复按原字节暂存；root 的实际编译诊断随后指出表达归一化及严格 linter 问题。当前保留 21 个原声明、原完整 blob 与原片段 offset/hash，14 个片段逐字相同，7 个片段仅执行 MECHANICAL_REPAIRS.json 中 10 个唯一固定替换。包括删去已完成目标后的 ring、化简零频 if True、去掉重复 simp 参数、一个 unused proof binder 的 alpha 重命名、乘法交换结合归一化、单目标 tactic 顺序和有限求和分配律方向。没有增加假设、改变常数/量词顺序或重推分析证明。当前源码及 installed offset/hash 以 SOURCE_FRAGMENTS.json 为准。root 已报告 probe4 的五个 supplier strict 全部通过，正式验收另行绑定真实回执。
