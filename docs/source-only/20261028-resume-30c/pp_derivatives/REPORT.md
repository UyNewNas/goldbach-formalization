# pp_derivatives 第三批交付

新增 `P5ActualEtaPsiOccurrenceBudget.lean`，403 行；第一、二批和生产源码均未改。未编译、零正式信用，`task_complete=false`。

本轮定义真正固定函数 `eta(s)=smoothTransition(s−1)`、`chi=1−eta`、`psi(s)=chi(s)−chi(2s)`。eta 在 s≤1 恒零、s≥2 恒一；其 log lift 的零阶有全局界，正阶在闭紧区间 `[0,log 2]` 外为零。psi 的 log lift 紧支撑在 `[-log 2,log 2]`。连续性、局部恒等微分和紧性推出全部指定有限阶的单一全局常数；没有加入任何 cutoff 导数界作为前提。

实际 complete product 通过逐组 log 求和恒等式变成 base product 乘 `exp(sum z)`，故 eta 只是同一固定 scalar log lift 的平移。`occWord_scalarLift` 精确识别任意有序导数字母串与其长度阶普通导数。grouped psi 的 `occWord_groupTensor` 则精确记录原 owner 字母的计数，每个字母只作用自己的组；重复原 label 保留，未引入错误的 `k^r` 损失。正的实际 U、R、T 给出 `actualEta_eq_scalarLift` 和 `actualPsi_eq_groupTensor`，没有把 marked t 或 rho 当作原独立 test u。

最终 `actualChart` 包含原 Family ambient、同一完整乘积 eta、全部原 grouped psi 与第二批实际 plateau。`actualChart_smooth`、`actualChart_compact` 及 `exists_actualChart_word_budget` 从这些真实对象推出：固定 kStar 后，先选择一个 C≥0 和自然数 B，再允许所有正 T、原 rank、m、owner、dyadic scales、原尺度 R、kappa0、长度≤12*kStar 的任意字母串和所有 z；导数绝对值均不超过 `C*log(T+2)^B`。

该点界端口已与 pp_fourier 协调，后者接 occurrence/Euclidean 导数转换、矩形积分和真正 mixedD 预算。本模块不循环导入其后续积分。故本轮 `local_step_complete=true`，但 `batch_target_source_complete=false`；本模块自身尚未给 D_T 积分，全局原目标仍 `task_complete=false`。native arithmetic-selected Family、整数 HB atlas、碰撞/素数幂及 same-rho PP 仍需后续。

源码与前驱全部 raw SHA256、安装映射和准确假设见 `REGISTRY.json`。未发现新的原稿数学缺口。
