# 四坐标图表截断的证明体勘误

本补件为 `ImbalancedChen.P5IndependentFourPrimeChartCutoff` 给出一个可逆选本。历史原件的 SHA256 为 `e3280f5e35364c4fa7bbe41299c8969daea1af2b70363a4e8003c3dd10c006b8`，选本为 `5b8132f4e6c639fd6ee95efed6bdcb9b8bc5a2bc8c700b1bd24ebade8cc954b3`。

| 原件位置 | 所修证明 | 数学等式及 Lean 改动 |
|---|---|---|
| 100–108 | `active_four_chart_argument_upper` | 在乘积上用原列表长，在目标上用尺度列表长。用两次指明指数的 `pow_add` 恢复系数 `2^(6K+10) = 2^(6K+2) · 2^4 · 2^4`，再按原 `argument` 的乘积结合。 |
| 126–128 | `active_four_chart_argument_lower` | 使用同一对长度和正前因子，将四坐标乘积下界写成原来 `C · (D · prod)` 的形式。 |
| 175–178 | `cutoff_lt_source_floor_of_scalar_threshold` | 显式使用 `Real.rpow_natCast` 转换自然幂，再逆向使用 `Real.rpow_mul`。指数等式为 `5 · (astar/10) = astar/2`。 |

五个公开定理与两个私有引理的声明头逐字相同。`TYPE_HEADERS.json` 列出每个原声明、原件与选本行号、两份字节指纹。实际粗秩二调用的第 22 行 `active_psi_scale_each` 连同证明体逐字相同。它从原逐词窗口和素数源区间推出所有活动尺度的上下界。整个四坐标模块都需要进入随后 Lean 的安装依赖图，因此另外三个证明体也需要有效的改写。

本件接续 `rank2-dependency-audit/REGISTRY.json` 的六个历史依赖，只处理其中已指出的下一层四坐标源。原作者登记的四维一般 W 识别及安装状态保留。完整依赖图的编译、剩余高秩分布估计和最终计数仍待完成。核查依据固定原件、Mathlib 源和字节差异。此补件没有运行 Lean 或 CI。
