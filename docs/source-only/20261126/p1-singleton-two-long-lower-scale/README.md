# 原 singleton 两条长变量的统一尺度下界

状态：**仅源码，尚未 Lean elaboration、普通编译或内核验收**。

本包只补齐 1106 稿 coefficient appendix 第 797–821 行所用的固定幂下界：对原 `longPositions` 已经给定的同一对位置，证明其两个下端点都至少为 `X0^(1/4)`。`X0` 始终是原矩形全部块下端点的乘积；没有重新选择两个变量，没有把总和非零替代实际 tuple 的 profile 活动条件。

## 两条声明

- `eventually_chart_long_lower_scale`：在 `x <= 2*R`、`R >= 1` 和原长变量阈值下，用固定 `1/12` 指数差吸收常数 `2^(1/3)`。
- `eventually_actual_singleton_twoLong_lower_scale`：使用既有固定矩形与实际 chart-window 证明，把同一下界运送到 physical `N`。最终 `N` 阈值先于 profile、chart、HB 行、矩形、活动 tuple 和两个位置量化。

复用现有 `P1OriginalSingletonFixedScaleTransport`、固定矩形、原 two-long dictionary 与 `originalMediumHigh`。所需活动窗口只给出 `X0 <= 2*R`；原 `longPositions` 给出每个原长端点严格大于 `R^(1/3+zeta/4)`。`zeta > 0` 来自原稿的 `kappa > 0` 与 `kappa <= zeta/10000`。

## 核验与边界

根代理和独立审阅代理已核对原稿、同一变量身份、量词顺序及精确依赖源码。发现并纠正一处 Mathlib API 表达：正乘因子的消去使用 `le_of_mul_le_mul_left`。这不是新增数学假设。见 `SOURCE_REVIEW.json` 的精确指纹、供应者提交与审阅范围。

本包没有重新证明 Brun、P2、Fourier 或阶乘估计。将来集成必须沿用已有 `NoMediumPairRows` 的互补后像，保持既有声明所有权；本包也不据此声称递归依赖已全部编译或 P1.5 已完成。
