# pp_derivatives 第二批交付

`P5ActualOccurrencePlateauWordBudget.lean` 为新的独占源文件，234 行。第一批与生产源码未改；未编译，正式验收信用为 0。

本轮闭合三个 cutoff 义务中的实际 occurrence plateau 一项。固定定义 `c(x)=smoothTransition(x+1)*smoothTransition(log 2+1-x)`，由 Mathlib 真正光滑 transition 的性质证明 c 在 `[0,log 2]` 恒一、在 `[-1,log 2+1]` 外为零且取值在 `[0,1]`。这符合原稿先固定 c 再选择目标尺度/图表的顺序。`plateau_rightClosed_atom` 直接证明每个整数 `(U,2U]` 原子的乘积 plateau 等于一，保留原右闭端点。

随后对真实 occurrence derivative 使用第一批的 Frechet 恒等式和现有导数支撑定理，证明导数字母串仍平滑且紧支撑。`wordBank` 显式枚举长度不超过 r 的全部有序字母串并证明覆盖，保留重复 label。有限字母串和有限维数集合上的紧性给出一个 `MC≥1`，同时控制所有 `m≤6*kStar`、`length(w)≤12*kStar`、所有 z；常数在 T、原 rank、owner map、dyadic blocks 及算术符号之前选择。这里没有假定 c 或其 tensor 的任何导数界。

`family_chart_actual_plateau_bound` 把该实际函数、平滑性和常数直接代入第一批 `family_four_chart_bound`，消除 Cut 的两项输入。eta 和 grouped psi 仍是两项明确剩余局部义务；`D_T` 积分、坐标体积归一化和完整 PP 仍 OPEN。

按第二批统一说明，`task_complete` 必须沿用第一批原始完整目标口径。具体 eta、grouped psi、完整 chart mixed-Euler 界和 `D_T` 仍开放，因此修订为 `task_complete=false`。本轮 occurrence plateau 一项已在源码闭合，保留 `local_step_complete=true`，另以 `batch_target_source_complete=true` 标记本轮窄步骤完成。`complete_module=true` 只说明文件文本闭合，`compiled=false`、`ready_to_install=false`、`formal_credit=0`。全部新旧源码 hash 和 source-only 安装映射在 `REGISTRY.json`。

没有发现新的原稿数学缺口。
