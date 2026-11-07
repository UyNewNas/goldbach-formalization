# upper_jensen 源码交付

新增 `P5OldFifthFirstFConcavity.lean`，安装模块名为 `ImbalancedChen.P5OldFifthFirstFConcavity`。文件文本闭合，未运行 Lean、lake、数值 checker 或审计，正式信用为零。

本轮确实消除的是旧 `P5OldFifthPointwiseQ` 源码显式保留的 `hconc` 内部义务。对原始 `firstF(s)=log(s−1)/s` 直接计算一、二阶导数。二阶导数乘以正分母后的分子是 `2(s−1)^2 log(s−1)−2s(s−1)−s^2`；在 `[2,4]` 上，以 `log(s−1)≤2` 将它压到 `(s−2)(s−4)−4≤−4`，再调用 Mathlib 已有二阶导数凹性判据。没有把凹性或任何目标积分当作假设。

为满足旧 `P5OldFifthChildQJensen` 已经写好的接口，还证明 `firstF_monotoneOn`。先对 `(x−1/x)/2−log x` 求导，得到 `(x−1)^2/(2x^2)≥0`，从其在 1 处为零推出对数上界；随后把 firstSlope 的分子比较化为 `(x+1)(3−x)/(2x)≥0`。因此获得 `Q_b` 在精确区间 `[0,b−2]` 上的凸性、单调性、非负性，并给出实际 frozen-parent 正部核 pointwise theorem 不再需要 `hconc` 的实例。

依赖仍为前任冻结的 source-only `P5OldFifthPointwiseQ` 及其 gap/barycentric/frozen-parent 链。直接依赖的原始路径、SHA、安装位置、所消费声明都在 `REGISTRY.json`。Mathlib 使用仓库 manifest 固定的 `e4c91783...`；已核对该提交的 `concaveOn_of_hasDerivWithinAt2_nonpos`、`monotoneOn_of_hasDerivWithinAt_nonneg`、对数及求导 API 源码。没有复制或重造 Mathlib 的分析定理。

原任务整体仍未完成：具体 child 的保存 picks、d、A/B 比率、partition、owner clipping loss、rational log floor 和当前 K 绑定仍在后续。旧 ChildQJensen 的文本现在有了其所期待的 `firstF_concaveOn` 与 `firstF_monotoneOn` 供应者，但本交付不宣称该旧文件已编译。未发现原稿数学缺口；这里处理的是已明确记录的内部形式化缺口。
