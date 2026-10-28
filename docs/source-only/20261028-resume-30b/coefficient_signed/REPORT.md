# coefficient_signed 第二批：平方自由 raw 投影与固定秩穷尽

输出 `P5All16SquarefreeRawProjection.lean`（313 行，13 个新引理）。本批有限反向覆盖、秩穷尽和投影连接已在源码中闭合，标记为 `local_step_complete=true`、`batch_target_source_complete=true`。`task_complete=false` 按原始完整 30 项任务口径登记；未编译，正式信用为 0。第一批文件未修改。

先复用现有 `OriginalGatedSlotsRetainedSupport.retained_rough_iff_divisor_upper`，不重做 ordinary Rosser 的整棵 first-exit 支持字典。对于任意 raw Cartesian 产品 `d`，从真实素数槽及 squarefree 条件推出列表无重复、`d.primeFactors` 等于该列表的 finset，因此 `k=d.primeFactors.card`；列表的素数集合包含于原始 rough universe，从而 `d` 整除原始 rough prime product。literal raw upper gate 加上该整除关系，反向构造真实 retained 支持。另一方向用真实 retained 的 canonicalSlots 构造 raw representative，包括空词 `d=1`。这给出逐秩支持的双向等价。

逐秩求和时，未过 upper gate 的项由原始 raw weight 自身为零消去；没有额外丢项。对所有 k 求和，每个平方自由 d 只在其唯一 prime-factor rank 出现。然后将原先仅限 policy.val<15 的旧 rank 辅助证明沿实际 all16 的 native active mark 重新推广，使用原始 `mark_modulus_cap`（适用于 W）得到 d<N^(153/256)，结合每个素因子至少 N^rho，推出固定 `floor((5/8)/rho)` rank bound。该界先于 N 和 marked tuple 固定，最终定理没有等价 support 假设，也没有把所需 rank bound 当输入。

最终 `squarefree_all16_linear_eq_physical` 对任意 signed F 证明全 all16、全 k 的 squarefree raw functional 等于真实 jointPresievedSigma 的物理和；`squarefree_all16_sigma_eq_joint` 再给出逐点系数等式，含零和 off-support。与第一批合成的 `squarefree_all16_linear_eq_owner` 将其连接到同一 retained owner-word 族。计数和 exact coprime mean 因而共享同一个投影系数。`raw_all16_eq_physical_add_collision` 保留原始未投影项与物理项之间精确的 signed repeated-rough kernel。

最终前提只有 N>1、eta>0、固定 rho>0、w=N^rho，以及实际 rough cutoff 许可 w<=Z；没有假设 PP、系数等式或投影结论。该 cutoff 许可仍须由真实参数构造在调用处实例化。

本批尚未处理 sorted owner-word/block regroup、多标签 scalar 的 analytic tensor 应用、repeated-rough 在 count/mean 各自的绝对误差包络或 PP 渐近估计，也未把旧 all-prime native sigma 与 common-beta 系数等同。完整主目标仍 OPEN。未发现新的原稿数学缺口；未运行 Lean、lake、checker、CI 或额度检查。源文件、直接及关键传递依赖的 SHA256、安装 import 映射和精确边界见 REGISTRY。
