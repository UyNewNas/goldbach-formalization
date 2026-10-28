# certificate_omega 源码交付

已写 `OriginalPairedN48OmegaStepArithmetic.lean`。本文件是完整局部证明源码，尚未编译，正式验收信用为 0；分配任务的完整 uniform Omega query 目标仍未完成。

本轮消除了 PhaseB4 中独立的算术检查边界：原始 `sourceDiv` 四个带符号商的 min/max 先归一化为现有 `Enclosure.mul` 与正分母 reciprocal，之后精确对应 112-bit outward round。因此除法 soundness 对负分子、跨零分子均成立，不需要新增 `StepArithmeticValid` 前提。再把真实 delayed weighted U 节点除回同一个网格坐标，接到实际 `sourceStep` 的两次加法和误差带；结合真实 Buchstab weighted DDE，得到下一 U 节点的语义。

`initial_U_contains` 直接使用真实 `[1,2]` 上 Buchstab=1/s，证明网格 `mesh<=i<=2mesh` 初值。`all_weighted_nodes_of_local_errors` 对真实源数组做强归纳，之前三个 U 节点的语义均由归纳得到；只保留原始 log 初段、局部 sharp error 与纯算术 `SourceProducerValid`。特别注意 Python 初始化 U[0]=1，但 0*Buchstab(0)=0，因此全部节点定理只覆盖有效的 `mesh<=i`，没有加入不可能的 U[0] 初值前提。

核心未完成项是原始每格 `h^3/6` trapezoid 误差。PhaseB4 已证明的 1/2-Lipschitz 只能给 `h^2/4`，不能偷换尺度。本文件明确保留局部 `SharpCellError`，没有证明该分析界，也没有重定义为较弱误差。之后仍须证明 sourceSmallLog Horner/tail、恢复数组并核纯算术 producer、证明 cell bulge 与 max query、连接同一个真实 parent 的 Z_B/costHi 和历史 floor。

依赖安装顺序：先按 REGISTRY 的精确 SHA 安装既有 source-only `OriginalN48Q112LocalProduct`、`OriginalPairedN48OmegaProducerAdapter`、`OriginalPairedN48OmegaTrapezoidStep` 及其原有前驱，再将本文件放入 `ImbalancedChen/OriginalPairedN48OmegaStepArithmetic.lean`。没有修改生产模块、原草稿、共享看板或 Git。没有运行 Lean/lake、编译、Omega/Python evaluator、数值 checker 或额度检查。

静态检查确认没有 sorry/admit/新增 axiom/unsafe。没有据此发现原稿新的数学缺口；这是既有实现边界的算术/递推补全。
