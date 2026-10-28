# lower_chambers 第二批交付

新增两份局部完整源码；第一批保持冻结。本批解决任意真实 strict W-winning 点的有理局部盒及其紧子集有限覆盖，整体原稿 lower/CapPlan 仍 OPEN。未编译，正式信用为 0。

`P2OriginalStrictWLocalRationalCover.lean` 的 `StrictWPoint` 明列原始物理条件：epsilon<z<y<x<start cutoff、x<mu、实际 baseline parent 的 first-square/second-cube 门槛、W 超过 parent、W activation，以及 W 严格超过每个非空 rank3 mask 的原始 `v(sum_I)`。它没有将 WBoxCheck、table、plan 或 winner 等式作为存在性前提。

证明把三个 lower endpoints、三个 upper endpoints 和 beta/delta 组成八维端点空间。所有几何门槛以及有限个 tent winner 余量组成一个开集；对角点 (x,x,0,0) 属于该开集。利用同一个开球和有理数稠密性，实际选出 lo<x<hi、beta>0、delta>0 的共同端点向量。正缓冲来自证明中的选择，而非外给的盒检查。对任意紧集 K，只要每点满足这些严格原始条件，就由 Mathlib 紧性提取有限有理盒覆盖。相等面/order/gate/winner walls 未进入 StrictWPoint，因此并未被免费覆盖或声称零误差。

winner 的全盒保留使用真实上下端点：A(sum hi) 与 C(sum lo) 的 min 是整个 closed box 上 `v(sum actual)` 的上界，因此允许盒穿过 tent 自身折点，不需把 v 伪装成全局 affine。

`P2OriginalLocalWBoxMeshLicence.lean` 从实际 corrected compact mesh 的 qLo/qHi 包含关系和前三 unselected bits 推出每个原始 WBoxCheck 字段，再给精确 WThirdTable 行。历史测试仍对实际 baselineCap rho；完整 buffered squares 使用同一个 W cap；未将 selected bits 擦除。qLo<=qHi 也在该模块从 corrected grid 的正步长证明。

仍需后续工作：统一 common mesh 的定量细化与边墙损失、有限盒共同 beta/delta、四/五层实际 frozen-parent stage、mixedWinner gapLower 与 Trace/source-form/同 rho 算术连接。lower_splice 负责后者的 mixedWinner-to-Trace 接口。未发现新的原稿数学缺口。

仅做源码和数学静态自审，并查阅 pinned Mathlib 主源确认复用接口；没有编译、Lean/lake、checker、kernel replay、CI、Git、额度检查或看板修改。完整路径、SHA、原稿锚点及剩余义务见 REGISTRY.json。
