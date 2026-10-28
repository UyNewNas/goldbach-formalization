# lower_tail：实际 L5 的有限结点质量

已输出 `P2LowerActualL5FiniteKnotMass.lean`。它补的是实际 L5 质数对上所有有限查询结点邻域的算术质量估计，而不是再次证明已有 dyadic log summability。

证明保留原始 `P5OriginalU5CausalFinite.pairSupport` 与 `argument=residual/a`。先把查询半径 `tau` 正确乘回 `a`，再从原有实际分支选择定理取得四个 affine residual 之一。对每个结点、每个分支，较大质数固定后仅对较小质数应用带闭端点的 `PrimeIntervalMertens`，最后做完全有限的 Fubini 与求和。有限并集允许重复付费，未删去任何等号点。

这里也消除了一个实际对象衔接：从原始 selector 的质数性及严格顺序推出互素，证明乘积权重恰好等于 `1/phi(p*q)`；从原始三角形坐标范围构造紧质数宇宙并证明它覆盖整个 L5 source。最终 `source_l5_table_knot_mass_le_mertens` 的左侧确实对完整原始 L5 occurrence 求和，没有另加二维 boundary-mass 或 source coverage 假设。右侧是明确有限的结点与四分支之和，每项为 `primeMass*(2*(tau*a/slope)/a+eps)`。

另附两个标量引理供 U10/U11 后续使用：`max(2,L/w)=2` 当且仅当 `L<=2w`；只有 `q>2+tau` 才能把 clamped query 的邻域全部转成 proper affine strip。这保留原稿指出的正测度 clamp state。

本任务整体仍未完成：L6 及 U10/U11 的实际有限 source 求和、冻结物理 row 与理想 typed residual 的绑定、共同函数收敛、真正 h248 count/mean 语义仍未闭合。没有把这些结论作为假设包装。原稿未发现新的数学缺口。

本文件文本闭合、无证明占位，源码作者已做静态推理审阅；完全未编译、未跑 Lean/lake、未做内核或数值检查，正式证明信用为 0。唯一直接导入是 source-only `P2LowerActualL5L6PrimeKnots`，其精确路径及 SHA-256 和主要传递依赖均列在 `REGISTRY.json`，供父代理验收及编译专员安装。
