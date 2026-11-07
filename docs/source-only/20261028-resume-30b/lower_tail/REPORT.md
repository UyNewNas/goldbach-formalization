# lower_tail 第二批交付

已输出 `P2LowerActualL6FiniteKnotMass.lean`，共 277 行、15 条定理。承接第一批冻结 L5 文件，补上实际 L6 的有限 h248 结点质量。第一批及生产文件均未改动。

本批使用完整 `currentChenUpsilon6RetainedSelector N E beta`，保留原始 E 掩码、真实质数标签和 product buffer，没有只取严格 ordinary inner selector。由原始对数域恒等式推出每个真实 pair 都落在具体紧质数宇宙 `[417/5000,59/250]`，由第六行原始两个不相交质数带推出互素，并证明乘积权重恰好等于原来的 `1/phi(p*q)`。

查询函数明确取原稿的 `(1/2-u-t)/a`。半径 `tau` 变回分子时乘 `a`；固定较大质数后，较小质数的结点邻域就是一个闭 affine strip。有限 union bound、有限 Fubini 和原有一维 `PrimeIntervalMertens` 给出整行的显式质量界：`knotCard * primeMass * (2*tau+eps)`。所有结点和等号均保留，没有把二维边界质量直接设为前提。

另证明关键实际衔接：在原始 masked native `lowerRows` 上，`query>=2` 当且仅当原始质数乘积不超过 `N^(1/2-2a)`。因此 `activeOriginalSource` 精确等于零缓冲的完整 retained source。最后一条 `active_original_table_knot_mass_le_mertens` 直接覆盖原始 L6 的整个 h248-active occurrence，包括 `query=2`，不遗漏普通 inner selector 以外的端点。

保留的边界：这里的 analytic query 没有被等同于自然取整后的实际 quotient level、`LowerData.L`、`lowerRho` 的均值或 frozen compiled residual。完整 lower_tail 仍需 U10/U11 的 clamped 实际 source 求和和 frozen-row 绑定，以及一维 Mertens 的 eventual error、共同因果逼近和最终 lower functional。未发现新的原稿数学缺口。

源码文件文本闭合，`complete_module=true`、`local_step_complete=true`；完整原目标仍 `task_complete=false`。只做作者静态证明审阅及 SHA 核对，完全未编译、未运行 Lean/lake、内核或数值 checker，正式证明信用为 0。精确 source-only 导入路径、SHA 和安装对应在 `REGISTRY.json`。
