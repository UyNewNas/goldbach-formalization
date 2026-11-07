# certificate_rows 第四批交验

新增两份完整局部源码。local_step_complete=true，但本批全目标 batch_target_source_complete=false，原始 task_complete=false；没有宣称解析 enclosure 或实际积分 floor 已闭合。所有源码和闭合有限算术证明项未编译、未执行，正式信用为0。

`P2Winner9SelectedRowAnalyticCaps.lean` 从两行真实有理顶点和原始 U/L、v_j/L 构造具体正下界。通过非负、和为1的真实 barycentric coordinates，把全部factor正性、gap非负、P正下界与P<=U、a_j/P<=V_j延伸到两行整个闭物理support。给出一个实际统一 q<1 使0<=Y<=q；因此补齐原稿binomial/Taylor所需的紧致区间条件。还证明 a_j 与 P 间的整个线段属于(0,V_j]、真实坐标正性、sum coordinates<R<=M及R/M的字面上限，并由compactness和分母不为0得到真实density可积。这里的cap domain仅为这些实际解析/几何守卫，不代表完整97个继承策略约束已经通过。

`P2Winner9SelectedCurvatureFloorWitness.lean` 逐字读取两个原始curvature Q0记录，把它们的T_Q80/raw_Q96绑到同一actual typed data。row21复用旧闭合rounding source，row22给新的闭合未执行cross-product证明项；再应用已有有向取整定理，得到raw floor <= exact Jensen*(1+T10+Q0)，并与原始joined archive的raw字段对齐。row22的curvature raw小于旧log-selected值，代码没有把该raw误当selected gain。

原稿采用的更晚mixed记录是Q6。第三批的真实measured mixed identity只有k=1，因此不能用它直接证明整个Q6 floor。后续必须补k=2..6真实moments和convolution、实际E[P]=1、T10正remainder、-log二阶Taylor及求和指数化，并把Jensen factor接真实mass/means，才能从本批精确算术表达式转到物理积分下界。这是形式化实现缺口；未发现原稿数学错误。

第三批源码SHA仍为49bf15aaeef4ef88b927d353e283dca5149232c17ac795d0b53ddd7b20f00f24，旧批次全部冻结未改。精确依赖、字面数据、SHA和remaining见REGISTRY.json。未运行Lean/lake、producer、certificate checker或数值重放。
