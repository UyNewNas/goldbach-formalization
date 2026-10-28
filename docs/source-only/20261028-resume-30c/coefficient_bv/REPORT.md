# coefficient_bv 第三批：实际高秩 pair caller

已输出 `P1ActualHighRankPairFactorCaller.lean`。未编译，正式信用0。`local_step_complete=true`；完整第三批目标及原始目标仍未闭合，`batch_target_source_complete=false`、`task_complete=false`。

本轮从第二批同一 actual attached upper rho 的 high 分支出发。新增 HighFrontier 是实际 q 的内部见证：用已有非零系数前驱获得实际 small 整数与原始保留 frontier，再以已证明的 small/rough 分解唯一性识别第二批 high witness；原始向量全部为不同素数，因此其素因子秩等于列表长度，推出实际 frontier 秩≥3。这里没有把高秩、原始素数列表、full q 或D-well支持作为新外部结论假设。

随后从该实际 frontier 推出原始素数性与前三项/尾部形状，并直接调用已有 actual_compact_frontier_all_rank_support。对真实 owned compact cell 的原稿 winning-pair 第6/7行，代码消除 actualSelectedPair_factorization 的原始支持及正性前提，保留该确定性算法的 capacity<1 全向量重跑分支。actual small 整数仅附着到第三因子；所得三个自然数的乘积精确等于同一完整 q。

数值上，原pair算法给三项的1−3delta、2−3delta、2−2delta余量。先放宽到 Monomials(delta/4)，再复用 third_attachment_monomials，实际 epsilon≤delta/4 给 Monomials(delta/8)。没有改变原整数、cap或rho。最后复用 transport，在任意完整local x>1上保留精确 log(N)/log(x) 的全部幂，包括谱项7/32，不擅自重置局部alpha。

必须保留的边界：actual leastWinningIndex=6/7、实际owned cell、whole-cell full margin、代表点t和原始A区间仍明确要求；它们是原稿可计算的分支几何，而非hMedium/hBrun之类目标输出。文件没有证明所有high项落入这两个分支，也没有把逐tuple allocator当作整盒统一slot assignment，更没有假定三卷积的signed系数范数或SW性质来调用谱估计。因此这是连接实际高秩对象到原稿pair数值factorization的必要内部caller，不是完整medium/Brun解析归约或任意高秩估计。

第一批与第二批冻结未动。直接source-only依赖是第二批 P1ActualCompactUpperBVBranchSplit，原路径、SHA和安装目标都登记于REGISTRY。其余引用均为既有生产source；coords私有前驱的短证明因私有不可导入而在本文件公开，来源已明确。未运行Lean、lake、checker、Git或额度检查。未发现可据以判定原稿数学缺陷的新证据。
