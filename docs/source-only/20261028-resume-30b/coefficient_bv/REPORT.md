# coefficient_bv 第二批交付

新增 `P1ActualCompactUpperBVBranchSplit.lean`，5 个定理，未编译，正式信用 0。完成一个真实分支 caller 与必要分解，整体分配目标仍 OPEN：`local_step_complete=true`、`task_complete=false`。

核对了原稿 modules/distribution-coefficient-completion-20261010.txt 第7节。其 upper 低秩为实际粗素数因子秩≤2，完整粗支撑指数19/48；small beta 因子再支付实际小 level。完整物理 q 的完整秩不能与此前 joint 系数去掉四个标记素数后的 residual 秩混用。因此本轮沿已经冻结的真实 compact upper attached coefficient 续接，没有把 joint family 强行放入 BV。

新增代码对计数接口的同一 `attachedUpperCoefficient 1 thirdPrefixRho epsilon` 定义实际 support，并证明对任意算术测试 F 的完整支持求和精确等于已有 actual low-rank 分支加其补集。计数、exact coprime mean、centre 或 signed discrepancy 可以使用同一恒等式，不重新选择 rho。

高分支中每个非零项都由真实 active integer binding 取得 a,b，保留 q=a*b、a<N^epsilon、真实 rough coefficient 非零、q 与 N 互素；用实际 small/rough 因子分解唯一性，证明 b 的素因子基数≥3。这里消除了 existing low branch 中“所有支持分解均低秩”的量词与真实非零 row 的秩之间的接口问题。低分支则由已有 shallow-tree identity 证明在同一完整 q 上等于 initial-policy coefficient。

最后直接调用冻结 Phase6 的 actualAttachedCompact_BV_and_reciprocal_mass，给出完整实际 prime-AP discrepancy 减去显式高秩 discrepancy 的 arbitrary-log bound。只使用原始约束 e≤1/384、epsilon≤2e；该供应器通过19/48+1/192=77/192<1/2支付完整物理支撑，B,C与最终N阈值先于所有compact policy/mesh/attachment查询。没有把最后估计作为新前提。

未完成的是高秩项的 medium/Brun 解析绑定、marked graph 的实际整数模数、generalized convolution BV 的实际 prime-product caller，以及完整 current-PP。这次是实际 upper 分支的精确排分与 ordinary BV caller，不是全joint或全PP闭合，也没有声称第一批排除零类本身提供BV估计。

直接导入两个 source-only 供应器的原文件路径、SHA与安装目标完整记录在REGISTRY；Phase4/5/2供应链也按读取到的源码SHA登记，均继续保持uncompiled/hold。没有改动第一批、旧草稿、生产源码、Git或看板；没有运行Lean/lake/checker、没有检查额度。
