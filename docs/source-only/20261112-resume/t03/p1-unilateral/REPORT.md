# P1.4 第五、第六单侧停项的完整模数

**源码结果。** 对 P1 原来的 raw 与 licensed 两棵树，在 `N>1`、原数据的 `e≥0`、`L=N^epsilon`、`epsilon≤1/500` 且 `X≥N^(3/5)` 时，每一个真实单侧停项的高模数值为零。因此原 `actualFifthSixthExclusiveAbsInvoice` 恰为零，`rawStopped−licensedStopped=0`。原物理系数差保留第八层的三个前沿账单。新文件共 320 行，SHA256 为 `4413db3318142fedbbb7d7817b795863893b42cd981de4d7d77decf66eb31ba7`。T10 已独立核对这份源码及其调用的真实量词。Lean 核验尚待执行。

## 原对象与前提

P1 的源码提交 `544e3b07a5572a2ae21bad180e48e1cdccd91c91` 和交接 `a023ae055d3d90738f6965a2848266aa13089faf` 包含同一个 `SixthBothInvoice` blob `fe848722381b301e3d044a284aad29cb4fa1909e`。它已在 `fifthSixthWithoutBoth` 中移除原来为零的第六 BOTH 类。本次从移除后的原列表出发。

两侧分别是 `P4AOriginalFull87CompleteSixthDispatch.policy e q om N` 和 `P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om N`。严格高模数测试仍为 `X<a*t.selected.prod`。实际状态取自 `sharedRankFour e q om N cap w z`，并使用原符号、质量和剩余有序素数。`delta,n,q,om,cap,w,z` 均沿原 P1 结论量化，没有增加旧第三 owner、档案出处、盒覆盖或假定单侧账单有界的前提。这里的策略独立于本轮 All22 有限分支的早期三项付款。

冻结稿 `9731290e8f53cffda44129906cde6a965eaa869b` 的 `proof-library/source/actual-k-compilation-joint-audit.tex` 第 28–44 行保留词的后缀和第六节点原有准入，第五替换在本节点重测。`proof-library/source/imbalanced-chen-transfer.tex` 第 10760–10767 行给出已准入第五自身的立方测试。编译审计第 200–220 行在原有序因子上用前一个奇数立方控制后继的偶位。`proof-library/source/actual-k-distribution-joint-audit.tex` 第 43–56 行保留小因子的真实符号，并区分基于 `N` 的模数界与局部尺度所需的固定余量。

## 第五单侧的每个物理终端

1. 第 36 行 `admitted_fifth_cube` 展开真第五负号准入。raw 侧先穿过原第八、第六层拼接，在原第五层高上得到 `ordinaryRosserPrefixAdmissible false D`。licensed 侧在真实 `active` 分支使用 `cap5`，在另一分支使用实际 `exponent5`。从 `c0ee142fe551ea8d36da6bbe6f65a12a0899e490` 的 `exponent5_le_initial_ceiling` 与 `finite_cap5_le_initial_ceiling` 得到两侧各自的 `D≤N^(299/500)`。已发表的 `odd_history_own_cube` 用五元词的奇数长度和严格顺序给出 `b₅*p₅²<D`。
2. 第 83、126 行把每个 `stoppedTerminals 8` 终端的新增因子追回这个第五词的真实剩余后缀。终端秩严格小于八，因此最多再选两个素数。原载体严格降序，新增因子均小于 `p₅`，其积至多 `p₅²`，从而终端的实际粗积 `b<N^(299/500)`。空后缀和第六、第七终端均在同一证明中。此处用的是原列表的每一次出现。
3. 仅当该终端原符号选择的 `actualSmallRosserPlus` 或 `actualSmallRosserMinus` 非零时，才使用对应 `*_active` 定理的 `a<L`。于是 `a*b<N^(epsilon+299/500)≤N^(3/5)`。原显示小因子集合可能含 `a≥L` 的零系数。第 183 行用 `nonzero_stopped_has_actual_ancestor_highq_witness` 提取真实非零系数和 `X<a*b`，与完整模数界矛盾。这样既覆盖 raw-only，也覆盖带原负号的 licensed-only。

第 168 行另核实，在共同准入的负号第五词之后，第六查询的符号为正。两侧原 `policy_even` 都返回真，所以原先筛去 BOTH 后的第六单侧列表为空。该事实来自真实的准入查询，未使用两棵树其余部分相等的假设。前一包的 BOTH 约化保留了 `c2ac1bb` 的 rank-seven 停项结果和 `05e8685` 的已许可第六层高上界。本包的第五层证明直接使用 `c0ee142` 的第五层上界。

## 对原账单的结论

| 导出 | 所付对象 |
| --- | --- |
| `actual_fifth_terminal_full_modulus`，第 126 行 | 每个真实准入侧的第五子树中，每个深度八以前的终端和每个活跃小因子的完整 `a*b<N^(3/5)`。 |
| `actual_event_zero`，第 233 行 | 原共享第四状态的 `actualFifthSixthWithoutBoth` 列表中，每个事件的 `signedValue=0`。 |
| `actual_exclusive_invoice_zero`、`actual_stopped_difference_zero`，第 274、286 行 | 原单侧绝对账单为零，原高模数 stopped 差为零。 |
| `physical_highq_le_frontier`，第 300 行 | 原物理差的绝对值至多为 `rawOutsideHighQInvoice + actualProducerThreeClassLeafBill + licensedOutsideHighQInvoice`，三项均使用同一组原参数 `N,cap,w,z,L,X,F`。 |

单侧停项部分属于原稿已有奇数立方与后缀顺序能够补齐的形式化连接。若在分布定理中需要固定 `thetaStar<3/5`，上面的中间幂次给出 `thetaStar=epsilon+299/500`，须在 `N` 前取 `epsilon<1/500`。交接容许的等号 `epsilon=1/500` 已足够消去此处 `X≥N^(3/5)` 的严格高模数测试。该等号没有单独提供低于 `3/5` 的固定幂次余量。

第八层前沿三项的支撑与付款、完整物理系数在素数积和互素均值两端的分布估计，以及与其余精度预算兼容的参数选择仍须分别处理。冻结主文 `paper/source/manuscript-body.tex` 第 258–274、743–751 行列出了继续得到 sharp prime 结论所需的条件。此次没有调用该外部估计，没有执行本地 Lean、有限守卫、数值计算或 CI。[单侧停项源码](P4AOriginalFull87UnilateralStoppedLevel.lean)
