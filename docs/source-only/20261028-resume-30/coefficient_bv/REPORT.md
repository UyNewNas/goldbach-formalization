# coefficient_bv 本轮交付

已输出 `P5OriginalJointFullModulusRank.lean`（10 个定理），未编译，正式信用 0。分配目标尚未全部完成，`task_complete=false`。

本轮完成了先前 hold 文本中的一个真实缺口：原始 U10/U11 joint coefficient 的四个标记素数不能从完整物理模数 q 的秩中删除。证明先把 `slots t` 的像识别为 `fullPrefix t` 的素因子集，利用原始严格顺序得到精确基数 4；再调用已存在的实际 row/prefix 互素定理，得到

`(fullPrefix t * r).primeFactors.card = 4 + r.primeFactors.card`。

这不是人为总秩假设。它从实际 selector、实际 rowSupport 和原始 common-beta 参数推出。对每个非零 `jointPresievedSigma ... q`，得到 `4 <= q.primeFactors.card`，因此该真实系数在 total-rank ≤ 2（甚至 ≤ 3）模数上逐点为零，并且对任意有限集与任意算术测试 F 的对应 signed sum 精确为 0。最后一个定理明确 residual-rank ≤ k 只等价于 full-rank ≤ 4+k，不能等价于 full-rank ≤ k。

这消除了把 joint 的低 rough/residual 秩误当成 native L1/L2 total-rank-two BV 秩的可能，给下一轮合法分支选择一个严格算术接口。没有建立非空 below-half BV family，也没有把空过滤器当作实质分布结论。

原稿 `manuscript-body.tex` 334–338 说低秩使用 below-half BV，但现有实际 joint 支持只给 `q<N^(153/256)`。153/256 > 1/2；本轮没有找到原始实际非空 owner 的更强 full-q exponent，也没有用别的系数替换它。仍需精确原稿 factorization/chart 分支分类与数值 gate，或说明这里的 low-rank 指的是哪一层，而不能由本文新增秩公式推出 BV。此处报告为形式化实现/绑定未闭合；没有证据把它升级为原稿数学反例。

依赖全部为现有生产 source，直接导入 `ImbalancedChen.P5OriginalJointPresievedArithmeticSupport` 与 Mathlib 的 `Nat.PrimeFin`；没有新增 source-only 依赖。源文件及依赖 SHA-256、原稿锚点、未闭合事项已登记在 `REGISTRY.json`。只进行了文本及依赖用例核对，没有运行 Lean、lake、数值 checker、Git 或额度检查。
