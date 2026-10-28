# lower_square 第三批：实际粗素数后继、冻结 cap 与残余预算

本批新增 3 份局部闭合源码，共 619 行、24 个定理（17 个公开、7 个 private）。第一、二批源码保持冻结。`local_step_complete=true`，但 `batch_target_source_complete=false`、`task_complete=false`。未编译、未内核验证，正式信用为 0。

`P2OriginalPairRootRoughProducer.lean` 构造 `pairRoot`、`warmTrace`、`pairPolicy`。外部 L5/L6 marked pair 以真实两个素数标签、递减顺序及其给定 cap 进入根；它是 marked incoming root，不是 L1/L2 普通序列首两步，故没有凭空施加 ordinary pair cube。外部根长度为 2，粗素数秩与完整物理秩的奇偶一致。代码证明实际 first-exit valid selection 与这一个具体 warm policy 的 accepted trace 双向等价，再从实际 retained support 和 native lower rho 非零，构造原 roughPrimeUniverse 的 chosen subword、精确乘积和真实 accepted run。没有输入 `hRoughWell` 或最终模数许可。

`P2OriginalPostFifthRoughSquares.lean` 提取真实粗词前三项对应的完整第五层状态；短于三项的原始粗词显式留在独立短秩分支。第五层之后，实际 `planChoice` 已不能 fresh，故后续 cap 等于此时真正冻结的 cap。偶层 admission 给出实际 cube；下一奇层旁路利用上一 cube 的实际余量和递减顺序推出 square，未增加奇层 cube 测试。归纳由此得到完整及 selected-complement 两组粗后继平方门槛，原始 selected 标签保持不变。自然数接口直接消费 actual run acceptance，并推出整数平方列表，不再把后继支持本身当输入。

`P2OriginalSelectedFifthRoughBudget.lean` 直接消费实际 corrected compact code 上的 `select`，取同一 `SourceForm`、掩码和实际 stored affine row。旧五素数 prefix 的门槛来自原 source selector，后继门槛来自上面的实际 trace 推导。粗 trace 用同一行的 double buffer，物理层级用 single buffer；代码证明两者相差恰一个 buffer，再从真实粗平方门槛推出 `product * L < N^physicalCap`。因此最终 residual budget 是结论。`L <= N^buffer` 只是整数行之前分配编译缓冲的标量条件，不是等价的最终粗支持假设。对现有 U5 的 literal smallLevel/smallCutoff，另证明 `attachmentNu*epsilon<=buffer` 给出该 L 条件，且 epsilon<=1/8 给出 beta-minus 所需的 cutoff²<=level，可送入第二批 native small extension 接口。

必须保留的实际边界：主 SourceForm 定理仍要求实际 scalar row 与第五层 `H.cap` 的精确身份；所有原 L5/L6 reached branches 的该身份尚未构造。新 `pairPolicy` 是本批明确构造的 source-only continuation，尚未证明它等于全部既有任意 U5 policy 或 L6 LowerData.policy，也未做安装。当前直接消费的仍是既有 tent CandidateBank；W 的独立算术许可及完整 mixed-bank 覆盖未因此闭合。所有短秩分支、统一缓冲与共同收敛、完整 canonical 标签及同 rho 的最终 small-attachment 调用、AP/BV/PP/lower mean 都继续开放。没有从 arbitrary retained policy 推出 global cap<=nu 或全模数支持。

本次核对原稿 280–297、693–735、808–817、879–905 行，未识别新的原稿数学缺口。原稿要求的内部对象衔接仍继续推进；这里没有把完整目标或 hLower 重新命名为 primitive 前提。

REGISTRY.json 记录每份源码、source-only 安装映射、前两批冻结字节、生产路径依赖及手稿的实际 SHA。仅做源码数学静态自审与哈希/占位 token 检查；没有 Lean/lake、编译、修编译、checker、测试、Git、额度检查或子代理。