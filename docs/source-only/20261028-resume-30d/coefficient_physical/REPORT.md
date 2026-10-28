# coefficient_physical 第四批交付

新增 `P5OriginalRowsCausalPhysicalJoin.lean`。这次先补实际 P4/P5 接线，再给同系数逐点 majorant 和有限密度账本。文件文本闭合；未编译，正式验收信用为 0，原完整任务仍未完成。

发现并保留的重要边界：旧 `physicalPolicy` 的基底是 corrected above-mu 第二/第三 fallback 的 `finalPolicy`，其 `through_sixth_eq_corrected_parent` 表明深度不超过 6 时没有插入真实原 P4/P5 row maxima。因此不能把旧链直接称作 completed adopted all22 policy。

新 `Inputs` 只包装原始数据：有理 buffer、原 mesh/rough 参数、完整 fourth rows 与原始 `licensed4`、原 fifth `J5/rows5`，以及尚待实例化的物理第三/第六祖先指数。新 `policy` 明确依次指向生产 `HistoricalThirdCoarse.policy`、`producerPolicy4`、`policy5`、以该真实 `policy5` 为基底的 sixth 和 eighth。原 licence 没有替换成 checker flag，真实 finite maxima 没有替换成 stored cap。

`next_policy_eq_actual_splice` 证明第五变化是在**共同 rank-four 前沿**上替换当前 fourth continuation，而不是 rank-five splice；第五自己的 admission 必须看到新 cap。`eighth_through_sixth_eq_original_fifth` 证明最终策略保留每一个深度不超过 6 的实际 fifth 查询，`joined_actual_fifth_test` 将其明确化为原 `exponent5` 的自然数测试。全部前沿记录中的历史、sign、mass、remaining 都由 `action_preserves_parent_frontier` 保持。

对同一新 `finalRho`，代码接入所有整数上的原 rough-indicator majorant，并把各阶段的真正 physical density 写为完整根叶/带符号终端源。small betaPlus/betaMinus 与完整模数 totient 留在同一个 terminal test 中。四次 `densityChange` 都是新策略减**当前**父策略的实际前沿差；有限 3→4→5→6→8 telescope 因此每次只记一次，未声明任何单项正性或数值 gain。H3 局部 q-fibre 也接到该 P4/P5-wired finalRho 及其真实 full root leaves。

这条新 joined policy 没有被无证等同于旧 above-mu fallback physicalPolicy。下一必要工作是两类前驱的合法 causal common refinement、采用的 P4/P5 原始 row/licence 实例、完整 selected sixth lambda6 供应、87 eighth owner/覆盖/不交和共同祖先 margins。support inflation <1/1000、599/1000、两项 reserve、K 与 PP 也都未闭合。与 transfer_power 已共享真实 policy5 接口及未完成边界；其正在补该实际 fifth 策略的支持上界，但本文件没有导入未冻结的新源或假定 full22 证书。

未发现新的原稿数学缺口。第一至第三批冻结文件、生产文件、Git 和看板均未修改。精确直接/关键传递依赖 raw SHA 与下一依赖任务见 REGISTRY。
