# lower_splice 源码交付

已新写 `P2OriginalLowerWJointTraceSplice.lean`。全部未编译，零正式信用；原分配的完整 selected I3 signed splice 尚未完成。

本次把 PhaseC 已明确的第一处断点变成可用构造：`WPriorityRows` 在 rank 3 且 whole-box `WBoxCheck` 成立时明确选择 W，否则保留原 row，rank 4/5 的行数据也原样保留。`WPriorityPlan` 将此表交给现有 `compactPlan`，所以所有后续门槛仍经 checkedChoice 检验。没有把待证明的 selected-row equality 当成前提。

已证明 merged row 的 fresh cap/argument、实际 `[p3,p2,p1]` integerTrace 冻结 cap，以及下一 rank-four frontier 的完整条件：旧 `2t1<baseline` 和 `t1+3t2<baseline` 原样保留，而新 `S3+3t4` 必须小于实际 W cap。另有相同门槛的自然整数乘子版本。`WPriorityPlan_fourth_choice` 明确重测第四阶段时所用 parent 就是 merged 的 W cap，不能换成 ideal parent。

这些证明依赖具体 incomingCode 与 WBoxCheck；incomingCode equality 只命名实际物理编码，不假设任何策略/计数恒等式。WBoxCheck 内保留完整 square、selected complement square、原始 W gate、严格 buffer 与共同 parent 条件。原 rank-three 接受条件由 odd-rank bypass 推导，不能把新 cap 反写进旧第二 cube 测试。

该构造是合法的 W-priority 备选有限计划，并不自动等于原稿最优 mixed W/tent bank。还须接入完整 source-form licence、覆盖/优先比较和共同近似；还须证明同一 roughPrimeUniverse 上 reached-frontier 的 entire parity-policy splice equality，之后才能归并实际 signed I3 的 `plus_old-minus_plus_new`。这两类缺口不能由本文件的 cap equality 代替。未发现新的原稿数学错误。

未改生产源、旧草稿、Git 或看板；未运行 Lean/lake、数值 checker 或额度检查。直接和关键传递依赖的精确 path/SHA/install-target 保存在 REGISTRY.json，供编译专员安装后复核。
