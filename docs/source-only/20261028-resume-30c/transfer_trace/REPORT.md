# transfer_trace 第三批

新增 `P2RoundedCausalFibreLossAndLevel.lean`，367 行。完整局部源码，未编译、零正式信用；原任务与本批完整收敛目标均未闭合。前两批冻结未改。

本批先处理原稿的关键方向：负系数向外舍入会产生 raw support 之外的 d，所以不能直接继承 raw support 指数。实际 compiler 的每个非零 d 都有同完整 logarithmic label fibre 的原 retained witness r；这由原 ALL/ANY 定义推出，未假设所需的 rounded-support 结论。等label意味着 canonical prime-word 长度相等，且 log坐标和最多增加 R·tau，因而 d≤r·N^(R·tau)。再用真实非零 beta divisor e<N^ell，得到完整 (b*e*d) 的指数 theta+ell+R·tau。

`exists_uniform_mesh_physical_level` 只从严格 raw指数余量与rank R选一次 tau，随后才量化N、CapPlan策略、cap、multiplier和整数word。没有选依赖N的prime-gap mesh来冒称共同有限逼近。`rounded_joint_sigma_physical_level` 进一步把此界接到第二批实际signed U6-U10-U11 sigma；lower fibre保留rounded rho，upper fibre用原native153/256 profile，允许同q抵消，未假设聚合sigma的unit bound。

密度方面定义真正混合 retained/rejected 完整历史fibre，证明未混合fibre的实际舍入系数等于raw，并推出 roundingLoss≤2*mixedMass（literal reciprocal-totient mass）。对于实际CapPlan，混合fibre又精确对应一条接受和一条拒绝的canonical integer trace，不允许另选顺序或理想父cap。

仍需的真实供应是：选定原始CapPlan/sourceform对所有raw accepted histories的统一full-prefix cap与rank，以及混合canonical trace fibres到实际wall strips的覆盖和uniform算术质量趋零。相邻lower_chambers本批在做实际rank3 wall strips，lower_square在做retained-tail门槛；本文件没有把它们的未完结论当作已证明事实。完整paired lowermean、数值density/fallback和same-rho PP仍开放。未发现新原稿数学缺口。

精确依赖和源码SHA见REGISTRY。无编译、checker、额度检查或其他目录修改。
