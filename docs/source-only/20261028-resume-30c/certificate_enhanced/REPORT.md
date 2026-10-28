# 第三批 certificate_enhanced

新增 `P2Author512EnhancedHQueryDomain.lean`，沿同一 enhanced author-512 h→mu/a→h 实际物理父矩形，补完 residual 与 directed query 的全部几何条件，并接到已有普通积分下界。

全父域的三tent `pairRanges` 由精确有理数求式给出 s_low≥3、s_hi+1/Q<4.1。任意 Fin512 子盒的包含关系经 signed affine-range 与 min/max 单调性传递，因此 Q80 outward rounding 后 query 始终有序、覆盖原精确区间、且 literal lower lookup guard 为假，真实增强半域不存在 s=2 crossing。进一步得到实际末格 `lookupStop 50` 必在100..154，仅55个真实原bank端点会被调用。没有执行逐格或bank checker。

`actual_query_knot_both_cells` 对位于原精确区间内的任意内部 knot `1+k/50` 证明 outward query 同时选择 k−1 和 k 两个闭单元，随后 `actual_lookup_knot_min` 把 literal lookup 整数约束到两条实际 copied bank 记录的最小值，保留原 `ceil(...)-1` 规则。

原全部200端点 licence 在此父域可缩为 `EnhancedEndpointLicences δ` 的55个 copied-bank 解析不等式。代码证明这些 licence 如何经真实 slice-min、h 反单调性和 exact endpoint coverage 传播到实际 query，再去掉 h-defect integral 原有的几何、query 与残量正分母前提。主定理 `actual_enhanced_pairCell_integral_lower` 对同一个实际 pairCell、同一个增强 residual，把 ordinary 最大候选与独立正 h 项接到真实 ordinary+h 两个积分。

55个解析端点不等式仍未证，故本批完整 endpoint-licence 目标没有闭合：`task_complete=false`、`local_step_complete=true`、`batch_target_source_complete=false`。现有 `P2HBankEndpoint50Facts` 与 `P2HBankSourceFloor50` 只供应较小原Wu source floor；它们不能证明更大的 copied enhanced bank。k50本身不在本父域所需55键内，这个事实也不能被误报为对其余55键真实h值的反例。没有发现新的原稿数学缺口，尚缺真正增强family/bank解析supplier。

所有代码未编译、未内核验证，正式信用0。原mask/fibre、Δ8 reserve、完整stored-output fold、实际增强W1会计与当前c均继续开放。第一、二批与生产源码未修改。精确来源SHA与模块安装映射见 `REGISTRY.json`。
