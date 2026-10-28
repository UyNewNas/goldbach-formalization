# pp_derivatives 第五批：真实各rank log atom 的 Euler 字典

新增 `P5ActualRankLogAtomEuler.lean`，285 行。D 的两处实际定义命名空间已按 root 明确授权修正并重新冻结，E 只消费最终 D SHA `f40cd3b0dbe177c9b2d9d2df3bd6b2f010601f0592a766119456a46bff05d9bb`。本批未编译、零正式信用，原完整 `task_complete=false`。

核对原始 source 后，完整独立 u-side caller/rank list 仍未供应。transfer_lambda 当前确认的真正独立 caller 为 production original247/native-cell/selected-row rank4；lower_square 仍补其它 adopted source-form 归属。rough residual q-coefficient 的 rank 不等于独立 original-prime test 的 rank。因此本批保留该边界，没有造 ranklist 或用零 profile 填补缺失 rank。

当前可推进的真实输入是生产 `PresievedRoughSmoothBoxAtoms.atom`：它对每个 residual rank r 有真正的 separated log-box atom、inner/outer reserve、实际 mesh endpoint 和已证明的紧支撑 Fréchet 预算。E 将这个实际函数提升到全实 prime variables：正坐标处严格取原 log(p)/log(N) atom，非正坐标以零延拓，N<2 按实际零分支。`profile_integer_atom` 证明它在正整数 tuple 上恰是已有 `actualPrimeTupleLog` 原 atom。

实质分析链：从原 weight 非零支撑推出真实正 floor；非正轴附近函数局部恒零，故全实 profile 光滑。正乘法 chart 上保留实际 `log(p_i exp z_i)=log p_i+z_i`，所以原 atom 后接 slope=1/log(N) 的真实仿射线性图。用该连续线性映射的范数、已有真实 atom Fréchet 预算和 log(N)>=log(2) 推出统一 chart tensor 界，再消费 D 的有序 Euler/张量字典，得到每个真实 atom 的完整 syntactic mixedEuler 字段。

`AtomKey = Bool × Sigma(r≤rMax, Grid r n)` 中每个成员都有原 production atom；不是 absent-rank 置零。有限求和构造一个正自然常数，先于所有 key、N、字母串及实点。`finite_rank_bank_occurrence_budget` 保持同一常数先于任意 occurrence count、重复 owner map、U 和 z；真实原字母串仅映射 owner，长度不变。空 rank0 的实际空乘积也在证明范围。

本轮 `local_step_complete=true`，但原 caller 到这些真实 rank/atom key 的完整身份还未供给，Family 的实际 lower/product margins 和完整 same-rho PP 仍开放，故 `batch_target_source_complete=false`、`task_complete=false`。此为形式化实现衔接缺口，本次未发现原稿数学缺陷。raw SHA、安装映射和剩余义务详见 `REGISTRY.json`。
