# lower_splice 第二批

新增 `P2OriginalMixedThirdBranchTableTrace.lean`，将第一批的优化 mixedWinner 与实际 BranchTable / compactPlan / integerTrace 接通。局部步骤完成；原始完整 lower_splice 目标仍未闭合，task_complete=false。

`mixedThirdRows` 的 rank3 行现在直接来自 mixedWinner 返回的同一个 SelectedBranchData，存入其 whole-box affine infimum 减共同buffer及原query；rank4/5 保留输入 rows（joint 包装器使用真实 rowsForStart），后续门槛仍由同一个 compactPlan 依据实际前代cap重新检查。

证明 `bufferedCap_wRow` 把优化selector的W动作还原为精确 `wCap`，没有重复减buffer；`mixed_selected_actual_licence` 保留 tent支持掩码 与 W独立WBoxCheck的二分，并在buffer≤screen时把tent支持检查降到实际buffer。W不被赋予tent-mask licence。

`mixed_selected_actual_third_trace` 对所有通过物理branchGates的mixed动作证明实际第三Trace cap；W分支的gate由实际mixedWinner来源证明自动提取，无需假设selected-plan或单独row恒等式。进一步证明实际第四choice重测parent就是该Wcap，第四retention同时保留baseline上的首square与第二cube，新第四cube才使用Wcap。

本步保留真实缺口：mixedWinner的严格chamber覆盖和交叉墙损失未证明；tent winner的parent/historical/topCap门槛仍由compiler实际重测，失败继承；优化affine endpoint尚未提供全局缓冲后quantitative convergence。完整reached-frontier parity-policy equality及signed I3 source/mean、presieve、普通Rosser应用仍待推进。未发现新的原稿数学错误。

第一批文件冻结未改，未改生产/Git/看板，未运行Lean、编译、修复、数值checker或额度检查。全部source-only、零正式信用。精确导入与源码SHA在REGISTRY中。
