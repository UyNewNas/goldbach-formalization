# lower_square 第四批：真实 marked-pair receiver 与第五层冻结身份

本批新增 3 份局部闭合源码，共 655 行、26 个定理（16 个公开、10 个 private）。前面三批源码保持冻结。本批 `local_step_complete=true`，但 `batch_target_source_complete=false`、原完整 `task_complete=false`。未编译、无内核信用，正式信用为 0。

首先核对了两处实际实例边界。旧 `CompactStart` 只有普通起点 a/h，其坐标上界不能覆盖 L6 外部第二素数一直到 `D=59/250`；旧 `compactPlan` 的 rank3 父层级又硬编码普通 `baselineCap`，不能替代 marked L5/L6 enhanced pair 的真实 piecewise root level。此前条件定理本身仍成立，但不能由此声称完整 marked-pair 采用已完成。这些是接收器实现边界，不是新原稿数学缺口。

`P2OriginalPairSourceReceiver.lean` 因此建立真正的 `[epsilon,D]` pair code/有理盒；未来 rough 素数仍由原 rough carrier 保留单独的 a ceiling，未把外部范围当 rough cutoff。它复用原始 `SourceForm.affine`、`supportMask`、`formRankEligible`、whole-box winner gap、`stableBase` 与 inherited-first ties，而不另造目标许可。实际点到其有理上端点的包含关系已证明，再从有限 full/selected-complement strict squares 推到同一真实 SourceForm 点上的两组门槛。

同一文件的 `pairPlan` 显式接收真实 pair seed。第三层从该 seed 读取，第四/第五层从同一 plan 已冻结的第三/第四 cap 读取。`pair_run_three_cap` 给出实际 warm root 经三次粗素数更新后的第五层 cap；`actual_fifth_source_cap` 直接由实际 selected source 和 primitive `freshCheck` 推出其精确 row cap。第三批额外要求的 scalar row-to-Trace `hcap` 身份，已在该局部路径上消除。`freshCheck` 只保留整数测试之前的 parent<candidate、candidate<=top 和当前偶层 arrival 原始不等式，没有把最终粗支持作为前提。

`P2OriginalSelectedPairNativeData.lean` 把 root seed 接回原始 U5/U6 piecewise level，再减显式 double buffer；没有换成普通 nu baseline。它构造 native U5 的实际 rho policy 和 native U6 的 `LowerData` 实例。U6 的原始 w/L 函数与外层 E 补集均保留。非零 native 系数现在由这个明确构造的 policy 恢复真实 rough carrier subword 与 accepted run，不需要假定任意旧 policy 等于它。该对象仍是待采用的 source-only candidate，不能因此声称全库已有任意 policy 已被证明采用它。

`P2OriginalPairFifthOnceBufferedSupport.lean` 再把实际第五层 SourceForm、已计算的 H5 cap、真实 accepted rough 后继串联起来，输出 once-buffer physical cap 的完整及 selected-complement 两组整数平方门槛、原选中标签不变，以及 `product * L < N^physical`。这里没有 hcap 输入、没有 hRoughWell 输入、没有最终模数预算输入；L<=N^buffer 仍作为几何阶段预先分配的小层级条件公开保留。

另外，`pairPlan_fresh_cap_bound` 已交给 transfer_trace。本文件给出任意 incoming<=153/256 时实际 finite choice freeze 仍<=153/256，邻任务据此接真实 pair raw/rank 与 rounded sigma support；本任务没有把粗支持结果伪装成 already verified。

完整目标仍缺：覆盖全部实际 adopted L5/L6 chosen words 的 finite bank 和 fresh/inherit/short 分类、真实紧截断 epsilon 与统一 buffer allocation/墙损失及共同收敛、W 独立算术许可与完整 mixed bank、全部 canonical factor/collision 与最后同 rho 的 small Rosser / AP/BV/PP / signed mean。原 `formRankEligible` 明确排除 W，本批没有悄悄放入。短秩和继承分支不被强行塞进 fresh rank5 定理。本文未声称全 lower、c 或最终主定理完成。

REGISTRY.json 登记本批每份源码、所有关键 source-only 安装映射与实际 raw SHA。只做数学/source 静态自审及哈希、占位 token 扫描；未运行 Lean/lake、编译/修编译、checker、测试、Git、额度检查或新子代理。