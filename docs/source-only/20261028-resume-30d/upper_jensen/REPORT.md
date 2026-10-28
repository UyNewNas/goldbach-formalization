# upper_jensen 第四批交付

新增三份 Lean，共465行、25项声明，写入本任务30d目录；前三批源码保持冻结。`REGISTRY.json` 登记原始SHA、每个source-only依赖、安装模块名和残余前提。未运行Lean/lake、内核审计、数值checker或额度检查；正式信用为0。

第一模块 `P5AllChildrenReserveReassembly` 对任意grid400 raw父盒，证明实际 retained/omitted 集合均为同一64个child的互斥并。以常数1的真实有限积分证明real体积精确可加，再得到

`sum64 childOwnerReserve = B*volume(rawOmitted) + modulus(e)*volume(rawRetained)`。

所以同一个raw父质量只支付一次，没有64倍，也没有decoded owner数量因子。这是child Jensen reserve对接实际raw B13银行的精确接口。父盒体积取自实际B13模块的 `rawBox_volume`。

第二模块对两个原始严格margin named父给出更强的几何结论。它逐点消费现有 `parent0/1_namedJ5_rawOwnerDomain` 与原始selected membership证明，结合共同decoded完整覆盖；并从字面正坐标和上界证明整个rawbox在原ambient内。因而128个actual child都被真实namedJ5 owner保留，omitted集合**等于空集**。这不是把遗漏体积小当作前提，也没有把任意一般trim当作零。

据此，每个父的all64 reserve恰为 `rowModulus(raw,e)/400^5`。先从真实连续模量的有限银行选择正有理e，再选择共同complete refinement q，令chi=e/20；沿原始owner licence证明全覆盖，并使两个父合计的128-child reserve小于任意给定eta。最后 `exists_named_actual_integral_ge_Jensen_sub_tolerance` 将此连接到原始可变第四/第五 `fullSelectedIntegral`，得到实际有限named策略的积分至少为symbolic all128 Jensen总和减eta。所有原始第四Geometry、gate、key与同一族来源保留；没有假设目标积分。

一般crossing/B13 adopted-bank schedule由upper_mesh并行推进，本交付提供其所需的child→parent exact reserve映射。一般raw银行可能保留非零baseline trim，不能仅缩小e就推其消失。两个named父的结论没有扩展为完整历史archive，也不识别full adopted J5。

尚无完整历史archive的Q80/atanh整数floor/byte绑定、symbolic Jensen数值总和、全银行trim预算、全局u分配、same-rho解析估计或最终K。没有新原稿数学缺口。本轮实际named局部有限策略已写出完整源码；广义任务及全银行batch目标仍开放：`local_step_complete=true`、`local_named_policy_complete=true`、`batch_target_source_complete=false`、`task_complete=false`。

当前批自审修订：实际积分末步显式调用既有 `selected_namedJ5_eq`，使 selected-owner 和与 namedJ5 和对齐；未增加数学前提，未编译。第二源旧SHA `20900c8c94c97c1c2468b7c26e89959107f5aaa7be71604b2586b8966e0e9b69` 被新SHA `9c440bf9c9ebea9afb08f909ca7e27e30edb076d24f82e93e3e4495b2c0652fc` 取代，首源和所有前批未改。

新增第三模块 `P5SharpQ80ActualFinitePolicy`，直接消费upper_fifth第四批冻结的原始sharp directed-log/Q80 soundness（子块真实改进b_C，不替换成旧parent b）。它定义未求值的128项rational floor总和并证明非负，再利用同一个实际zero-omission/common-buffer schedule，将该symbolic sharpQ80总和减任意eta接到原始actual fullSelectedIntegral。真实log界、向下floor、d≤0零分支均来自该独立证明源码；本consumer不增加目标floor/积分前提，也不计算任何Q80总量。其冻结依赖SHA `326346be7336aee65f58ff8ee8680e50a48e1ed16704844f5f3eba63def00c58` 已登记。
