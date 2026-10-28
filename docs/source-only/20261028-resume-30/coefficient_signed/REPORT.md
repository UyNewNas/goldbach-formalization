# coefficient_signed：同一物理系数的有限 owner 展开

已输出 `P5All16PhysicalOwnerDiscrepancy.lean`，共 6 个新引理。该文件文本闭合；未编译，正式验收信用为 0。

证明从真实 `OriginalJointPresievedCompiler.jointPresievedSigma` 出发，不把系数等式或 PP 结论当假设。先由原库已证明的小/粗素因子分解唯一性，把每个物理 residual carrier 拉回同一个 `(e,d)`；再对每个真实 retained `d` 使用 PhaseE 的 owner-word 分解和 `physical_joint_row_raw_value`。`Z≤N` 由实际 all16 compiler 推出，调用者只需 `1<N` 与 `0<eta`。随后按原始 mark 集求和，得到任意 signed 测试函数的完整有限展开。

`physical_owner_sigma_eq_joint` 用有限指示测试逐点证明新 owner 展开读出的系数就是原 `jointPresievedSigma`。`joint_signed_PP_owner_expansion` 对同一个模数 `fullPrefix(t)*(e*d)` 同时展开真实 count 与 exact coprime reciprocal-totient mean。代码使用完整 `ordinaryTuples`，包括 W 和零行；没有使用排除 W 的旧 `tuples`。marked `t`、残余 owner 词 `J` 与独立 Part3 测试词 `u` 分别保留。原始 upper gate、粗素数符号、共同 beta 与 residual `M_res/k!` scalar 各出现一次，不引入第二个 marked factorial，也不引入 `mu(q*product(u))`。

这消除了 retained-domain 的全局 same-rho 有限求和衔接，但没有完成整个 raw-to-physical 目标。新族仍以真实 `fixedRoughSupport` 为索引；还须证明 unrestricted 全 k 的平方自由投影反向覆盖、rank exhaustion、owner orders 到 sorted blocks 的 regroup，以及 repeated-rough 在 count/mean 两边各自的绝对误差包络。也未证明 PP 渐近估计、未把旧 all-prime native sigma 等同新 common-beta coefficient。因此 registry 的 `task_complete=false`，不计主定理闭合。

本次未发现原稿数学缺口；上述剩余是形式化实现与实际对象连接。未运行 Lean、lake、数值 checker 或 CI。直接及关键传递依赖路径、命名空间、声明与 SHA256 已记录于 `REGISTRY.json`；draft imports 尚未安装验证。
