# lower_tail 第四批

交付两份 Lean 文件，共 274 行、12 条定理。30c 的两个 raw SHA 保持冻结；本批也保留固定网格 knot 半径扩大的结论。

`P2UpperActualSelectedClampReserve.lean` 将实际静态选中 policy 的正 excess 精确接到现有的 `JointNearCapPointError.policyExcess`，并证明原始联合 source 中整块 clamp 的真实 `1/phi(fullPrefix)` 加权 excess 至多为既有 `jointTotalError`。由已经写出的 `exists_uniform_joint_native_reserve`，得到一个网格 m 和阈值 N0，先于所有 N 和原始移动 E，统一支付 `nativeClampCost <= originalClampCost + epsilon`。该供应内部使用实际四质数 prime-box mass 的 Mertens/PNT 极限和 proper affine strip 支付；本批没有再假设 boundary mass、最终 mean 或 `PrimeIntervalMertens` 结构。

`P2UpperActualH248DensityDefect.lean` 解决的是不能略过的计数语义边界。它把同一实际 sigma 的物理密度精确分解为 `densityScale * tableHarmonic + densityDefect`，其中 defect 是逐个真实 ordinary row 的实际密度减去归一化 H248 cost。新的原始 count 上界明确保留这个 defect、真正 fallback sifted counts、同 sigma 的 singletonPP 和已经支付的 primitive correction。没有把 defect 设为零或把 h248 均值当新前提。

本批还形式化了一个具体实现障碍：实际 `actualSmallRosserPlus` 行在物理 query 不超过 3 时，其已证明 ordinary-F 极限为 `4/R`；而增强 nativeCost 是 `4*(1-H248)/R`，两者差严格等于 `4*H248/R`。对实际固定 query 位于 `[2,101/50)` 的认证行，序列化 H248 的值严格为正，所以该普通行的归一化密度不可能最终小于等于增强 cost。这定位了当前“ordinary rho 直接识别为增强 H248 密度”的错误捷径。它不是原稿反例；原稿增强筛法需要接入自身真实附加修正和 count 语义。

仍未完成：增强 h248 count/mean 供应及其真实修正系数连接、原始 fallback 的 switched/prime-product 支付、最终 PP 与 lower functional。这里给出的是实际 clamp cost 的支付和精确未支付残差，完整任务保持 `task_complete=false`、本批目标也为 false；窄步骤 `local_step_complete=true`。

全部是文本闭合的 source-only 代码。没有编译、Lean/lake、内核、数值 checker 或 CI；正式信用为 0。源码及实际 prime-box/Mertens、ordinary density 和 table 前驱的 raw SHA 均在 `REGISTRY.json`。
