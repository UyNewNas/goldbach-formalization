# coefficient_physical 第三批交付

新增 `P5OriginalPhysicalFullPolicyFibre.lean`，文本闭合，未编译，正式验收信用为 0；原完整目标仍未完成。

本批消除了上一批对**当前实际 corrected physicalPolicy** 保留的 oddified/full-root 拓扑边界。证据来自正确的 Phase7 文件 `P5OriginalAboveMuThirdLowerPhysicalCoefficient.lean`：`thirdReplacement` 使用 `ordinaryParityRosserPolicy false`，且已有 `final_even`。第三前缀是奇数秩，因此其后相对剩余问题是 lower residual；这不会把全球 Bool policy 的 lower 参数改成 true。全球偶数秩仍应保留。

新代码先给出一般策略的精确条件：`oddFirstExitPolicy (R false)=R` 当且仅当每个 `R true pre=true`。随后实际调用 `final_even → family_even`，证明 corrected third、sixth、eighth 全部 splices 组成的 `physicalPolicy` 在所有历史上都满足该条件。此结论不需要假设全局 cap 供应或密度估计。

由此证明 arbitrary prime weights/carrier 上**完整根叶记录**相等，包含 selected word、正负号和 mass；fixed rough support、Mobius lookup 与同一个 physicalRho 的 full-policy attachment 全部接通。第二批的 H3 局部叶 filter 与 active q 唯一纤维也提升为该完整 physicalPolicy 的真实根叶，而不只停留在 oddified carrier。

`physical_third_branch_global_upper_tests` 进一步写明适用范围：在第三 selected-pair 分支并且深度 4 至 6 时，偶数全球节点绕过，奇数全球查询使用第三祖先冻结 cap 上的原 upper admissibility。六阶之后有 later splice，不能直接沿用旧第三分支 cap；全局 even-retained 性仍保持。

这是已有正确前驱的接口补接，不是新发现原稿数学缺口。对任意不满足 even-retained 的 Bool policy，本文件不宣称拓扑相等。原完整目标仍缺全球合法因果 cap、87 域 owner/coverage、不交、局部算术纤维非空、积分及同系数密度 telescope、K 和 PP。第二批及第一批冻结文件均未改动；精确源 hash 与直接、必要传递依赖见 REGISTRY。
