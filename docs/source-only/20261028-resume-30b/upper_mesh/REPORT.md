# upper_mesh 第二批：实际 literal kernel 模量

交付 `P1OriginalFifthLiteralKernelModulus.lean`，27 个声明，文件文本闭合。未编译、未执行 kernel/checker，正式信用为 0。本次窄步骤 `local_step_complete=true`，完整 upper_mesh 原目标仍 `task_complete=false`。

第一批留下的 `hmodulus/hzero` 现已用具体对象供应：

- 固定实际正坐标紧立方体 `K=[1/400,19/96]^5`；真实 grid400 且所有 lower key≥1 的 `rawOwnerDomain` 由原始域定义落在 K。
- 使用同一 `literalRawKernel(e,raw,t)`：保存的原始 mask 仍给可变 `M_I(t)-2e`，旧项仍为 tuple-dependent `rawFourth(t)-2e`，没有冻结成常量。
- 利用实际 canonical lower factor 的全局连续性，将严格 own-cube profile 在正 tuple 上精确改写为零延拓 factor。由此证明 `(e,t)` 的联合连续性，包括严格门槛等式面。
- 将 `max(0,literalRawKernel)` 放入真实 `C(K,ℝ)` 空间，由 compact-open/sup-norm 指数律得到整个 family 在 e 上连续。定义 `rowModulus raw e=‖f_e−f_0‖`，直接证明其连续、在0为0、非负，并逐点控制真实 kernel 差。
- 在物理 buffer 紧区间 `[0,3/51200]` 再组成一层连续映射，取 `rowMassBound raw=max(1,‖bufferFamily raw‖)`，得到所有 e/t 的共同有限质量界。该 M 不依赖 mesh q 或 decoded child 数。

`finite_bank_modulus_inputs records` 恰给第一批 `exists_joint_buffer_mesh_complete_cover` 所需的 `hmodulus`、`hzero` 及实际 `M≥1`。本文件没有重新包装 buffer schedule；直接提供具体 modulus/massBound 即可代入。

语义范围：这里的 literal kernel 是 MI 减去 fifteen-tent+W rawFourth majorant 的保守原始行 kernel；它与任意实际 licensed old4 的恒等式没有被断言。后者仍由既有 lower comparison 的真实祖先/Geometry 前提约束。

仍欠实际 selected/firstStop crossing 的一维截面界及 B13 逐行积分误差、历史归档每行正key/selected/firstStop判定或 omitted-child trim、全87域共用祖先与 K reserve绑定。因此全 upper_mesh/upper/K 继续开放。窄审阅未发现原稿新缺陷。

直接导入、定义依赖和前驱的精确 SHA、安装映射及使用方式见 REGISTRY.json。未修改第一批、生产源码、Git或看板。
