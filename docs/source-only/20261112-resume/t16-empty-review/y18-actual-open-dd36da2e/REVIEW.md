# Y18 开放提案实际 Git 树独审

**本地提交和整树通过核对。** 从私有 `output/t-batch-20261110/publish.git` 的原始 commit 对象重新计算出 `dd36da2e1de4f0fdd056a0096243928c1fb41ce9`。其唯一父提交为 `356c3782e9428098a2fcbfb18c689bef264d84fa`，实际根树为 `6f2672eac296bfc8bff15477d51633d1b58f8fe4`。每个 Git 读命令均指定 `-c protocol.allow=never`，并禁用按需下载、replace 对象和可选锁。

实际树包含 14,280 个文件路径。逐字节读取了全部 13,320 个不同的 blob 和 1,721 个 tree，分别合计 1,032,682,803 和 1,058,605 字节。每个对象重新计算 Git 原始 SHA-1，并分别计算 SHA-256。按路径汇总的整树内容清单 SHA-256 为 `da36f179518d8ed6f76c59786f02bedf5d7992b9c63a5b083d6370dbe67957d5`。

对照直接父树，14,231 个路径继承的模式和对象 ID 完全一致，48 个路径新增，1 个修改，0 个删除。49 个变更文件共 6,534,795 字节。逐个核对实际 Git 原始内容、冻结时的独审清单、发布暂存 payload 与 PREPARED 收据。仅两份变更文件是 Lean 审计源码，即 CandidateAudit 和原 Round6Audit。实际 8 个 workflow 的原始字节全部匹配，唯一修改的原有 workflow 是 variable-envelope，其中只增加指定分支的 push 排除行。新 workflow 的窄 push 条件和原共享并发组均匹配。

实际外置选择 SHA-256 为 `e91d70ef0fb18859d9137c5424e6a104d25d5e70c50ddbc6278c04572440ce61`。它保留 `deployment_authorized=false` 与 `reuse_decision=null`。实际树里没有 Y18_P2R3_REUSE_DECISION.json。若之后采用可部署选择或新的复用决定，须核其新提交和证据字节。P2r3 第 12 步的失败原因以独立终态日志为准，本回执不据此判断 FinitePiIntegral 或 28 个共享源的对象状态。

本次核对只覆盖上述实际本地开放提案。未执行 Lean、Lake、stage 或任何证明，没有查询或写入远端，没有发布或排队 Y18。原冻结签名保留在先前目录；本次逐对象与逐路径证据在 ACTUAL_TREE.json。
