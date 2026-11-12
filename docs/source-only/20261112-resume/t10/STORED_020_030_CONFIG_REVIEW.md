# Stored020–030 配置独审

**准予按三个精确文件准备独立远端验证。** 父提交为 `356c3782e9428098a2fcbfb18c689bef264d84fa`，分支为 `ci/stored-blocks-020-030-20261112`。`STORED_020_030_SCOPED_CONFIG_ALLOWLIST.json`（SHA-256 `f980f86f9934d08812d56b24a047f09c00232655b1f93195a6b9a6614d5881e6`）逐件列入原始及新文件的 SHA-256、Git blob、字节数，以及 12 个原始输入的固定路径和身份。配置本身未执行。

三件改后共 17,647 字节。逐一解析父树七个工作流的实际 push 规则，新的三路径提交只匹配 Stored 作业。VE 的唯一变化是忽略新验证分支，另外五个工作流的字节完全相同。原 `workflow_dispatch`、`goldbach-p0-heavy` 和 `cancel-in-progress: false` 均保留。发布时需检查同组已有的 pending 作业，避免用新排队项替换它。

从原 `124d09f9fc74e7b78261e2471a573f1657b5633e` 树读回 11 份字面源码及真实父类型。每件大小、SHA-256 和 blob 与 v3 清单相同。每块存在唯一预期 `source_index_at` 旧 proof 文本，基址为 `4096 * block`，并保留 `rows_size = 4096`。两个 range 变为 20–30，记录索引改为 `block-19`，对应 `modules[1]` 至 `modules[11]`；`modules[0]` 是父类型。原生成器的分块证明表达式、快照、全声明核验与 replay census 原样保留。Stored000–019 未列入这次 12 项目标与重放。

从来源安装、12 GiB trust-zero guard、依赖锁定，到编译、checker、完整声明类型/传递公理、运行时审计的全部步骤与成功运行 43122130246 的父配置相同。归档增加父类型源码及实际 `.olean*`。即使未来成功，需独立核验 GitHub artifact 后方能确认新增 `[81920,126976)` 的长度和下标。当前 72 块与 143 块职责均没有变化。
