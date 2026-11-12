# Y18 driver 提案独审

**冻结提案的静态配置通过，可构造本地待审 Git 树。** 提案作者的 REGISTRY 为 `04bf5be5b34cdee334f03e51b385aa82fd7f68edd2da5b7b41c4290923bc5725`，实际 workflow 为 `28888819eed559bf3ad8c768361658a6df0493cde9aca9943f9fc0f5536702ba`，外置选择草案为 `e91d70ef0fb18859d9137c5424e6a104d25d5e70c50ddbc6278c04572440ce61`。已从本地冻结文件逐项复算全部 14 份作者文件的字节数、SHA-256 和原始 Git blob SHA-1。

## 确切落盘路径

父提交固定为 `356c3782e9428098a2fcbfb18c689bef264d84fa`，原树为 `c0cee91c752ed35e9e5331ba74207606fa440c37`，分支为 `ci/y18-empty-mother-20261112`。提案按 49 个变更路径签署。其中有 35 个已审候选文件，即原 registry 的 34 项及 registry 本身，有 11 个 driver 文件、两个实际 workflow 文件和一份外置选择。相对父树新增 48 个文件，修改一份原有 workflow。原候选的作者 ALLOWLIST 在外置选择中保留来源 SHA。

从父 Git 树重新提取原七个 workflow。六个字节完全相同，variable-envelope.yml 仅增加这一分支的 push.branches-ignore 单行。新增 workflow 只匹配该分支和自身路径的 push，沿用 `goldbach-p0-heavy`、`cancel-in-progress: false` 和只读权限。完整 8 个实际 workflow 及 49 个拟变更路径的模式、来源和双散列见 PROPOSED_TREE_PATHS.json。

新 workflow 的 14 步已解析，9 段 shell 及实际证明子 shell 均只作了 Bash 语法解析。初始步骤在 checkout 前由 RUNNER_TEMP 和 GITHUB_WORKSPACE 建立可用路径。主 checkout 取两层历史，绑定器从实际 commit 读取唯一父提交，对照实际 HEAD、完整变更路径、外置选择、磁盘字节和 Git 对象。固定 PYTHONDONTWRITEBYTECODE，末次复核会再次检查已安装文件集合。归档、安装和数学调用均未执行。

## 实际运行合同

候选 registry `ad2f974d49c24296cd2f7fd079d78e60c56dcc5aa96180064b1ef4289b8f7568` 和 manifest `8c48f34f4479b13cb38749360df78ed06f1d80ddee646472579ad0f1e214a496` 与前次独审逐路径一致。原 13 个 List API 替换、61 个备用原生版本的取舍、六个原生生产者锚点、两份新源的 17 个原定理及两套公理输出随选源保留。实际编译要求覆盖 337 个项目和 1,348 个原生模块。严格完整声明、所有权、类型和公理核对覆盖其中 797 个数学模块，内核重放另外包含实际生成的 CandidateAudit，共 798 个模块；888 个标准原生依赖仍须具备逐项源码、setup、实际编译及产物绑定。

实际 workflow 按顺序调用源的前后复核、带原参数与锁的编译、wrapper、快照、checker、最终 audit 及 17 项专项核对。setup 的已选直接和传递输入与真实规范产物相连；wrapper、checker、audit 的实际二进制、有序 LEAN_PATH 和已用对象前后散列最终与 checkpoint 相连。FinitePiIntegral 的原硬拒绝仍在。如 wrapper 审计在该处失败，已有输出和诊断进入隔离留存，完整 798 重放的成功条件仍未满足。

360 分钟作业自首步起把数学阶段限制为 285 分钟，超时发 TERM 后 30 秒可发 KILL。末段为运行时复核、checkpoint、总收据和产物上传预留 75 分钟。运行时检查、实际产物捕获和上传均设 always，原总收据仍须此前各门全部成功。未创建项目或运行时的失败有单独的状态日志。具体可留存的字节依赖本次实际产出和上传结果。

## 外置决定与下一次复核

这份外置选择明确保留 `deployment_authorized=false` 和 `reuse_decision=null`。当前 49 路径的树若被执行，select 会在启动证明前拒绝。独核本地 P2r3 v4 的 32d54188 源清单，28 个同源模块的 SHA 均与 Y18 一致，其中包括 FinitePiIntegral。两个项目的工具链和依赖锁相同，P2r3 项目 lakefile 的 Git blob 为 `c7b839a2240d9960fb1f01f0e8808a9459935e0e`，Y18 使用 `5891a201863f0edffc5028406724d6bc970cc892`，两者有效项目配置有差异。

根将在收到 P2r3 运行 43186809155 的终态日志和实际对象收据后判断共同失败、修补和对象复用情况。采用决定后的外置选择，以及新增的 Y18_P2R3_REUSE_DECISION.json，须按将入 Git 树的实际字节另审。若须改候选源或采取已验对象恢复，须另审相应变更。此次没有实时远端查询、新的真实 driver commit、CI 运行或内核及缓存验收。
