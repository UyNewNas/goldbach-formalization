# C9 Core CI 终态与 VE 范围回执

记录时间：`2026-10-12T05:45:13.527685+00:00`。审查者：`/root/p3_p4_intake`。

**C9 的 Core CI 实际运行后以 `cancelled` 结束：全项目构建未完成，根内核重放与根公理审计均为 `skipped`。同一提交上的独立 VE 检查成功，覆盖八个明确模块、358 条所属声明。Core 日志还提供了当时七个新增生产模块全部 `Built` 的直接证据。**

## 1. 固定身份与工具链

| 项目 | 固定值 |
|---|---|
| 形式化提交 | `c9f407efe66240c08c2e8a678330ba7b98b74db5` |
| 提交 tree | `c818607f1ffda6246cf1d03dd9a5dbb557c94be3` |
| 集成分支 | `chatgpt/chen-p0-integration` |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 手稿提交 | `ba6ec11d800eccc54406490631895e174de85766` |
| 工具链 | `leanprover/lean4:v4.33.0-rc1` |
| Lean 可执行文件 commit | `62eed1db4d67327ec8120be05f1a1b0847d74561` |
| Mathlib pin | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| Goldbach pin | `09b97db5764ade1246bfb77206baa1b124760958` |
| lean-action pin | `f061402b660e0c34644504b324e830f2991d4865` |

两份原始日志的 checkout 后 `git log -1 --format=%H` 均打印完整 C9 SHA。此回执审查的是固定 [C9 源码](https://github.com/UyNewNas/goldbach-formalization/commit/c9f407efe66240c08c2e8a678330ba7b98b74db5)。只读观察到的本地集成 HEAD 为 `278f949444748a30b5165ff47bfa283ab0bad0d8`，它不改变 C9 CI 的源码身份。Root 另明确报告：C9 运行期间从未更新该集成远端 ref；这里将该操作历史保留为 Root 的陈述，没有把它伪装为已独立核查的全部远端事件。

## 2. Core 终态、真实 runner 与时限

[Core run 38205485501](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38205485501)，job `114667925695`，第 `1` 次 attempt，事件 `push`，工作流 `Lean core verification`。API 终态为 `completed / cancelled`。

| 时间证据 | UTC |
|---|---|
| Run created / started | `2026-10-12T04:51:30Z` |
| Runner 第一行日志 | `2026-10-12T04:51:34.5809561Z` |
| 全项目 build 阶段开始 | `2026-10-12T04:53:22Z` |
| 最后一条 Built | `2026-10-12T05:36:45.4599294Z` |
| 取消错误 | `2026-10-12T05:36:46.7524377Z` |
| 最后非空日志 | `2026-10-12T05:36:48.8532523Z` |
| 终态 run updated_at | `2026-10-12T05:36:51Z` |

Runner 日志明确记录 GitHub Hosted Compute Agent、runner `2.337.0`、Ubuntu `24.04.5 LTS`、镜像 `ubuntu-24.04 / 20261004.327.1`、Azure `eastus2`。准备、工具链安装、Lake/Mathlib cache、全项目构建均有实际步骤和输出。因此本次是实际执行的 CI，不能记成“没有 runner/steps”。简化 job 响应没有 runner id/name 及 step 完成时间字段，这些缺失值没有解释为 `0` 或没有运行。

[C9 固定 core 工作流](https://github.com/UyNewNas/goldbach-formalization/blob/c9f407efe66240c08c2e8a678330ba7b98b74db5/.github/workflows/lean.yml) 第 14 行是 `timeout-minutes: 45`；线程数 `2`，根 replay 与 audit 各有 `25`、`10` 分钟步骤时限。run 开始到取消约 `45 分 16.752 秒`，与 45 分钟 job 时限相符。**取消原因仍标为未确认**：原始日志只写 `The operation was canceled.`；尝试只读获取完整 job 与 checksuite/checkrun 信息均被连接器以 `INVALID_ARGUMENT / URL is not an allowed ... endpoint` 拒绝，未拿到 timeout annotation。没有重试、绕过、重跑或取消 CI。

### 三门与辅助步骤

| 步骤 | 实际结果 | 接收解释 |
|---|---|---|
| Build the full project | `cancelled` | 全项目 build 不通过；存在下列七个目标的局部成功证据 |
| Bundled leanchecker — ImbalancedChen | `skipped` | 根内核重放没有运行 |
| Root declarations/transitive axioms | `skipped` | 根公理审计没有运行 |
| Record required verification outcomes | `failure / exit 1` | 正确拒绝把取消或跳过视为成功 |
| Retain logs and timings | `success` | 只表示日志留存成功 |
| Optional cache capacity/save | `skipped` | 不影响三门必须完成的要求 |

全日志扫描没有发现任何真正的 Lean `error:`。首个 CI 错误是取消；随后 `Process completed with exit code 1` 来自必需结果的 shell 检查，不是 Lean 诊断。`ring` 的“failed to close”文本均是 `info` / `Try this` 建议，所属模块带有成功 `Built`，没有据此记 Lean 失败。最后进度是 `9643/9786`，模块 `MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityProducer`，并非完整构建成功。

### C9 已实际编译的七个新增生产模块

下表只记 Lake 在这次 Core CI 中报告的普通编译成功；原工作流 `BUILD_ARGS` 为空，不能将它升格为 P0 的 strict 三门回执。七个模块既有的 P0 strict/replay/axiom 核验继续按各自固定源码回执记录。

| 模块 | UTC | Core 原始日志行 |
|---|---|---|
| `ImbalancedChen.CurrentChenBuchstabRefinement` | `2026-10-12T05:25:01.2633618Z` | 2547 |
| `ImbalancedChen.Certificates.RationalLogCertificate` | `2026-10-12T05:23:56.1881590Z` | 2513 |
| `ImbalancedChen.Certificates.PairedFibreIntegral` | `2026-10-12T05:23:54.8869453Z` | 2512 |
| `ImbalancedChen.Certificates.PairedCertificateChecker` | `2026-10-12T05:24:22.2527116Z` | 2527 |
| `ImbalancedChen.Certificates.PairedV2Data` | `2026-10-12T05:24:44.7095623Z` | 2538 |
| `ImbalancedChen.Certificates.PairedV2` | `2026-10-12T05:25:03.9713645Z` | 2548 |
| `ImbalancedChen.CurrentPairedBuchstabBridge` | `2026-10-12T05:25:29.6366319Z` | 2572 |

C9 根文件第 248–250 行已经导入 Buchstab、PairedV2 及 Buchstab bridge；PairedV2 引入检查器和数据链。因此不能把“旧根入口未导入”套用到这七个模块的 C9 状态。此处有真实局部构建证据，但没有根构建完成、根 replay 或根 audit 的证据。

## 3. VE 成功的精确范围

[VE run 38205485520](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38205485520)，job `114667925525`，terminal `completed / success` 来自既有正式 job 回执；其原始日志在 `2026-10-12T04:54:26.8145579Z` 输出 `PASS: 358 declarations`，在 `04:54:26.8433350Z` 记录 `verification=success`，最后日志时间为 `04:54:27.9565817Z`。没有把日志时间写成 API 未提供的 `completed_at`。

实际入口为固定 [verify_variable_envelope_boxes.py](https://github.com/UyNewNas/goldbach-formalization/blob/c9f407efe66240c08c2e8a678330ba7b98b74db5/verification/verify_variable_envelope_boxes.py)，声明归属审计为 [VariableEnvelopeBoxesAudit.lean](https://github.com/UyNewNas/goldbach-formalization/blob/c9f407efe66240c08c2e8a678330ba7b98b74db5/verification/VariableEnvelopeBoxesAudit.lean)。

| 范围 | 模块 |
|---|---|
| 六个明确生产目标 | `ImbalancedChen.VariableEnvelope` |
| 六个明确生产目标 | `ImbalancedChen.VariableEnvelopeConsequences` |
| 六个明确生产目标 | `ImbalancedChen.VariableEnvelopeRegularity` |
| 六个明确生产目标 | `ImbalancedChen.VariableEnvelopeScaled` |
| 六个明确生产目标 | `ImbalancedChen.VariableEnvelopeBoxes` |
| 六个明确生产目标 | `ImbalancedChen.VariableEnvelopeCertificates` |
| 两个边界回归目标 | `verification.VariableEnvelopeBoundary` |
| 两个边界回归目标 | `verification.VariableEnvelopeBoxesBoundary` |

六模块明确 `lake build`、两个边界回归编译、逐一 bundled `leanchecker --verbose MODULE`、358 条归属声明的传递公理审计以及 Python reference 回归均有实际 `START/PASS`。允许公理是 `propext`、`Classical.choice`、`Quot.sound`。358 按定义模块枚举，包含私有和自动生成声明；旧匿名边界 example 不一定成为持久声明。

该入口自己限定为三变量区域 `0 ≤ z ≤ y ≤ x ≤ 25/128`；不覆盖延展的 `x ≥ μ` 表达式或完整数值证书。它不导入或审计 P0 新增的九个生产组件，也不能替代完整 `ImbalancedChen` 根的三门。C9 仅含其中七个新增组件：`AboveMuSecondCoarse.lean`、`Part3LongSlotDistribution.lean` 在固定 C9 tree 中不存在，不能让 C9 的 VE 或 core 结果覆盖这两个后续文件。

## 4. 留存证据与接收结论

Core 日志 artifact 已上传：[lean-verification-38205485501-1](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38205485501/artifacts/11727984561)，ZIP `29951` bytes，上传日志报告 SHA-256 `8b3e3ce886eb1779350685ec166ecb58bc9725d59af9728a0a3e0e3152814471`。VE artifact：[variable-envelope-38205485520-1](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38205485520/artifacts/11726869041)，ZIP `43149` bytes，报告 SHA-256 `2d788a3035c9bc96a285b45ebf580303501c617546059e13b0b168b374840858`。本次未下载 ZIP；这两个值是上传工具的原始报告。

| 本地原始证据 | 重新计算的 SHA-256 |
|---|---|
| [c9f407-core-terminal-jobs.json](sandbox:/workspace/scratch/535d89efd063/p0-round2/c9f407-core-terminal-jobs.json) | `4835fae1bbc80c7998050c2b03330caed532831994535148e410a4342b503644` |
| [c9f407-core-terminal-run.json](sandbox:/workspace/scratch/535d89efd063/p0-round2/c9f407-core-terminal-run.json) | `1c6fb151a04a68c9d685f1cf5ecfc32185ceb19db9d8adbba4ab8dbd3ee84709` |
| [c9f407-core-job.log](sandbox:/workspace/scratch/535d89efd063/p0-round2/c9f407-core-job.log) | `07fe94f0139dda18448126384183e1d3a27c251fc0be0225b63e7fff314368f2` |
| [c9f407-VE-job.log](sandbox:/workspace/scratch/535d89efd063/p0-round2/c9f407-VE-job.log) | `c44b06441a81e74a8b1c0f7f2606013fb54d39ec08ce9a89b40e36392b386647` |
| [p2-first-bridge-actions-progress.json](sandbox:/workspace/scratch/535d89efd063/p0-round2/p2-first-bridge-actions-progress.json) | `dd7064ddb0da2f7fe96e399830776927cef82a0428fd5bd75ef4b35a90b20047` |

配套 [JSON 回执](sandbox:/workspace/scratch/535d89efd063/p0-round2/c9f407-terminal-CI-receipt.json) 保存完整 job steps、八模块全部阶段时间、七个已编译模块的固定 source blob/SHA-256、固定工作流哈希、访问阻塞原文与范围界限。

接收结论：**Core 完整三门未通过；VE 八模块验证通过；C9 七个新增生产模块有真实 CI 编译证据。** 本回执替代旧进度单中 Core 的 `in_progress` 状态，保留 VE 的已完成结果，不取消既有 P0 组件核验，不把局部成功外推为根或最终主定理完成。最终 `hLower`、`hUpper` 及其真实供应要求没有因此闭合。

本任务仅只读读取固定 Git 对象、保存的 JSON/日志及两次被拒绝的 GitHub GET；没有启动 Lean、没有重跑 CI、没有修改工作流/生产代码/主文档/ledger。仅创建本 `.md` 与同名 `.json` 两个回执文件。
