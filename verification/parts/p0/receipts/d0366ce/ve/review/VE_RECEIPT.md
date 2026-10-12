# VE 独立实际 CI 回执

## 接收结论

**通过原件接收审查**：对固定集成提交 `d0366ce64272e81faf6166a8a90050f56b328d38`，复用已真实执行成功的 [Variable envelope verification run 38289734726](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38289734726)，attempt 1；[实际 job 114946657574](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38289734726/job/114946657574) 的步骤均执行成功。独立读取核对 39 项，39 通过、0 失败。审查者只处理已保存原件与 Git 对象，没有启动 Lean、Lake、CI、网络轮询，没有修改仓库或原件。

实际 job 时间为 `2026-10-12T18:15:59Z` 至 `2026-10-12T18:18:44Z`。API 状态为 `completed / success`；`outcome.log` 原文为 `verification=success`。因此这是一份真实已执行 CI 的验证回执。

## 固定来源与 27 件原件

| 项目 | 固定值 |
|---|---|
| 集成源码 SHA | `d0366ce64272e81faf6166a8a90050f56b328d38` |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| CI artifact | `11765091242`，`variable-envelope-38289734726-1` |
| ZIP 字节数 | 43195 |
| ZIP SHA-256 | `70cb8852b79d8409d1982016ba60823982a30d7320c80195620ecf058f5d31a7` |
| ZIP 原件 | 27 件；与已有提取目录逐字节一致 |
| 工具链 | `leanprover/lean4:v4.33.0-rc1` |
| 实际 Lean commit | `62eed1db4d67327ec8120be05f1a1b0847d74561` |
| mathlib pin | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| goldbach pin | `09b97db5764ade1246bfb77206baa1b124760958` |

`VE_RECEIPT.json` 保存了 27 个 ZIP 成员的名称、大小、SHA-256，三份 API 元数据的 SHA-256，以及 report 中 20 项源码逐一对应的固定 Git blob、SHA-256 与匹配结果。20 项全部与集成 SHA 的 Git 对象相符。工具链文件、依赖 manifest、lakefile 与共同证明基线逐字节相同。

`report.json` 中的 `base_commit=7ba701070c5481acf9de1adb4489fd8016e08089` 是既有 VE 检查器的历史标签；本次已执行源码身份由真实 API、`provenance.log`、`head-commit.log` 和 `report.head_commit` 一致绑定为 `d0366ce64272e81faf6166a8a90050f56b328d38`。这两个字段不能互换。

## 显式目标与声明计数

| 模块 | 范围 | 声明数 |
|---|---|---:|
| `ImbalancedChen.VariableEnvelope` | 生产 | 42 |
| `ImbalancedChen.VariableEnvelopeConsequences` | 生产 | 30 |
| `ImbalancedChen.VariableEnvelopeRegularity` | 生产 | 31 |
| `ImbalancedChen.VariableEnvelopeScaled` | 生产 | 31 |
| `ImbalancedChen.VariableEnvelopeBoxes` | 生产 | 76 |
| `ImbalancedChen.VariableEnvelopeCertificates` | 生产 | 74 |
| `verification.VariableEnvelopeBoundary` | 边界 | 0 |
| `verification.VariableEnvelopeBoxesBoundary` | 边界 | 74 |

共 **358 条声明 = 284 条生产声明 + 74 条边界声明**。`verification.VariableEnvelopeBoundary` 使用匿名 `example`，定义模块清单为 0；它仍然完成了单独的严格编译和 stock kernel replay，不能因为清单为 0 删除其执行证据。

全部声明种类是 theorem 257、definition 95、inductive 2、constructor 2、recursor 2。其中生产 theorem 191、边界 theorem 66。`theorem-types.txt` 对应 257 个 theorem；`declarations.json` 对应全部 358 条声明及其类型。接收时重新解析 `axioms.log` 的 358 条原始 JSON 记录，与该 JSON 文件完全相同，并逐字节重建核对了 TSV 与 theorem-types 文件。

## 实际编译、内核重放和公理检查

六个生产模块由原始 `lake build` 命令全部显式列出；`build.log` 各有实际 `Built` 行，并以 `Build completed successfully (1396 jobs).` 结束。该命令是项目的 Lake 构建；本回执不额外声称六个目标都带有命令行 `-DwarningAsError=true`。

两个边界模块各执行 `lake env lean -DwarningAsError=true -o ….olean ….lean`。八个模块分别执行 `lake env leanchecker --verbose MODULE`，每件 replay 原件都有准确的 `replaying MODULE` 行且 exit 0。checker 来源是 Elan 锁定工具链中的 bundled `leanchecker`。这些命令没有使用 `--fresh`；本回执不将它们扩大为所有导入依赖的递归 fresh replay。

公理审计实际执行 `lake env lean -DwarningAsError=true verification/VariableEnvelopeBoxesAudit.lean`。固定源码按 Lean 环境的 defining-module metadata 遍历常量，包含 private 与自动生成声明；遇到 `info.isUnsafe`、自定义 axiom 或不允许的传递公理即抛错。本次整个循环成功。358 条声明的实际传递公理并集为 `Classical.choice`、`Quot.sound`、`propext`，无其他公理。原始记录不含独立的 `isUnsafe` 布尔字段；这里依据实际审计源码及完整成功的循环，不伪造逐条字段。

| 原始阶段日志 | 秒 | 退出码 |
|---|---:|---:|
| `head-commit.log` | 0.002 | 0 |
| `working-tree.log` | 0.275 | 0 |
| `python-reference.log` | 0.040 | 0 |
| `lean-version.log` | 0.655 | 0 |
| `build.log` | 14.466 | 0 |
| `VariableEnvelopeBoundary-build.log` | 2.431 | 0 |
| `VariableEnvelopeBoxesBoundary-build.log` | 5.148 | 0 |
| `VariableEnvelope-replay.log` | 4.059 | 0 |
| `VariableEnvelopeConsequences-replay.log` | 4.013 | 0 |
| `VariableEnvelopeRegularity-replay.log` | 4.083 | 0 |
| `VariableEnvelopeScaled-replay.log` | 4.092 | 0 |
| `VariableEnvelopeBoxes-replay.log` | 4.045 | 0 |
| `VariableEnvelopeCertificates-replay.log` | 4.038 | 0 |
| `VariableEnvelopeBoundary-replay.log` | 3.925 | 0 |
| `VariableEnvelopeBoxesBoundary-replay.log` | 4.449 | 0 |
| `axioms.log` | 8.584 | 0 |

本次 VE 记录中没有 Lean 失败诊断；这里的“无诊断”只描述这次成功运行，不覆盖其他 Part 的历史失败记录。

## 类型输出和绑定的准确口径

358 条类型来自锁定 Lean 的 `Meta.ppExpr info.type` **默认打印器**，属于编译器确认类型。接收时未发现 `⋯`、`…`、`...` 省略标记。但本模块审计没有开启 `pp.all`、显式参数模式或输出原始 `Expr`；因此这份回执不能冒充完整展开的 `pp.all / raw Expr` 类型导出。全部 257 个 theorem 的实际文本已经在原始 `theorem-types.txt` 保留。

固定检查器在执行前记录 20 项源码 hash，并在所有阶段完成后、写入 `PASSED` 前重新比较同一列表。独立复核也把这些 hash 对齐固定 Git SHA。该 VE artifact **没有保存生产 `.olean` 的前后 digest 清单**；不能将它描述为 Round 3/4 的那类源码与对象双快照绑定。八件实际 stock replay 的证据另有原始日志保留。

Python 参考检查为 `PASS`，有 10 个 interval cases 和 15 个 phi-range cases；原始报告明确 `original_sources_checked=false`。本次使用仓库内固定参考提取物与 fixtures，没有再次读取并 rehash 手稿的完整原始 Python 文件。参考 Python 中涉及扩展表达式的 fixtures，不改变 Lean 证明的正式范围。

## 范围与仍未闭合输入

本次 Lean 的可接收范围是三变量 VE 在 **`0 ≤ z ≤ y ≤ x ≤ 25/128`** 上的结果，以及上表列出的后果、正则性、缩放、盒与 VE 证书模块和边界回归。检查器的原始 scope 也明确排除了扩展的 `x ≥ μ` 表达式与完整数值证书。

**本回执不覆盖**新增 P1 `StoredHistoricalBoxPermit`、P2 `PairedV2Batch4To64Data` / `PairedV2Batch4To64` / `PairedV2Prefix64` 的本批根验证，也不覆盖 `MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser` 的八条声明依赖接收。前者必须使用本批主工作流与 Round 4 审计原件；后者仍使用其独立历史 strict compile / stock replay / 全声明公理与绑定证据。它们都不能从这八个 VE 模块的成功推导。

本次 VE 成功不提供真实解析 `K`、`c`、`hLower`、`hUpper`，不能消去现有最终条件式桥定理的分析假设，也不构成无条件最终定理的完成记录。接收 Part 为 P0 的限定范围回归证据；各 Part 的实际构造、上下界和分布供应仍须按各自固定版本台账核验。

## 原件位置与复核入口

原始 API 与 ZIP 目录：`/workspace/scratch/535d89efd063/p0-round4/d0366ce-ci/ve`。原件目录：`/workspace/scratch/535d89efd063/p0-round4/d0366ce-ci/ve/artifact`。独立审查全部内容见同目录 `VE_RECEIPT.json`。仅重做原件一致性核对可执行：

```sh
python /workspace/scratch/535d89efd063/p0-round4/final-receipt-prep/ve-review/verify_ve_receipt.py
```

该入口只读取 Git 对象和已有本地文件，输出本审查目录中的 JSON/Markdown；不会启动证明、CI、网络、修改 Git 或提取覆盖原件。
