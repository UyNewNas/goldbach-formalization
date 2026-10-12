# 固定 d0366ce 核心归档消费者入口

此目录只准备离线证据接收程序。**当前没有提供本次核心归档，也没有生成通过回执或最终 1005 类型文件。** 程序不调用 Lean、Lake、Elan、内核检查器、网络或 Actions；唯一外部程序调用是只读 `git show` / `git rev-parse`，用于核对固定提交中的真实源码。

## 固定身份

| 项目 | 固定值 |
|---|---|
| 本批代码 SHA | `d0366ce64272e81faf6166a8a90050f56b328d38` |
| 本批代码 tree | `e2ab22b96f76c8969386296558c626c62a581700` |
| 继承的上一集成 SHA | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` |
| 实际核心 run | `38289734671` |
| 实际核心 job | `114946653833` |
| attempt | `1` |
| 归档名 | `lean-verification-38289734671-1` |
| 工具链 | `leanprover/lean4:v4.33.0-rc1` |
| Lean commit | `62eed1db4d67327ec8120be05f1a1b0847d74561` |

## 实际归档到齐后执行

由 P0 root 提供下载文件路径。下面的 `ROUND4_CORE_RAW` 是接收目录占位；替换成实际目录，三个 JSON 必须是实际 GitHub 元数据，不能使用仅有会话文字的归纳结果。

```bash
ROUND4_CORE_RAW=/absolute/path/to/actual/downloads
python3 /workspace/scratch/535d89efd063/p0-round4/final-receipt-prep/consume_core_artifact.py \
  --repo /workspace/scratch/535d89efd063/goldbach-formalization \
  --artifact-zip "$ROUND4_CORE_RAW/core-artifact.zip" \
  --run-json "$ROUND4_CORE_RAW/run.json" \
  --jobs-json "$ROUND4_CORE_RAW/jobs.json" \
  --artifacts-json "$ROUND4_CORE_RAW/artifacts.json" \
  --output /workspace/scratch/535d89efd063/p0-round4/final-receipt-prep/actual-d0366-consumed
```

`--output` 必须是新的或空的目录，且位于集成仓库之外。重试时使用另一个目录，保留第一份失败或待接收记录。消费者直接读取 ZIP，无需解压，也不会覆盖其他会话或仓库中的文件。

需要的原始文件：

| 输入 | 接受的格式 |
|---|---|
| `--artifact-zip` | 上表实际核心归档 ZIP；其整个文件 SHA-256 和字节数必须吻合 GitHub artifact 元数据 |
| `--run-json` | 原始 run 对象，带实际 `id`、`head_sha`、`run_attempt`、repository、workflow path、完成状态 |
| `--jobs-json` | 原始 `{"jobs": [...]}` 响应，或完整的目标 job 对象；包含实际 steps 和起止时间 |
| `--artifacts-json` | 原始 `{"artifacts": [...]}` 响应，或完整的目标 artifact 对象；带 `digest`、字节数和 `workflow_run` 绑定 |
| `--repo` | 能只读取得固定 d0366ce 和 28fd630 Git 对象的本地仓库；不要求当前 checkout 与 HEAD 指向这些提交 |

## 成功门槛

六门必须在实际 job steps、`outcomes.log`、逐门日志及 timing TSV 中共同显示已执行且成功：完整 build、四个显式新模块 target、根 bundled leanchecker、根 axiom-audit、Round3 types、Round4 types。构建可复用正常缓存；显式 target 检查不会被描述为强制重新编译。可选 Lake 缓存保存不替代上述任何门，也不会因步骤结论为 success 就宣称确实上传了缓存。

归档中的两个实际 receipt 必须共同绑定本批完整 SHA。消费者会检查：

- Round3 的 198 项和 Round4 的 414 项完整原始 `P0_ROUND*_DECL`，包括私有及自动生成声明；JSON、原始 stdout、模块 census、总数、唯一名称、完整类型与公理集合必须相符。
- 两个导出器各自的源码与生产对象 before/after 均一致；所有源码 SHA-256 与固定 d0366ce Git 内容一致；两个导出器的生产对象映射一致；被归档的 audit 对象字节吻合其 receipt。
- 根回放日志有全部 23 个已接收模块的真实 `replaying` 标记，以及根 `ImbalancedChen` 标记；记录真实根公理检查声明数及固定 `axiom-audit v0.1.2` commit。根计数取实际 footer，不预填预期值。
- 两个导出器打印的最终桥定理完整类型一致，且仍可见 `hLower` 与 `hUpper`。该单独定理不计入 1005 项声明清单。

消费者读取的源码期望、审计器配置与接口都来自发布的固定提交；没有运行仓库 Python 验证器。它只检查真实归档，不会把旧 28fd630 的通过状态转成新 SHA 的通过状态。

## 类型合并与格式范围

先从发布的 `INHERITED_TYPES_591.json` 去掉旧 Round3 的 198 条，保留老 393 条；再合并本次真实 Round3 的 198 条和 Round4 的 414 条，得到 1005 条。保留的老 393 条有 388 条实际 `pp.all`、5 条 Buchstab 完整默认 `Meta.ppExpr`。本次 612 条只有在真实编译输出与实际 `set_option pp.all true` 源码同时核对后，才获得 `PP_ALL_COMPLETE` 标记。

全部成功后的格式总数才是 **1000 条 `PP_ALL_COMPLETE` + 5 条 `DEFAULT_META_PPEXPR_COMPLETE`**。P1 旧生产者交接中的 permit14 默认格式将由本次真实 Round4 输出替换；不会仅凭预期将它们升级。P5 的上游 `S1LowerRosser` 8 条继续单列，不混入 23 模块或 1005 类型。

## 返回码及输出

| 返回码 | 状态 | 含义 |
|---|---|---|
| `0` | `PASS_ORIGINAL_EXACT_CORE_CI_EVIDENCE` | 实际六门与全部归档、源码、类型核对通过；消费者自身仍只是离线检查 |
| `2` | `PENDING` | 缺少实际归档/元数据/固定 Git 对象，或实际运行尚未完成，且已有绑定元数据没有已知失败；不会生成验证后的 1005 文件 |
| `1` | `FAILED_CI_WITH_INCOMPLETE_EVIDENCE` | 已有绑定 run / job / 必需 step 元数据明确非成功，同时还缺 ZIP、artifact 项、digest 或其他证据；两种状态同时保留 |
| `1` | `FAILED_CI_FROM_SUPPLIED_METADATA` | 已有绑定元数据明确非成功；可取得的归档身份与原始诊断先保留，不能升级为通过 |
| `1` | `FAILED_EVIDENCE_CONSUMPTION` | 身份或内容冲突、归档不完整、消费者检查错误等；若此前已知 CI 失败，其独立记录也继续保留 |

每次会生成 `CORE_RECEIPT.json`、`CHECKS.json`、`FIRST_REAL_LEAN_DIAGNOSTICS.json`、`RECEIPT.md` 和校验清单。只有真实全部成功后才生成：

- `COMPLETE_TYPES_1005.json` 和逐声明 `TYPE_FORMATS_1005.json`；
- `MODULE_LEDGER_VERIFIED.json`，明确 23 个已验组件、14 个仍待验组件；
- `ACTUAL_FINAL_BRIDGE.json`、`ACTUAL_FINAL_BRIDGE_TYPE.txt`；
- `SOURCE_OBJECT_BINDINGS.json`。

取得真实证据后也会保留原始 metadata、完整 ZIP 和已有原始日志；这些保留动作不以全部门成功为条件。两个实际类型导出目录通过消费检查后复制其原始 payload。

消费者自身的首条诊断属于证据消费层；CI 元数据中的非成功结论另列，两者都不能描述成生产 Lean 诊断。真实 Lean 首诊断按各原始流分别保留，不断言跨流的先后次序。

### CI 状态与证据完整性分别记录

程序先读取现有的原始 run / job / step 元数据；其固定 run、job、SHA 等身份核对成功后，立即保存 `observed` 和 `known_ci_failures`，再检查归档是否存在及其 digest。`prepare()` 记录缺件，不会在读取现有失败元数据之前因为缺 ZIP 提前退出。原始元数据字节也会在归档取得之前保留。

`ci_metadata_status` 与 `evidence_status` 是两个字段。例如，完成失败的 run 元数据加上缺 ZIP，应得到 `FAILED_CI_WITH_INCOMPLETE_EVIDENCE` / exit 1，同时留下该 run 的 `failure` 结论、缺件清单和 `pending_evidence_reasons`。它不能只被写成 CI 仍待定。没有实际 Lean 日志时，`FIRST_REAL_LEAN_DIAGNOSTICS.json` 中不会用元数据失败或消费者错误补出一条 Lean 诊断。

该修复保留全部成功门槛：只有真实归档、固定 Git 内容、实际六门、612 条本次类型与继承 393 条全部满足要求，才生成成功回执及 1005 文件。局部行为检查使用明确标记的消费者层失败元数据 fixture；它不代表真实 GitHub run，本次实际核心构建仍由 P0 root 独自监控。

## 仍需真实供应者与证据边界

此批组件接收不会闭合完整历史构造、全部数值证书、算术分布与误差、同一实际 rho 的 K 密度证明、完整 Chen 均值与 c，以及最终 `hLower` / `hUpper`。完整入口仍不能把这些输入改装成新结构或类型类来宣称闭合。Part 5 只需等待 Part 4-A 的实际 K 密度接口，不需等待 Part 4-B。

生产对象哈希来自后续 Round3/4 类型导出器的前后快照。bundled 根检查器本身打印模块重放标记，没有逐 marker 的对象摘要；消费者不会发明早先回放时刻的对象哈希，也不假定归档包括所有生产 `.olean`。这些是实际日志的范围说明。

继承记录中的历史相对路径保持固定 Git 提交下的原始作用域。依据 d0366ce 发布的 `verification/parts/p0/round4/ledger/REF_RESOLUTION.md` 映射到旧 28fd630 的 `verification/parts/p0/round3/ledger` 等路径，不宣称复制了所有历史 payload。

## 准备阶段状态

这里只执行本消费者的 Python 语法检查、固定源码期望提取，以及缺件返回 `PENDING` 的行为检查。没有制造成功归档 fixture，没有执行 Lean、内核重放或 CI。实际成功与格式升级须待 P0 root 提供本批真实归档后才能记录。
