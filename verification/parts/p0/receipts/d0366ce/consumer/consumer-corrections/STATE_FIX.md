# 消费者状态顺序修复

本说明只涉及仓库外的 Part 0 证据消费者。集成源码固定为 `d0366ce64272e81faf6166a8a90050f56b328d38`，没有修改 Lean、工作流或任何 Part 分支。本次实际核心运行仍由 P0 root 独自监控；本修复未读取该运行的新元数据，未观察到一次实际失败。

## 原问题与封存

P2 静态审查指出，原程序在 `prepare()` 先要求 ZIP 和所有元数据文件存在；随后又在读取 artifact 项、digest 和 ZIP 之后才记录并处理已完成失败的 run / job / step。因此即使现有原始元数据已经明确显示失败，缺归档也可能使回执仅显示 `PENDING`，并漏掉 run / job 的已知失败结论。

修改前的脚本 SHA-256 为：

`85911b447a1a4b8c455f148725ae1b5a961daae771c5b484c9db5429a2a7067b`

原脚本、原 README、固定源码期望、准备检查、缺件检查、准备清单和原缺件输出目录均封存于 `before-known-failure-state-fix/`。其 `PRESERVED_MANIFEST.json` 给出原始字节摘要。原先的准备检查仍只适用于这个原脚本版本，没有被覆盖或改写成新版本检查。

## 修改的控制流

`prepare()` 现在只准备独立输出目录、记录现有输入及缺件，不因缺 ZIP 提前退出。程序随后依次读取可取得的原始 run / job / step 元数据，核对固定身份后立即保存原始字节和 `observed`；任何已完成但非成功的必需记录立即进入 `known_ci_failures`。缺 artifact 项、digest、ZIP 或其他材料发生在这些记录之后。

回执单独列出两类状态：

| 字段 | 表示的事实 |
|---|---|
| `ci_metadata_status` / `known_ci_failures` | 已取得并绑定身份的 CI 元数据结论 |
| `evidence_status` / `missing_inputs` / `pending_evidence_reasons` | 证据是否齐备，以及具体缺什么 |

已知 CI 失败同时缺件时，返回 `FAILED_CI_WITH_INCOMPLETE_EVIDENCE` / exit 1。元数据没有已知失败而证据不足时，仍返回 `PENDING` / exit 2。若归档已经取得并核对身份，程序先保留现有真实日志和诊断，再返回已知 CI 失败。身份冲突、JSON 解析等消费者错误仍与 CI 结论分开记录。

固定 Git tree 检查移到元数据接收之后、任何证明门消费之前。成功路径仍要求完整固定 Git 内容、成功 run / job、六个实际成功步骤、归档绑定、原始日志、类型与对象校验全部完成。没有降低成功门槛，也没有把元数据结论或消费者错误写入 Lean 首诊断文件。

## 局部核对

新脚本 SHA-256：

`925ebb6e12e1693635ca56dfbf58fc548e5ee350897079a95b0bf11b63b6ed63`

Python 语法检查通过。生产脚本中的 d0366ce、tree、实际 run `38289734671` 和 job `114946653833` 常数均未改变。

`check_known_failure_state.py` 只运行消费者层的负向控制流检查。隔离的内存实例使用负数 run / job ID、非 Git 的 fixture SHA、显式的 `SYNTHETIC_CONSUMER_CONTROL_FLOW_FIXTURE_NOT_ACTUAL_CI_EVIDENCE` 标记，并禁止全部 subprocess。生产脚本字节未改变；这些内容不是实际 GitHub 元数据。

| 消费者层用例 | 实际本地返回 | 保留的两类事实 |
|---|---|---|
| 完成失败元数据 + 缺 ZIP | exit 1 | 已知失败；缺实际 ZIP |
| 完成失败元数据 + 缺 artifact 项 | exit 1 | 已知失败；列表没有目标 artifact |
| 完成失败元数据 + 缺 digest | exit 1 | 已知失败；缺 GitHub digest |
| 只有失败 run，其余证据均缺 | exit 1 | run 失败；其余元数据及归档不足 |

四例共 48 项局部断言通过；全部保留原始失败 run 元数据，没有生成 1005 类型、已验台账、最终桥或任何 Lean 诊断。没有构造成功 CI artifact 或 PASS fixture。

另以新脚本实际运行一次“全部实际元数据及归档均未提供”的回归检查，真实返回 `PENDING` / exit 2，7 项局部断言通过，验证未知状态未被误改为 CI 失败。这个调用没有读取任何实际 run 结论。

记录位于 `known-failure-state-fix/`：

- `NEGATIVE_CONTROL_FLOW_CHECK.json`：四例 48 项，只属于消费者逻辑；
- `MISSING_INPUT_REGRESSION.json`：无实际元数据时仍为待接收；
- `SYNTAX_CHECK.json`：新脚本的 Python 语法检查；
- 各 fixture 的输入、原始本地 stdout 和消费者回执均留存，并标明不是实际 CI 证据。

已把固定新脚本摘要和变更范围直接交给 P2，要求只读静态复核新增控制流。P2 的复核另存，不覆盖原版审查。此说明不预填其结论。
