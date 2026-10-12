# Core 消费者状态修复后的独立静态复核

## 结论

**原审查指出的“已有失败 metadata 加缺归档时仅显示 PENDING”问题已在新控制流中闭合；未发现本修复放宽任何成功接收门槛。** 六门、固定源码、完整 198＋414 类型、对象连续性与最终合并检查均保留。此结论只属于消费者代码审查，不能解释为实际核心 CI 通过。

| 对象 | SHA-256 |
| --- | --- |
| 修复后 `consume_core_artifact.py`，1079 行 | `925ebb6e12e1693635ca56dfbf58fc548e5ee350897079a95b0bf11b63b6ed63` |
| 封存的原消费者，957 行 | `85911b447a1a4b8c455f148725ae1b5a961daae771c5b484c9db5429a2a7067b` |
| 保持不变的 `CONSUMER_REVIEW.md` | `22ae4bb9237a0842105296568bfad29af854e02f894ec066ff514cc6a655e078` |

固定目标仍为集成提交 `d0366ce64272e81faf6166a8a90050f56b328d38`、树 `e2ab22b96f76c8969386296558c626c62a581700`、实际运行 `38289734671`、作业 `114946653833`、attempt 1。本复核没有查询该运行的新状态，没有取得或读取其实际核心归档。

本报告另存；原版独立审查与封存脚本均未覆盖。下述行号对应修复后脚本。

## 复核范围与方法

只读查看了新旧消费者、`consumer-corrections/STATE_FIX.md`、`CONSUMER_STATE_CHANGE.patch`、负向检查程序、已有原始负向 metadata 及结果记录。执行的是 Python AST 解析与新旧源码 AST 比较；未导入或执行消费者，未重跑 P1 的用例，未创建任何 fixture，未运行 Lean、CI 或网络访问，未改动脚本及仓库。

AST 比较确认全部顶层赋值不变，包括目标身份、工具链与依赖 pin、六阶段名称、模块集合及 198／414 声明计数。以下证明证据消费方法的 AST 与原版相同：

- `read_logs`
- `check_root_and_fixed_inputs`
- `expected_snapshot`
- `check_record`
- `read_export`

原有方法的变动仅在初始化、准备、metadata 接收、运行异常分类、报告文字与最终合并状态标记；`merge_and_write` 的差异是成功后增加 `evidence_status` 字段。另增的四个方法分别处理固定 Git 树、缺证据记录、metadata 原字节保存和已绑定 CI 状态观察。

## 原问题的闭合路径

### 1. 已知失败先于归档缺失保存

`prepare` 第 269–276 行只记录缺件，不因缺 ZIP 或本地 Git 对象提前退出。第 292–304 行在解析现有 metadata 时保存其原始字节、长度与散列。

run 的固定身份检查在第 327–334 行完成，随后第 335–339 行立即写入 `observed` 并观察 CI 结论；job 同理在第 358–366 行先绑定身份再记录状态。必需步骤从已绑定的 job 提取，第 379–385 行立即记录其结论与缺失时间信息。

第 306–320 行将已经完成且非成功的结论保存为 `known_ci_failures`。缺 artifact metadata、缺目标条目、缺 digest、缺 ZIP 的后续路径分别在第 399–424 行抛出 `EvidencePending`，不清除已经保存的失败记录。

第 971–980 行的异常分支明确区分：

| 已观察到的事实 | 消费者状态 | 退出码 |
| --- | --- | --- |
| 已知绑定 CI 失败，同时证据不完整 | `FAILED_CI_WITH_INCOMPLETE_EVIDENCE` | 1 |
| 没有已知 CI 失败，证据不足或状态未最终确定 | `PENDING` | 2 |

因此，失败加缺件不再被写成只有等待。JSON／身份／其他消费者错误仍通过第 981–984 行独立报告；此前保存的 `known_ci_failures` 不会被这一分支清除。

### 2. 没有 metadata 不会制造失败

所有实际 metadata 均缺失时，`read_supplied_metadata` 返回缺件状态；没有调用能够加入 CI 失败的有效记录。`read_metadata` 最终抛出 `EvidencePending`，第 978–980 行保持 `PENDING`／退出码 2。

缺某条 job 或必需 step 的查找从原来的立即失败改为先记录缺证据，但第 481–484 行阻止该状态进入证明接收。第 485–493 行还有最终硬检查，要求实际 run、job 和六个必需步骤完整存在、完成、成功，且每个步骤有起止时间。`len(matches) <= 1` 没有变成“缺项也可以成功”。

### 3. 仍先保存真实诊断再报告已知失败

归档存在且身份、散列、长度、成员路径和 CRC 核对通过后，第 441–477 行保存实际归档及可取得的原始阶段日志、类型 stdout／stderr 首处真实诊断。之后第 479–480 行才抛出 `KnownCIFailure`。

CI metadata 失败记录使用 `SUPPLIED_BOUND_CI_METADATA_NOT_A_LEAN_DIAGNOSTIC` 标签；它没有加入 `self.diagnostics`。最终真实 Lean 诊断文件仍只取自原始日志解析，消费者错误也不会被补写成 Lean 诊断。

## 成功门槛保持

第 959–966 行的完整成功路径为：准备输出 → metadata 与归档身份 → 固定 Git 树 → 六门原始日志 → 固定项目输入 → 198 条实际类型 → 414 条实际类型 → 对象／类型合并。

固定 Git 树检查只是从 metadata 前移动到其后，第 278–285 行仍要求精确树，且运行中位于任何证明门消费之前。第 485–493 行的成功 metadata 硬检查也位于这一流程之前。

**唯一写入总体 `self.report["status"]` 为 `PASS_ORIGINAL_EXACT_CORE_CI_EVIDENCE` 的位置是第 953 行。** 第 920 行对已接收模块台账的同名状态赋值位于同一个已完成全部校验的合并流程中，不能独立触发成功。新增的任何 `except` 分支都不产生成功状态。

原始六门、198＋414 完整记录、前后和跨导出对象映射、固定来源、393 条继承记录来源标签以及最终 1005 条唯一声明的核对方法保持原样。新增状态字段没有替代其中任何一项。条件式桥仍明确要求 `hLower`、`hUpper`，本修复没有宣称最终数学主定理闭合。

## P1 局部记录的证据身份

查阅的 `NEGATIVE_CONTROL_FLOW_CHECK.json` 明确标为：

```text
SYNTHETIC_CONSUMER_CONTROL_FLOW_FIXTURE_NOT_ACTUAL_CI_EVIDENCE
PASS_NEGATIVE_CONSUMER_CONTROL_FLOW_ONLY
```

其生产脚本散列与本次复核对象一致。测试程序只在隔离内存模块中换用 run `-382`、job `-114`、`CONSUMER_FIXTURE_NOT_A_GIT_SHA`，fixture 的 run／job 均为失败，六个步骤只有失败或跳过。生产文件和生产固定常数未改。所有 subprocess 在该局部程序中均被禁止。

已有记录显示四个负向用例、48 项断言通过：失败加缺 ZIP、失败加缺 artifact 条目、失败加缺 digest、只有失败 run 而其余证据缺失。各用例实际消费者状态都是 `FAILED_CI_WITH_INCOMPLETE_EVIDENCE`／退出码 1；记录明确不含成功证明载荷，也没有产生实际 Lean 诊断。

另查阅 `MISSING_INPUT_REGRESSION.json`：全部实际 metadata 及归档未提供，已有运行记录为 `PENDING`／退出码 2，7 项局部检查通过，`no_observed_actual_run=true`。这只是消费者缺输入回归，不是 GitHub 运行结论。

**本复核没有重跑这些用例。上述通过次数是已读取的 P1 局部记录，不是本审查重新执行的测试，更不是实际 CI 或 Lean 通过次数。** 未发现这些文件把负向消费者 fixture 冒充实际核心 CI 证据。

## 后续接收边界

该修复已满足本次针对状态顺序、已知失败保留和成功门槛的静态复核要求，可以用于随后接收真实齐全归档。实际核心构建、内核重放、公理检查及类型导出的最终结论，仍须由固定实际运行的原始证据决定；本报告不预填其状态。
