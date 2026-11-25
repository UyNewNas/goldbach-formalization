# Archive v4 strict runner：独立只读审查

## 结论与时点

对冻结的 `run_archive_v4_inputs.py` 与 `SOURCE_TARGETS.json`，**本次静态审查未发现阻碍交给 Root 逐 owner 实测的问题**。新增来源绑定、26 原件快照与前置回执检查，仍通过固定 Batch13 的正常编译、独立内核及完整 owned declarations 验收接口执行；未见放宽原验收门槛或将旧 Core 的 224 个 exports 迁移为新版本信用。

本报告只记录源码、API 签名、调用实参、目录结构及证据边界审查。审查者没有执行 runner、Lean、leanchecker、Lake 或 P1 任务，没有重新读取 80 MB 原件，没有修改生产、候选 Lean 源或旧回执。这不是 P1 PASS、实际资源测量或整份 Archive 证明。

本目录原 `REPORT.md` / `REVIEW_MANIFEST.json` 保留此前 source-only 审查时点，不回写为此次 runner 审查或之后的编译结果。新报告和 `DRIVER_REVIEW_MANIFEST.json` 单独绑定 runner。

## 冻结输入

| 输入 | 字节数 | SHA256 |
|---|---:|---|
| runner | 32,002 | `c7d7a43bd0b4ebc52f6d884a4b83cc82de531157dffa435ee5234bfb15a02c75` |
| SOURCE_TARGETS | 168,092 | `29819ebed6b1a1ef036fd49f86db4e546cca74d93a73aa30f69d858908131f43` |
| RUNNER_REPORT | 9,671 | `39734b66bc14ca00c5b14c2a215cf94f83cdb81cbe4ac20fe19d33d6209c97fd` |
| 原 Batch13 API | 24,975 | `95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea` |

Batch13 来源为 commit `4cea0407c1258eaddd7d4952cffa4aea67310422` 下 `docs/p1/20261125/batch13-repairs/run_repairs.py`。已独立从共享 Git 对象读取并核 SHA。helper/tooling commit 仍为 `220c14630ffd266f824bdbf0977147ecb740c0dd`；runtime observation/review、lane-0 serializer 和 helper pins 未替换。

对参考 `run_higher_facade_retry1.py`（SHA `c7ffc22ec3f4cd453fd21a92814ead753cdb312c6a3bbedd814327e935ad607d`），`need`、`sha`、`git`、`check_configs`、`binding` 及完整 `main` 的 AST 一致。新增差异集中于源清单、原件绑定、单目标安装及前置接受回执检查。未增加直调编译、扩大预算、丢弃输出或缩减 owned 审计的替代引擎。

## API 与原回执目录兼容性

已逐项核对原 API 签名：

- `context(source_commit, project, m, graph, sources, h, d)`。
- `normal_valid(source_commit, project, m, receipt, binding, h, d)`。
- `normal_one(source_commit, project, root, m, graph, sources, h, ops, d)`。
- `audit_valid(source_commit, project, directory, plan, passed, graph, sources, h, d)`。
- `audit(source_commit, project, root, passed, graph, sources, h, ops, d, run, accepted)`。

新 runner 对上述函数的所有实参顺序、模块集合和 context 类型与原签名相符。特别是复用阶段给 `normal_valid` 的 binding 是当前实际 `api.context`，给 `audit_valid` 的 `passed` 是 `{module: normal}`，不是无关 owner 或旧 Core 的集合。

原 API 写出、runner 读取的目录一致：

| 证据 | 相对选定 owner 根目录的位置 |
|---|---|
| 正常编译回执 | `normal/<module>/NORMAL_PASS.json` |
| 审计计划 | `audits/<key>/AUDIT_PLAN.json` |
| lane 完整结果 | `audits/<key>/lane-0/VALIDATION_RESULTS.json` |
| 包装器运行上下文 | `runs/attempt-*/RESULT.json` 及同目录 BEFORE/AFTER 快照 |

新根目录独立为 `/workspace/p1-complete-proof/20261125-p26-archive-v4-inputs-v1/<source-commit>/<module>/`。`require_accepted_owners` 使用上述正常回执和 audit 目录，并要求找到完整成功的 wrapper 记录。它只调用原 `normal_valid` 与 `audit_valid`，不重编或重新执行已过 owner 审计。孤立 ready object、normal-only、partial audit、不同 source commit 或不同工具上下文不能满足该前置条件。

原 API 本身仍检查：真实完整依赖源码、对象和 trace context；正常编译日志实际 built modules 恰为 `[m]`；直接依赖 `--no-build` ready 检查；normal 源/产物/命令/日志；单模块 leanchecker；owned 全名、完整类型、全部 axioms 与原标准 axioms 限制。新 runner 未替换这些逻辑。

## 单目标与来源范围

32 个目标恰为三个 helper、共同 loader、26 个 data owner、PackedInputs 和新 Core。SourceJson 是既有依赖，闭合 guard facade 不在目标或任何选定闭包中。每次只对一个 `--module` 调用 normal/audit；前置清单不会展开为依赖 build。

250 项项目 catalog 包含 32 个目标与 218 个只读既有项目源；218 为 Consumer 与其依赖共 217 项，再加 SourceJson。所有项目源码从同一完整 `--source-commit` 的正常 module path 读取，核对 SHA、字节数和原 helper import lexer。此前 source-only 审查固定的 250 项 source/import 数据与新 catalog 一致。

每次 context 只冻结实际使用的闭包；小 data owner 不会被冒称检查了整个 Consumer 对象闭包。Core 阶段才涉及全部 218 个既有项目依赖。源 commit 需为所审 P1 基准后代，未知 source/import/前像立即停止。

只安装当前 owner：新 Core 仅允许空槽、精确旧前像 `df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182` 或精确目标；其余只允许空槽或精确目标。原生产 Archive 独立要求且前后冻结为 `f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49`，本 runner 不安装 facade。

## 前置信用与原件输入

geometry00、geometry12、moment12 的次序和其余 data 的三样本前置要求明确。maps 需要其全部 28 个新 owner 依赖接受记录，Core 需要之前 31 个 owner。所有前置记录必须属于同一个 source commit、driver、API、runtime/config，绑定当前实际源/对象/trace，以及相同 26 原件与生产 Archive。后来改变这些 pin 会停止旧回执复用；这是明确的连续性边界。

原 13 geometry + 13 moment 的 family、cell、relative path、logical absolute path、resolved path、bytes、SHA 都在源清单固定。worker 在 normal 之前与 finally 中分别保存原 `d.fingerprint` 得到的完整 26 项快照，严格比较历史期望与前后结果；原件不存在、内容或路径改变即失败。前置接受记录也须有同一原件 before/after。源码中没有 JSON/数值 host 检验、换行归一化或跳过原件的开关。80,189,086 是原始文件字节总数，不是 codepoint 长度或数学证明。

## 保留的义务与实际风险

wrapper PASS 只表示当前 input/helper/Core owner 在实际上下文中完成原严格验收。`archive_complete=false`、`only_cell00_proved=false`、`proved_parse_cells=[]`、`archive_shape_or_row_guards_proved=false`、`old_core_224_exports_credit_transferred=false` 均明确保留。新的输入表示验收不证明 13 个 parse success、shape、数值 guards、pulling、积分或终点。

新 helper/data/maps/Core 均需真实 P1 验收。尤其 geometry12 14,461,008 B 的资源表现仍未知，cell00 局部证据不能推及最大输入；runner 未自动扩大资源或重试。`--check` 只代表只读 preflight，不能替代 normal/kernel/full-owned。原工具对 orphan-ready、partial audit、未 ready 依赖或 runtime 差异的停止条件仍存在。

新 noncomputable getters 的标记可能需要向 Original28918 的 `rawVertex` abbreviation、OwnedSource 的 `originalPoint` / `vertexId` 传播；这些下游不在本轮目标，旧对象不获得新表示的信用。该风险已在 v4 源审查中记录，未由本轮编译复现。

## 本轮操作范围

仅读取冻结文件、固定 Git API blob、比较函数 AST/调用及清单，并写本目录两个新审查文件。没有执行被读取的 Python code object，没有运行生成器或验收器，没有原件扫描、编译、云操作、生产改动或远端提交。
