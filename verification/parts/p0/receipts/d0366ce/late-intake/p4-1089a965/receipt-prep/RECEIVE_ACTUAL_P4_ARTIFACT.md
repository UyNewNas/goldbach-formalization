# P4 专项实际产物：离线逐门接收入口

## 当前状态与固定范围

本目录为收到真实 artifact 后准备接收方法，**不是成功回执**。目前没有将本入口用于新的实际 P4 artifact，没有运行 Lean、Lake、kernel replay、CI 或构造通过 fixture。

- 源提交：`1089a965e20664e63ffd51e0105c11befa406a1f`。
- 专项 run：`38288356713`，job：`114942066124`；只接收这个实际 run / job 的原件。
- 共同证明基线：`1a80c1bcce67886f699d097fc37fd245cd3620bf`。
- 按固定 `verification/verify_part4_upper.py`、`verification/Part4UpperAudit.lean` 和 `.github/workflows/part4-upper.yml` 的真实文件布局和门实施。
- 五模块公共源码定理数 53 只用于核对公开声明子集。**owned 声明总数、各模块数量、定理数量、公理列表、对象部分数量、运行时间及 ZIP 大小一律从真实产物读取。**
- 新 `.lean.txt` common-carrier 四候选在本运行之外；本运行不能验证它们，也不属于 d036 的集成核验。

已有 44 文件封存集及其 `INTAKE_MANIFEST.json` 保持不变。新增内容只位于这个 `receipt-prep/` 子目录。

## 1. 收到什么后执行

需要保存以下真实、只读输入：

| 输入 | 来源/用途 |
|---|---|
| 原始 artifact ZIP | GitHub 已完成的 `part4-upper-38288356713-<实际 attempt>` artifact；保留完整压缩文件，不只取几个日志 |
| `run.json` | 该实际 run 的原始 REST JSON；固定源 SHA、run ID、attempt、最终 status / conclusion |
| `jobs.json` | 该 run 的原始 jobs JSON；具体 job ID 和每个 required step 的实际结果 |
| `artifacts.json` | 该 run 的原始 artifacts JSON；artifact ID、name、所属 run/source、digest 和 ZIP 大小 |
| 本地项目 Git 对象库 | 已有共同 repo 中的固定 1089 对象即可；不切换 HEAD、不重新构建 |
| 必要时的依赖 Git 对象库 | 只读取固定 `lake-manifest.json` 指定 revision 的 Git 源对象。无需 `.olean`、Lean 可执行环境或缓存。不能假定旧会话目录仍存在 |

如果元数据仍显示 `in_progress`，不能写成功。若 artifact 暂未存在，不运行空输入检查来制造状态；继续保留当前候选状态即可。

## 2. 可直接执行的入口

脚本：`check_actual_p4_receipt.py`。

```bash
python /workspace/scratch/535d89efd063/p0-round4/late-intake/p4-1089a965/receipt-prep/check_actual_p4_receipt.py \
  --artifact-zip /真实接收路径/part4-upper.zip \
  --run-json /真实接收路径/run.json \
  --jobs-json /真实接收路径/jobs.json \
  --artifacts-json /真实接收路径/artifacts.json \
  --artifact-id 实际数字ID \
  --repo /workspace/scratch/535d89efd063/goldbach-formalization \
  --output-dir /workspace/scratch/535d89efd063/p0-round4/late-intake/p4-1089a965/receipt-prep/actual-run38288356713-review1
```

把上面四个输入路径和 artifact 数字 ID 替换为收到的真实值。输出目录必须尚不存在，且必须在本 `receipt-prep` 下；脚本不会覆盖旧回执、原始 ZIP、repo 或封存集。

如已正常取得依赖固定 Git 对象，可附加：

```text
--dependency-repo goldbach=/实际存在的goldbach依赖Git仓库
--dependency-repo batteries=/实际存在的batteries依赖Git仓库
```

按真实 import closure 的需要提供，不能为了示例另建或假装有这些路径。脚本使用 `git cat-file` / `git ls-tree` 读 pin revision，设置 `GIT_NO_LAZY_FETCH=1`，不拉取网络、不读工作树版本来代替固定 revision。对于未提供或缺失的固定源对象，输出 `unresolved_fixed_source_objects` 和 `unresolved_modules`，保留 `INCOMPLETE_EVIDENCE`。这属于源码身份核对尚缺证据，**不意味着需要重跑已成功的 Lean 构建**。

脚本直接读取 ZIP，不解压。它核对 ZIP digest、大小、成员唯一性和普通文件属性，然后为实际成员逐个计算 SHA-256。

### 退出码与产物

| 退出码 | 回执状态 | 含义 |
|---:|---|---|
| 0 | `READY_FOR_P0_COMPONENT_ACCEPTANCE_REVIEW` | 所有已实现离线门在真实输入上通过，交由 P0 进行组件范围与集成审查；不是 K/hUpper/最终主定理闭合 |
| 1 | `REJECTED_OR_FAILED_EVIDENCE` | 实际门失败、身份不一致、类型/公理/数据不一致或无法解析；保留第一实际诊断与原件定位 |
| 2 | `INCOMPLETE_EVIDENCE` | 原始输入或固定源对象不足、运行未完成等；不计为成功 |

输出主要文件为 `OFFLINE_RECEIPT.json`、`OFFLINE_RECEIPT.md` 和 `OUTPUT_MANIFEST.json`。遇到实际诊断时另保存：

- `FIRST_DIAGNOSTIC.json` / `.txt`：按真实运行阶段顺序发现的第一条错误/进程诊断，含 artifact member、SHA-256、原始行和行号。
- `first-diagnostic-original-stage.log`：该诊断所在的整份原始 stage log，逐字节复制。
- `FIRST_LOCATED_LEAN_DIAGNOSTIC.json`：第一条具有 `.lean:line:column` 位置的真实 Lean 诊断，避免通用 `error: build failed` 掩盖源码位置。
- `first-located-lean-diagnostic-original-stage.log`：该 Lean 诊断的整份原始日志。
- `first-failing-or-last-stage.log`：第一失败阶段或最后已到达阶段的原始日志。

若只有 timeout/kill、启动失败或缺失原件，无法得到 Lean 文件行号时，Lean 诊断保持 null。不得按证明修复猜测错误位置。

## 3. 真实 artifact 的预期布局

artifact upload 的根是 `.lake/part4-upper-verification/`。ZIP 可带外层目录前缀；脚本从唯一顶层 `report.json` 识别它，再以报告中的 `run_directory` 定位本次独立子目录。

```text
report.json
provenance.log
lockfiles.log
install.log
dependencies.log
cache-imports.log
cache.log
runner.log
outcome.log
run-<真实 time_ns>/report.json
run-<真实 time_ns>/<下表列出的实际 stage logs>
run-<真实 time_ns>/declarations.json
run-<真实 time_ns>/declarations.tsv
run-<真实 time_ns>/declaration-types.txt
run-<真实 time_ns>/theorem-types.txt
```

顶层与子目录报告应逐字节一致。缺少文件时不能从其他 run 或其他源码版本拼接一个“完整成功”目录。

## 4. 首先定位真实执行到了哪里

固定 runner 的完整成功路径有 19 个子进程 stage。这个数来自 runner 顺序；声明数量不由此推断。

| 次序 | 原始日志名 | 实际执行 |
|---:|---|---|
| 1–3 | `head-commit.log`、`working-tree.log`、`baseline-ancestor.log` | 固定 HEAD、工作树记录、共同基线 ancestry |
| 4–5 | `lean-version.log`、`lean-prefix.log` | 实际 Lean 版本、实际 sysroot |
| 6 | `dependencies-and-targets-build.log` | `lake build` 加全部五个目标；timeout 5,400 秒 |
| 7 | `ActualUpperPolicyDensity-strict-build.log` | 该模块强制严格源编译 |
| 8 | `UpperCoefficientPerturbation-strict-build.log` | 同上 |
| 9 | `ActualUpperDensityAssembly-strict-build.log` | 同上 |
| 10 | `RealPhysicalUpperWeightBridge-strict-build.log` | 同上 |
| 11 | `RealUpperCountingAssembly-strict-build.log` | 同上 |
| 12–16 | 五个对应的 `*-individual-replay.log` | 按相同模块顺序逐个 stock replay |
| 17 | `axioms-and-types.log` | 严格编译 Audit，并输出全部所属声明类型/公理 |
| 18 | `all-five-and-imports-fresh-replay.log` | 单次 aggregate stock `--fresh` Audit replay |
| 19 | `final-head-commit.log` | 末尾 HEAD 检查；此后仍须对象部分集合与二进制哈希重查 |

每个 stage log 第一行是 `command=<实际 JSON argv>`。它应与 `report.stages` 中相应条目的 command、顺序和 path 一致；结束状态应为 `PASSED`、整数 exit code 0。除第 6 项外，固定 runner 的子进程 timeout 是 1,800 秒。

### 最小且充分的失败区分

| 观察到的原始证据 | 可以确定的阶段 | 不能扩大成的结论 |
|---|---|---|
| 安装/cache 失败，runner report 不存在 | 尚未得到正式 runner 目标验证回执 | 不能说目标证明错误，也不能声称编译通过 |
| `dependencies-and-targets-build.log` 失败或仍运行，无 strict stage | 独立 strict 门尚未到达 | **不能仅据此说五 target 全部未尝试**；该 `lake build` 已命名全部五目标 |
| 第 6 项日志出现某目标的 `Built` / `Building` / `Replayed` 标记，或该模块源码位置诊断 | 至少该目标在依赖构建阶段出现实际尝试/结果证据 | `Building` 不是成功；普通 `Built` 也不是后续强制 strict / replay / Audit 全部完成 |
| 某 `*-strict-build.log` 的非零返回及实际 Lean 错误/严格 warning | 该模块 strict 失败 | 不把后续不存在的 replay/type 清单算为通过 |
| 某 `*-individual-replay.log` 非零 | stock replay 失败 | strict 成功不能覆盖此门 |
| replay exit 0，但 `report.error` 为 marker 或 object check 失败 | replay 后身份/marker 门失败 | 不能只看 exit 0 |
| `axioms-and-types.log` 非零 | Audit 编译/运行失败 | 不从部分已打印声明推断剩余声明安全 |
| Audit stage exit 0，随后 inventory parser 报错，fresh stage 未出现 | Audit inventory 或 post-Audit object gate 失败 | 53 源码头不能补 compiler-owned inventory |
| fresh stage 非零 | aggregate fresh 失败 | 五个单独 stock replay 不能替代全 import closure fresh 门 |
| fresh exit 0，最终报告仍失败或没有 final stage/重查标记 | fresh marker、对象、输出或 final binding 尚有失败/缺证 | fresh 命令成功不是最终封存成功 |
| report PASSED，但 CI required outcome/job/run 失败或未完成 | 整套 required outcome 尚未通过 | 不仅凭 runner 内一个 PASS 接收 |

对于“未到达”，脚本分别列出每模块的依赖构建实际标记、源码诊断、strict stage 是否已记录。缺少实际标记写成缺少证据，不把静默当作未尝试的证明。

成功依赖构建中的旧 warning 不应掩盖后面的首条实际错误。诊断提取优先错误，并支持 `error:`、`error(lean.synthInstanceFailed):`，以及 Lake 把 severity 放在源码位置前的形式。只有 strict 失败且没有错误形式诊断时，才保留该失败阶段的真实 warning 作为候选失败诊断。

## 5. 身份、源码与 import graph 门

首先将 actual run/job/artifact 全部绑定到源 1089，而不是当前分支名或 d036。至少核对：

1. 原始 `run.json` 的 head SHA、run ID、attempt 和最终 completed/success；`jobs.json` 的实际 job ID、run URL、head SHA，以及所有 required step 成功。
2. `artifacts.json` 的 artifact ID/name、所属 workflow_run、head SHA、ZIP digest 与实际 ZIP 大小。
3. `provenance.log` 的 head/expected/event SHA、run/attempt、固定 lean-action commit `f061402b660e0c34644504b324e830f2991d4865`、工具链 `leanprover/lean4:v4.33.0-rc1`。
4. 初始和末尾 HEAD log、root working tree 空记录、共同基线 ancestry stage。
5. 三个锁文件原字节 SHA-256 与共同基线一致；全部十一 dependency revisions 与固定 manifest 一致。
6. `source_sha256` 必须含五生产模块、Audit、runner、固定源码 lexer、owned workflow 和三个锁文件。对报告里的每个源文件，与其固定项目/依赖 Git blob 逐项比较。
7. 从同一固定源码重新遍历五目标 import graph，核对 source hash inventory 的精确文件集合；跟随项目和非 Mathlib 供应源，Mathlib/Lean/Std 等 leaf 按固定 runner 规则处理。

缺少某个依赖固定 Git 源对象时，脚本不从 cache 目录猜测，也不联网补齐；它列出明确 package、revision、path 和已记录 hash。优先复用已经存在且可读的固定对象补该身份核对，不重复 Lean 构建。

Mathlib 源码不是这个 runner 的逐文件 hash inventory；Mathlib pin/cache 和后续 stock `--fresh` 的 import replay 不能描述成“已对每个 Mathlib/imported object 逐一离线重新哈希”。

## 6. 编译对象与工具链二进制门

五个强制编译必须是源文件各自的：

```text
lake env lean -DwarningAsError=true -o <同一实际ROOT>/.lake/build/lib/lean/<MODULE>.olean <MODULE>.lean
```

Audit 也需自己严格编译并生成对象。脚本比较真实 argv，不接受仅有旧根 `lake build`、换模块名或省略 warning-as-error 的命令。

固定 runner 在各 strict 输出后立即保存该目标实际存在的 `.olean`、`.olean.server`、`.olean.private`；单模块 replay 前后和最后检查集合与哈希。主要对象必须存在，其余两部分按真实产物是否存在确定，不假定每个目标一定三部分。

需要的报告字段：

- `compiled_module_sha256`：五个生产目标的对象部分集合和哈希。
- `audit_module_sha256`：Audit 的对应集合和哈希。
- `output_part_sets_and_hashes_rechecked = true`。
- `toolchain_binaries`：实际 sysroot 下 `lean`、`lake`、`leanchecker` 三路径和 SHA-256。
- `toolchain_binary_hashes_rechecked = true`。

必须同时有固定 runner 的实际完整成功路径，不能只信两个布尔值。源文件、dependency HEAD/cleanliness、final HEAD、对象与工具链都在末尾重新检查。

**对象/二进制实体通常不在这个上传目录中。** 因而离线回执准确表达为“固定 runner 在真实 CI 中记录并前后重查的哈希证据”；不能假称离线重新读取、重放或重新 hash 了不存在于 archive 的对象。完整 stock fresh replay 的真实命令、出口和 marker 仍是必要门。

若在第五个 replay 完成前失败，runner 可能尚未把局部 Python 变量中的目标对象哈希写入 final report。保留已成功阶段事实，但不得凭这一点声称其对象/完整 axiom inventory 已封存，可暂留更细组件候选。

## 7. 完整类型、owned axioms 与 fresh 门

按 `axioms-and-types.log` 中的原始行解析：

```text
PART4_UPPER_AUDIT_DECL <JSON>
PART4_UPPER_AUDIT_MODULE <JSON>
PART4_UPPER_AUDIT_COUNT <实际整数>
```

Audit 的固定源码通过 defining-module metadata 收集五模块全部声明，包括 private、generated 和 structural；拒绝 own axiom 和 unsafe，使用官方 collector 收集每条 transitive axioms。每条只允许 `propext`、`Classical.choice`、`Quot.sound`。声明总数、五模块 count 与实际原始 records 必须一致，且声明名称不能重复。

每条记录应有完整 name/module/kind/universe_parameters/type/axioms；`pp.all=true` 与 privateNames 来自已绑定固定 Audit 源码。任何空类型、`⋯` 遗漏、未知所属模块、禁止公理或不一致总数均阻止接收。

`declarations.json` 必须与原始 Audit 记录一致；`declarations.tsv`、`declaration-types.txt`、`theorem-types.txt` 按固定 runner 的导出格式逐字节比较，不能把原始 53 个 source signatures 重命名成这份 elaborated inventory。53 个公开源码 theorem 应存在于真实完整清单中，但清单总数以真实 records 为准。

五个 individual replay 的实际 argv 使用 sysroot 下的 bundled `leanchecker --verbose MODULE`，各 log 精确 `replaying MODULE` 行恰一次。

aggregate 必须使用：

```text
lake env <实际sysroot>/bin/leanchecker --fresh --verbose verification.Part4UpperAudit
```

原始 log 中精确 `replaying verification.Part4UpperAudit with --fresh` 行恰一次，exit 0；Audit 固定 import 五个目标提供联合 import closure。不要额外假定每个 imported module 在 verbose 输出里的未核定行格式，不拿生成 marker 字符串替代原始文件。

## 8. 最终 outcome 与数学范围

完整成功还要求：

- `runner.log` 的 19 个 `START` 和 `PASS` 标记各与真实 stage 对应，末尾 actual declaration count 与原始 Audit 一致。
- `outcome.log` 实际为 `cache=success`、`verification=success`。
- report 为 PASSED、所有 stages PASSED、最终 count/module records/fresh module/两类重查标记完整。
- GitHub `Record and enforce the required outcome` 与 `Retain actual logs...` 等实际 required steps 成功，整个 job/run 最终 completed/success。

满足这些门最多支持五个固定条件式组件的接收。`hIntegral`、`hCertificate`、实际 compiled/raw error budget、同一 Q/rho 的 majorant/coprime/distribution，以及最终 hLower/hUpper 仍按完整类型保留。sharp K、c、完整 Chen mean、hLower、hUpper 没有因此获得实际解析供应者。P5 只等待 P4-A，不必等待 P4-B。

## 实现验证状态

只执行了 Python AST parse / compile-to-code-object 和 `--help`，实际结果保存在 `syntax-check.json` 与 `help.stdout.log` / `help.stderr.log`。未用伪造成功 archive 做 fixture，也未宣称此脚本已经通过一个尚未收到的实际 P4 artifact。收到实际固定产物后，首次运行结果、真实诊断及必要的离线接收脚本修正必须另留回执，不能回填为本准备阶段已通过。
