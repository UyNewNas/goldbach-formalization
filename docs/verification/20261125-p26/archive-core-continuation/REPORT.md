# 新 ArchiveCore / RowNumerics 严格单 owner 接续候选

## 范围与状态

本包提供 `run_archive_core_continuation.py`，只允许一次选择以下一个新 owner：

| 目标 | 固定源码 SHA-256 | 项目闭包 | 必须先验证的旧 owner 回执 | 原件读取 |
|---|---|---:|---|---|
| `ImbalancedChen.P2OriginalSaving19ArchiveCore` | `4f5fcde939aad232d55f846ba5b52ca44862085cdf3354a288d354b953138c03` | 251 | 全31个 v4 input owner，加真实 ArchiveSchema | 全26份，前后 path/bytes/SHA 完整相同 |
| `ImbalancedChen.P2OriginalSaving19RowNumerics` | `4be5f94041cc77997b8ad720966bc87938824493287480dd13d8abc7d95ef98e` | 6 | 同一真实 ArchiveSchema | 不读取 raw files |

两个目标的总 catalog 为252个项目模块。它们各自独立验收；RowNumerics 不要求先编 Core，Core 也不导入 RowNumerics。选一个 target 不会编另一个。

本轮只准备源码、读取固定 Git 对象和已下载的真实 first7 回执，执行 Python AST/语法及调用参数检查。**没有运行 driver、Lean、P1 或原件读取，也没有修改主仓。** 新目标的 source commit 由 Root 发布后的 `--source-commit` 指定，必须是实际存在的完整 SHA；没有预填尚未创建的 commit。

## 真实旧来源固定

### v4 input chain

- 实际 source commit：`07826355aedef5a01e76c36ad304bc6b115f3c2b`。
- 原 driver：`docs/verification/20261125-p26/archive-v4/verify/run_archive_v4_inputs.py`，SHA `c7d7a43bd0b4ebc52f6d884a4b83cc82de531157dffa435ee5234bfb15a02c75`。
- 原 manifest：同目录 `SOURCE_TARGETS.json`，SHA `29819ebed6b1a1ef036fd49f86db4e546cca74d93a73aa30f69d858908131f43`。
- 原 manifest 仍是32-owner版本；本接续严格排除其中旧 ArchiveCore，只要求前31个输入 owner，直到 PackedInputs。
- 原回执根：`/workspace/p1-complete-proof/20261125-p26-archive-v4-inputs-v1/<078完整SHA>/<module>/`。

准备时实际逐项读取078 Git 中这31个 owner 的完整32源闭包，验证 source bytes、SHA、完整 import 列表均与新 consumer catalog 一致。没有把 old Core 的旧定义或回执带进这个比较。

Root 已下载的 first7 完整证据来自 `/workspace/p26-v4-first7-evidence/archive-v4-first7/`。本 manifest 为每个已知 owner 额外固定九个真实文件：BINDING、NORMAL_PASS、AUDIT_PLAN、VALIDATION_RESULTS、成功 RESULT、两份 dependency context、两份 loader snapshot。没有改写其中的云端绝对路径，也没有用本地复制目录替换原 receipt_root。

其余24个 owner 的当前回执尚未在本包准备时确认。本包**没有为它们发明 hash 或填写 ready**：运行时须读取原078目录中真实回执，执行完整旧 API 验证，再把实际指纹和 context 写入本次 BEFORE/AFTER 证据。

### ArchiveSchema

- 实际 source commit：`77c23a2a530ce8d34ec79f88181817072024d4a9`，由共享 Git 对象实际解析并读取。
- 原 driver：`docs/verification/20261125-p26/independent-owner-verify/run_independent_owner.py`，SHA `a2f9528662278b6aa994fb160013b5d0c2f5d762a455dec536afa90004b8443e`。
- 原 manifest：同目录 `SOURCE_TARGETS.json`，SHA `1366f95d28811c303f3a7d0f0079f1335752365251148cd041062a948a36746d`，原5-owner scope 不改。
- 只要求其中 `ImbalancedChen.P2OriginalSaving19ArchiveSchema` 的实际完整 strict 回执，不把其他四个 owner 的进度当作它的证明，也不要求为本接续重跑它们。
- 原回执根：`/workspace/p1-complete-proof/20261125-p26-independent-owners-v1/<77完整SHA>/ImbalancedChen.P2OriginalSaving19ArchiveSchema/`。

Schema 的实际77 Git 两源闭包已与新 catalog 逐字及完整 imports 核对。其 P1 回执在准备时尚未确认，保持与 pending24 相同的运行时硬门；未设虚构 receipt pin。若最终 Schema 实际接受发生在另一 commit，当前包装会拒绝，必须据真实回执显式更新来源；不能仅因 source SHA 相同就改 label。

## 每个 legacy owner 如何验证

`legacy_inputs` 在 source preflight 中固定旧 driver / manifest 的 Git bytes，验证所需旧源来自其实际旧 commit，且旧闭包是所选新 consumer 闭包的子集。它仅验证来源，不宣称任何云端回执 ready。

serialized worker 的 `require_legacy_acceptance` 对每个所需旧 owner 执行：

1. 检查原目录、BINDING、旧 commit、旧 module、旧 driver/manifest SHA、原 scope、原 source origins、完整 source/import graph、目标 source SHA 与原前置 owner 清单。项目、runtime、source/runtime configuration、API 和 tooling 必须与本次冻结 context 相同。
2. first7 的九份已知回执额外匹配已取得的固定 bytes/SHA。其他 owner 从实际原目录读取并验证，不因 hash 尚未知而跳过检查。
3. 生成 `api.context(old_commit, ..., old_owner_closure, ...)`，使用 **old_commit** 调用原 `normal_valid`。这会验证原 normal 命令和日志、只构建原单一 target、owner 自身 source 与五个 outputs，以及全部依赖 context。
4. 使用 **old_commit** 调用原 `audit_valid`，核完整 owned/generated/private inventory、types/axioms、独立 kernel、normal reuse、命令/log、runtime 和 audit plan。缺失、partial、错误 scope 或 stale context 都会停止；不接受仅有 NORMAL_PASS。
5. 要求真实成功 wrapper RESULT 与 BEFORE/AFTER context 匹配当前实际旧闭包。v4 还要求原 BINDING、RESULT 及两份 loader snapshots 都与当前26份原件完整记录一致，并保持旧 production Archive f48 指纹。
6. 另外对同一旧 owner 生成新 consumer commit 下的 context。只排除 `source_commit` 身份字段，其他字段逐一全等：project sources、dependency `.olean` **与 `.trace`**、configuration、existing runtime。owner 自身的五个 outputs 已由旧 normal/audit 验证并另记入接续摘要。

旧 API 验证从不传入新 commit。旧回执不重写、不复制成新 PASS、不重新 normal 或 audit。结果同时保存 actual legacy commit 与新 consumer commit，以及两份完整 context。

先前 wrapper 的 RESULT 并没有 normal/audit 哈希快捷字段，本包装按实际目录读取 `normal/<module>/NORMAL_PASS.json` 和 `audits/<key>/lane-0/VALIDATION_RESULTS.json`；没有依赖不存在的字段。实际 dependency snapshot 是 `{provenance, context}`，比较的是其中完整 context。

## 新 target 的单独 normal / kernel / owned 审计

主执行与原 wrappers 一样使用 lane-0 serializer、runtime review 和 published Batch13 API：

- API commit `4cea0407c1258eaddd7d4952cffa4aea67310422`。
- `docs/p1/20261125/batch13-repairs/run_repairs.py` SHA `95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea`。
- 原 tooling commit `220c14630ffd266f824bdbf0977147ecb740c0dd` 与所有 helper pins 保持。
- 原 P1 configuration observation/review 仍从 `298670f119d24874b719facb3ef756f1e01223a1` 读取并验证。

driver 只有一个 `api.normal_one` 和一个实际 `api.audit` 调用位置，均只接收 CLI 选中的 module。所有 dependency 仅校验 readiness。原 `normal_one` 的 direct dependencies 检查仍是 `lake --no-build build ...`；不 ready 就停止，不能顺便重建。

完整原 `audit_valid` 不改：所有 environment-owned 声明必须完整登记，包括 generated/private；禁止新增 axiom、`sorryAx`、省略输出，axioms 仅原标准集合。新 Core 的 exports 由这次新 source/object 自己接受；旧 v2 Core 的224exports没有转移。

11个 donor 函数保持逐字：`need`、`sha`、`git`、`check_configs`、`source_origin`、`source_slot`、`production_archive_snapshot`、`loader_input_snapshot`、`binding`、`check_installed`、`main`。变化限于新目标/source catalog、严格 legacy 跨 commit 接续和本次 worker 的前后证据阶段。没有替换验收引擎或放宽 budgets。

## 安装边界与前后证据

Core 必须已存在，且实际 source hash 只能是旧 v2 `df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182` 或精确新 `4f5fcde9…`。未知源、symlink、缺失 Core 槽均停止。旧前像通过原安装 helper 备份后才允许更换；如果已经是精确新源则按原流程 no-op。旧 v4 Core `7e87…` 不是允许的替代前像。

RowNumerics 只允许空槽或目标 `4be5f940…` 相同字节，不允许其他前像。两个目标都不更改生产 Archive；该文件持续冻结为 `f48ba6e6…`。

worker 顺序为：

1. 核 lane 与冻结 BINDING；Core 读取并保存全部26份原件 BEFORE。
2. 验证所有所需 legacy owners，保存 `LEGACY_ACCEPTANCE_BEFORE.json`。
3. **只有前置验证成功后**，安装所选新 target；保存实际依赖 context BEFORE，调用原单目标 normal 与完整 audit。
4. 重查新 target 的 source/dependency objects/traces/config/runtime，要求 AFTER 与 BEFORE 相同。
5. Core 重读原26份输入；随后再次验证所有 legacy owners，保存 `LEGACY_ACCEPTANCE_AFTER.json` 并要求全摘要与 BEFORE 相同，包括实际回执指纹与旧 context。

任一步失败只能得到 HELD_OR_FAILED。前置 owner 尚在排队、没有真实 kernel/full-owned PASS、source/object/context 不等价，都会阻止新 target 的 normal。未知 pending hashes 的冻结是在真实验证后运行时完成，不能因为 placeholder metadata 或一个 JSON status 字段而通过。

新输出根：

`/workspace/p1-complete-proof/20261125-p26-core-continuation-v1/<new-source-commit>/<selected-module>/`

## 原26文件与 RowNumerics 的不同范围

Core 使用原 v4 的 `loader_input_snapshot` 函数和原 manifest 中的26条记录，保留 family、cell index、loader relative path、logical absolute path、resolved actual path、bytes、SHA。没有只比摘要而丢路径，也没有用 byte count 当作 codepoint count。该 snapshot 仅冻结文件输入，绝不是 parse/数学证明。

RowNumerics 路径不调用 loader snapshot、不读原件、不请求31输入 owner 回执。它只检查真实77 Schema 接受；其余三个既有 Q96 source/object suppliers 由原 context 与 `--no-build` readiness 检查冻结，不能自动构建或冒称新 owned 验收。当前 Schema/Q96 readiness 未在本地运行本 wrapper 验证。

所有结果始终保留 `archive_complete=false`、`only_cell00_proved=false`、空 `proved_parse_cells`，shape/row 数值与 floor claim 为 false。无论 Core definitions 是否通过，此 driver 不导入或证明完整 Archive guard facade、Original28918、OwnedSource、PullingReuse，也不包含新增 cell00 parse/typed/shape cohort。

## 发布与调用

将本目录纳入仓内 `docs/verification/20261125-p26/archive-core-continuation/`，并把精确新 Core、RowNumerics 及相同 catalog 的生产源纳入同一个实际新 commit。`P26_CONTINUATION_COMMIT` 应设置为已经发布、在 P1 Git 中可读的完整 SHA。例如：

```bash
python3 -B docs/verification/20261125-p26/archive-core-continuation/run_archive_core_continuation.py \
  --source-commit "$P26_CONTINUATION_COMMIT" \
  --module ImbalancedChen.P2OriginalSaving19ArchiveCore --run
```

RowNumerics 用同一 driver 单独更换 `--module`。`--check` 只做源/config/runtime preflight，不等于所有旧 strict receipts 已就绪；provenance 明确记录这点。实际 legacy validation 始终在受序列化保护的 worker 内前后执行。

本候选无需等待 pending25 的 hash 才能完成源码冻结，因为没有把它们设为已接受，也没有提供跳过门禁的参数；实际运行必须等待其真实回执验证成功。如果实际 old commit、旧 driver、原件路径或源闭包改变，当前包装会拒绝，届时需显式更新与再次审查，不允许偷偷沿用信用。

## 独立只读终审

`/root/p26_higher_moments_review` 对冻结 driver 与 manifest 做了独立只读终审，并实际核对 first7 的63个 receipt pins、旧两类 binding/result 格式、95caf API、跨 commit context 子闭包比较与11个逐字保留函数。未发现阻塞或过强格式门。该审查没有运行 driver、compiler 或云端 readiness；其余24个 input owner 与 Schema 的实际回执仍由运行时门验证。完整记录见 `INDEPENDENT_REVIEW.json` 与 `API_COMPATIBILITY.json`。
