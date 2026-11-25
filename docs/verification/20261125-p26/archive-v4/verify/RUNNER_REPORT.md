# Archive v4 inputs：P1 strict runner 候选

## 状态

**仅生成与静态审查；没有执行本 runner、P1 命令、Lean、原件读取或依赖编译。** 原 34 个 Lean 候选源及 `SOURCE_MANIFEST.json` 已冻结，本目录不改这些源或其验收状态。

当前 driver：`run_archive_v4_inputs.py`，32,002 B，SHA256：

`c7d7a43bd0b4ebc52f6d884a4b83cc82de531157dffa435ee5234bfb15a02c75`

固定目标与项目源 catalog：`SOURCE_TARGETS.json`，168,092 B，SHA256：

`29819ebed6b1a1ef036fd49f86db4e546cca74d93a73aa30f69d858908131f43`

Root 已确认发布布局：33 个 input/Core/reader 源放在主仓 `ImbalancedChen/`，其中 SourceJson 原样只校验；原生产 Archive 保持 `f48ba6e…`。因此本 runner 的**全部项目源码都从同一 `--source-commit` 的普通 `module_path` 读取**。`docs/verification/20261125-p26/archive-v4/` 仅供应固定审查 manifests、输入元数据与 driver。Archive facade 候选留在 docs，不是本轮目标，也不在任一目标闭包。

## 沿用的验收框架

以主线 `run_higher_facade_retry1.py`（SHA `c7ffc22e…`）和 `run_higher_facade_and_gate.py`（SHA `1fc656ef…`）为基线。`need`、`sha`、`git`、`check_configs`、`binding` 和完整 `main` 函数字节保留；特别是原 source/runtime 配置选择、P1 project/repository 限制、lane-0 serializer、冻结 executed-driver、原 Git worktree 前后检查均未变。

原 Batch13 API 从固定 Git 对象加载并先核 SHA，不复制改写其实现：

- commit：`4cea0407c1258eaddd7d4952cffa4aea67310422`。
- path：`docs/p1/20261125/batch13-repairs/run_repairs.py`。
- SHA：`95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea`。
- helper/tooling commit：`220c14630ffd266f824bdbf0977147ecb740c0dd`；全部原 helper pins、runtime observation/review pins 保留。

`api.context`、`api.normal_one`、`api.normal_valid`、`api.audit`、`api.audit_valid` 原样使用。每次 worker 只有一次选定目标的 `normal_one` 和一次该目标的 `audit`；未增加 lake/Lean 直调、依赖 build、审计预算、截断例外或正常/内核验收绕过。原 API 仍要求日志实际 built modules 恰为所选一个目标、direct dependencies 用 `--no-build` 检查就绪，并在 normal/kernel/full-owned 阶段核验既有 runtime、source、objects、traces 和配置。

## 32 个目标与执行次序

目标恰为：PackedChars、CharInputBridge、SourceJsonCharInput、PackedLoader、26 个原件 data owner、PackedInputs、Core。**SourceJson 是原已存在的依赖，不是新的 normal 目标；原闭合 guard facade 也被排除。**

候选次序：

1. 四个 foundation owner。独立 helper 不人为依赖彼此；真实 import 依赖必须已经通过本 runner strict 回执。
2. `P2OriginalSaving19ArchiveGeometryData00`。
3. `P2OriginalSaving19ArchiveGeometryData12`。
4. `P2OriginalSaving19ArchiveMomentData12`。
5. 其余 geometry 01…11、moment 00…11。
6. PackedInputs，最后 ArchiveCore。

runner 保持参考实现的单 `--module` 入口，不偷偷展开为多 owner build。`SOURCE_TARGETS.json` 给出完整 `owners` 顺序与每个目标的 `required_accepted_owners`：geometry12 必须有 geometry00 的成功 strict 回执；moment12 必须有前两样本回执；其余 data 必须有三个样本回执；maps 必须已有其全部 28 个新 owner 依赖回执；Core 必须已有 31 个前置 owner 回执。

`require_accepted_owners` **只读取**这些既有回执，调用原 `normal_valid` / `audit_valid` 验证，不重新编译或重新执行审计。它要求同一个 source commit、同一 driver/tool/runtime/config、相同项目源/对象/trace context、同一 26 原件输入绑定，以及原 wrapper 的成功 RESULT 和 BEFORE/AFTER 文件。ready object、孤立 normal、局部 audit、旧 Core 的 224 exports 或不同依赖上下文均不作为新前置验收。

依赖不 ready 时原 API 会停止；不自动修复、构建或重跑已有供应商。部分 audit 保留并停止，仍由主线检查，runner 不删除或跳过失败证据。

## 源前像与修改范围

每次只安装当前 `--module`：

- Core 允许不存在、精确 v2 前像 `df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182` 或精确本轮目标。
- 其它 31 个目标只允许不存在或精确清单目标；不存在时按原 `write_frozen` 创建。
- 所有其它已有项目源码，必须与固定 catalog 中的目标 SHA/imports 一致；没有任意旧前像白名单。
- 生产 Archive 独立 snapshot，**只允许原 f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49**，且全过程不变。runner 不安装 facade 候选。

固定 catalog 包含 Core 的全部 250 个项目模块；其中 32 个目标和 **218 个只读既有项目源**。后者为 MomentFloorConsumer 与其依赖合计 217 个模块，加原 SourceJson。每次实际 context 仍按参考框架冻结选定目标的真实闭包；Core 阶段会涉及全部 218 个既有项目依赖。独立 data owner 阶段仅需 3 个项目模块与外部 Lean，无须重建 217 个 Consumer 闭包模块。

所有源来自显式、完整、以已审 P1 baseline 为祖先的 Git commit，并与固定 source catalog 逐字 SHA、bytes、原 helper import lexer 结果核对。文档 `review_input_pins` 也在执行时从同一 commit 读取并核验。

## 26 原件前后绑定

保留 v2 reader 诊断的原路径遍历，分别 13 geometry 与 13 moment。每次 run 在 lane worker 内保存：

- `LOADER_INPUTS_BEFORE.json`，在执行选定 normal 前；
- `LOADER_INPUTS_AFTER.json`，即使发生失败也尝试保存；
- 根 `BINDING.json` 绑定的完整 26 项原件元数据。

每项记录 family/cell、原 relative path、逻辑 absolute path、resolved path、原文件 bytes 和 SHA。使用原 `d.fingerprint` 的 byte 读取，不解码文本或规范化 CRLF。整个记录列表必须与主线原 `ORIGINAL_INPUT_SCALE.json` 已绑定的 26 项 metadata **完全一致**，也须与当前冻结 binding 一致。总原始字节数 80,189,086 仅是文件绑定元数据，不被冒用为 Unicode codepoint length 或 JSON/数值证明。

这些外部 IO 不是 Lake 的自动依赖，因此单独前后冻结。前置 data owner 的 strict 回执也必须携相同 26 项 BEFORE/AFTER 绑定。原件不可用、内容变化、重定向后的路径不符，都会停止；没有 `--skip-inputs` 或 hash-only 解析成功标志。

## 回执与验收界限

输出根独立为：

`/workspace/p1-complete-proof/20261125-p26-archive-v4-inputs-v1/<source-commit>/<module>/`

保留原 normal、audits、runs、source backups、冻结输入及 lane 回执结构。新增 `REUSED_PRECEDING_ACCEPTANCE.json` 只记录已读验证的前置 normal/full-owned 证据，不声称重编或重审。

单模块通过只能标记该 input/helper/Core owner 的实际 P1 strict context 验收。以下字段始终为否/空：`archive_complete`、`only_cell00_proved`、`proved_parse_cells`、`archive_shape_or_row_guards_proved`、`old_core_224_exports_credit_transferred`。没有运行原 closed parse/shape/numerical guards，输入表示通过不等于这些义务完成。

## 已做的静态检查与剩余风险

已完成 Python AST 解析与内存中的 `compile(..., 'exec')` 语法检查，**未执行该 code object**。提取已钉 SHA 的 Batch5 纯 `imports(data)` 函数，独立核对全部 250 份源的 imports 与 catalog 一致；未执行 helper globals/main、runner、shell/build 或 P1 API。34 份 Lean source 与 source manifest 的指纹保持原样。

剩余需要主线实际验证的事项：

- 新 loader / data owners / maps / Core 都尚未在 P1 strict 编译；本脚本静态正确不等于 P1 运行已过。
- 14,461,008-byte geometry12 与 3,451,302-byte moment12 的真实资源成本未知；保留现有 lane/runtime 预算，失败不会自动加预算重试。
- 所有前置 strict 回执被有意绑定到同一 source commit/driver/runtime。之后若修改这些 pin，本 runner 会停止旧上下文复用，需主线明确审查如何续接，不自动忽略差异。
- `--check` 沿参考 runner 只做源/runtime/input 只读 preflight，不代表 normal、kernel、owned 或全部前置回执已经通过。它也需要实际 26 原件与既有 P1 文件就位；本地没有完整原件时不能冒称 cloud-ready。
- 原 helper 处理 orphan ready objects、partial audits、源配置差异或依赖未 ready 的限制保持；这些真实状态应据失败证据处理，不能自行清理 trace 或挪用旧验收。

## 文件

- `run_archive_v4_inputs.py`：待主线评审/发布的 runner。
- `SOURCE_TARGETS.json`：32 目标、250 源 catalog、26 原件 pins、前像/次序/前置验收要求。
- `RUNNER_STATIC_AUDIT.json`：参考 source pins、逐字函数复用与静态检查。
- `IMPORT_LEXER_CHECK.json`、`reference_batch5_source.py`：固定原 import lexer 的静态一致性证据。
- `prepare_runner.py`：机械生成器，不运行 P1。
- `attempts/docs-source-origin-draft/`：Root 确认主仓发布布局前的未运行草稿；不应执行或误用其 pin。

执行示意仅供 Root 在发布后填入具体 commit；本轮未运行：

```bash
python3 -B docs/verification/20261125-p26/archive-v4/verify/run_archive_v4_inputs.py \
  --source-commit <完整40位已发布commit> \
  --module ImbalancedChen.P2OriginalSaving19PackedChars --check
```

主线复核后用同一入口的 `--run`，逐一按 `SOURCE_TARGETS.json` 次序运行指定 owner。没有整包“一次全编”入口。
