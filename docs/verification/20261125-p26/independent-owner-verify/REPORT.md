# 五个独立新 owner 的 P1 strict 单目标包装

## 状态与交付

**source-only 候选。没有运行本 runner、P1、Lean、leanchecker 或任何依赖 build；没有修改主仓。** 已完成来源、实际旧回执、API 签名/实参、Python 语法与独立只读审查。当前文件可供 Root 纳入下一次已发布 source commit 后逐目标提交。

- `run_independent_owner.py`：35,076 B，SHA256
  `a2f9528662278b6aa994fb160013b5d0c2f5d762a455dec536afa90004b8443e`。
- `SOURCE_TARGETS.json`：118,482 B，SHA256
  `1366f95d28811c303f3a7d0f0079f1335752365251148cd041062a948a36746d`。

发布布局固定为 `docs/verification/20261125-p26/independent-owner-verify/`，包含 driver、SOURCE_TARGETS 和 `reviews/` 三份已固定 metadata。五个 Lean owner 及它们的依赖应放在同一新 commit 的普通 `ImbalancedChen/...lean` 路径。新 commit **不在脚本中伪造或提前硬编码**：`--source-commit` 必须是已存在、完整 40 位、以所审 P1 基准 `298670f…` 为祖先的 commit，且其中每个 source/import/bytes 必须与固定 catalog 相符。

## 五个目标及先后条件

| 目标（均为 ImbalancedChen namespace） | 项目闭包 | 新 owner 的 strict 前置条件 | 外部接受条件 |
|---|---:|---|---|
| `P2OriginalSaving19ArchiveSchema` | 2 | 无 | 原 SourceJson 必须现成 ready，禁止重建 |
| `P2OriginalSaving19PrefixInterface` | 2 | 无 | 原 HomogeneousRecurrence 必须现成 ready，禁止重建 |
| `P2OriginalSaving19PrefixMoments` | 3 | 同新 commit、同 driver 的 PrefixInterface full PASS | 无 |
| `P2OriginalSaving19PullingFiniteCodes` | 1 | 无 | 只使用现有外部 Lean/Mathlib objects |
| `P2OriginalSaving19HigherMomentsPrefix` | 228 | 同新 commit、同 driver 的 PrefixInterface、PrefixMoments full PASS | 实际 bd718 facade 回执及完整跨 commit 等价核验 |

五个目标的联合 source catalog 为 **231** 个项目模块，包含 5 个新 owner 和 226 个既有供应者。所有新目标只允许当前 source 不存在或已经是精确目标字节；没有任意前像、覆盖或依赖修复选项。

Archive、ArchiveCore、PackedInputs、PackedLoader、Original28918、OwnedSource 和实际 PullingReuse 都明确不在本 scope，也禁止出现在目标图中。此范围没有执行原件 loader，所以新包装不读取 26 原 JSON；旧 v4 输入包装的 26 原件 before/after 门禁原样保留，未被本包装替代。

Schema/PrefixInterface/PullingFiniteCodes 可独立运行；PrefixMoments 必须在 Interface 之后，HigherMomentsPrefix 必须在两个 prefix owner 和旧 facade 证据均满足之后。仅 ready object、局部 local pass 或孤立 normal receipt 都不能充当这些新 owner 的前置 strict 验收。

## 保留的原验收引擎

Batch13 API 完全沿用固定 Git 对象：

- commit `4cea0407c1258eaddd7d4952cffa4aea67310422`。
- `docs/p1/20261125/batch13-repairs/run_repairs.py`。
- SHA `95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea`。
- helper/tooling commit `220c14630ffd266f824bdbf0977147ecb740c0dd`；原 helper pins、runtime observation/review、lane-0 serializer 与 guards 全部保留。

driver 仍通过原 `context`、`normal_one`、`normal_valid`、`audit`、`audit_valid`。正常编译和执行审计各只有一处调用，输入集合仅所选 owner；没有新的 lake/Lean 直调、依赖 build、预算上调、抽样审计或 private/generated declaration 例外。原 API 仍核对实际 built modules 恰为当前 owner、依赖 `--no-build` ready、source/object/trace/config/runtime、独立 kernel 与全部 owned types/axioms。

相对已审 v4 wrapper，`need`、`sha`、`git`、`check_configs`、`source_origin`、`source_slot`、`binding` 和完整 `main` **逐字相同**。`check_installed` 与已过 facade retry1 wrapper 逐字相同。单目标安装沿既有实现，只将允许源变更的旧 Core 特例删除：全部目标都仅 absent/same bytes。

原 normal/audit 回执目录不变：

- `normal/<module>/NORMAL_PASS.json`。
- `audits/<key>/AUDIT_PLAN.json`。
- `audits/<key>/lane-0/VALIDATION_RESULTS.json`。

新独立输出根为：

`/workspace/p1-complete-proof/20261125-p26-independent-owners-v1/<source-commit>/<module>/`

`require_accepted_owners` 只读取同新 commit 的上述真实回执，并调用原验证函数。它不重新执行依赖 normal/kernel/audit。要求 prior wrapper 的成功 RESULT 与前后实际 context 一致；部分审计、不同 source/driver/manifest/runtime 或过期 objects 均停止。

## HigherMomentsPrefix 的安全跨 commit 接续

已从 Root 提取的真实 facade retry 证据固定以下原时点：

- 原 source commit：`bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3`。
- facade 源 SHA：`9b2253f2ae8174e6ab00fd60c276643823f947e75145ca23e00ec5ccd458524c`。
- 原 driver：`c7ffc22ec3f4cd453fd21a92814ead753cdb312c6a3bbedd814327e935ad607d`。
- 原 wrapper RESULT SHA：`ac489c0eb93da86ed757a572b8844d67ae38538809f2cd90b092702e8d969fd9`。
- 原 audit result：`audits/b4796410e4ca5f3aac15/lane-0/VALIDATION_RESULTS.json`，SHA
  `12fc809c4fafe7f6b0f991dff8926539665418144e6a5415f72b53db913b4145`。

manifest 固定原 BINDING、NORMAL_PASS、AUDIT_PLAN、VALIDATION_RESULTS、成功 RESULT 和两份 before/after context 共七个真实文件的 bytes/SHA。原云回执根保持：

`/workspace/p1-complete-proof/20261125-p26-higher-facade-retry1/bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3/ImbalancedChen.P2OriginalSaving19HigherMoments/`

`require_legacy_higher` 的顺序是：

1. 核对七个原回执的精确指纹，以及旧 commit 中 driver/manifest 的原 SHA。
2. 读取旧 BINDING 的 224 项真实 graph/source/origin，并逐项从 **bd718 原 Git 对象**核 source bytes/imports。
3. 对照新 commit 已固定的完整 consumer catalog。所有旧 224 项 source bytes、SHA、完整 imports 和项目 import graph 必须相同；差异列出并停止。
4. 用 **old_commit=bd718** 调用原 `context`、`normal_valid`、`audit_valid`。原 `normal_valid` 同时验证 facade 自身 source + 五个 outputs，context 另验证其全部依赖 objects/traces/runtime/config。旧 before/after context 也必须与当前实际状态相同。
5. 另外生成新 consumer commit 对同一 facade 闭包的 context，逐字段比较实际 source/object/import/config/runtime；只允许 `source_commit` 身份字段本身不同。

旧 normal/audit 验证调用从来不传新 commit；旧 receipt 不修改、不重发，也不记录成新 commit 的 facade PASS。输出保留 `legacy_source_commit`、`consumer_source_commit` 和两份 context，明确 `receipt_relabeled=false`、`recompiled=false`、`reaudited=false`。

这些原件 source/import 等价已在本地只读准备时对实际 Git 和真实 BINDING 核过。**当前 P1 objects/traces 的等价尚未在本地验证**；必须由 serialized worker 在云上运行时检查。前置旧回执不存在、源或对象变化、存在额外/partial audit、runtime 不符，都会在安装新 HigherMomentsPrefix 和执行 normal 之前停止。没有跳过该检查的参数。

## 前后冻结与结果含义

worker 保持 lane-0 验证与冻结 binding，在新目标之前检查全部前置接受证据，保存 `REUSED_PRECEDING_ACCEPTANCE_BEFORE.json` 与 `LEGACY_HIGHER_ACCEPTANCE_BEFORE.json`。随后只安装所选目标，保存实际依赖 context，调用原 normal 与完整 audit。

之后再核对 source/object/trace/config/runtime context，并重新只读验证前置与旧 facade 证据，保存对应 AFTER 文件且要求与 BEFORE 相同。任何阶段失败只产生 HELD_OR_FAILED，无法凭已产生的某一部分 audit 得到 wrapper PASS。

结果只认证所选 owner 的实际 P1 context。以下均保持否/空：Archive complete、parse cells、shape/row guards、原 pulling 三个数值 guards、actual row numeric/floor claim、旧 Core 224 exports 信用转移、旧 receipt relabeling。Schema 的生成/private 声明必须由新 Schema 自己的完整 owned 审计认证；已有旧 Core 声明不能迁移为它的 PASS。

## 旧 v4 输入链的安全继续方式

本 driver **不运行旧 v4 链**。原输入 owner 从尚未通过的目标继续，到 PackedInputs 为止，必须继续使用：

- source commit `07826355aedef5a01e76c36ad304bc6b115f3c2b`。
- 旧 driver SHA `c7d7a43bd0b4ebc52f6d884a4b83cc82de531157dffa435ee5234bfb15a02c75`。
- 旧 SOURCE_TARGETS SHA `29819ebed6b1a1ef036fd49f86db4e546cca74d93a73aa30f69d858908131f43`。
- 旧输出根和已接受回执，不更换 source_commit 标签，不重跑已过 owner。

**跳过旧 `ArchiveCore` 目标。** 新 Schema 可由本 driver 先验收；新的 schema-split Core 不在本 driver 的 owner 清单。

之后若要验收新 Core，必须另作明确的接续：对每个所用旧 input owner，以其真实 078 commit、旧 driver 和原回执重新只读调用原 normal_valid/audit_valid；同时逐项比较旧实际闭包与新 source commit 的 source/imports、当前 objects/traces/config/runtime，并保持全部 26 loader input bytes/path/SHA 的前后绑定。新 Schema 使用它自己的新 commit strict 回执。新 Core 则执行自己的 normal/kernel/full-owned。不能将旧 PackedInputs 回执改名为新 commit，更不能把旧 v2 Core 的 224 exports 当作新 Schema/Core 的接受证据。

该下一阶段的逻辑没有在本 wrapper 中留一个宽松开关或半实现入口；其 scope 明确停止于上述五个 owner。

## Root 发布后用法

将整个本候选目录保存到上述 docs 路径，并把五个目标及相同 catalog 源纳入同一个新 commit。`P26_NEXT_SOURCE_COMMIT` 应设为**已经发布的**实际完整 SHA。示例：

```bash
python3 -B docs/verification/20261125-p26/independent-owner-verify/run_independent_owner.py \
  --source-commit "$P26_NEXT_SOURCE_COMMIT" \
  --module ImbalancedChen.P2OriginalSaving19ArchiveSchema --run
```

其余目标每次更换一个 `--module`。`--check` 沿原 main 只做源/runtime preflight；不代表 normal/kernel/full-owned 或云端旧 facade object 等价已通过。命令本轮没有执行。

## 静态与独立复核

`build_driver.py` 只从已审 wrapper 提取保留函数、读取固定源/旧证据、生成本目录文件；未执行被生成的 driver code object。已完成 AST 和 `compile(..., 'exec')` 语法检查、所有 API 调用的参数数量/顺序核对、单一 normal/audit 调用位置检查、全部来源的原 import lexer 比较、224 项旧 Git/source/import 等价以及 forbidden dependency 检查。

`/root/p26_higher_moments_review` 独立只读核对了冻结 driver、实际 pinned API 和 donor 函数：确认 API context 只取被验 module 的闭包、normal_valid 覆盖 owner 自身五个 outputs、旧回执始终按旧 commit 验证、后置再验证保留、异常仅能 HELD。未运行 wrapper 或核验远端当前对象状态。

完整记录：`STATIC_AUDIT.json`、`API_COMPATIBILITY.json`、`INDEPENDENT_REVIEW.json`。本报告不声称新 owner P1 PASS。
