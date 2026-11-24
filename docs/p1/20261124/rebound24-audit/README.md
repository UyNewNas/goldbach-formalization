# audit24：实际云端来源重新绑定

本包准备完成，未执行云端审核。原 runner 逐字保留。计划仅包含 24 个待补审核目标和 477 个项目祖先源文件；90 个 Seed 模块全部列为已完成排除项。

## 必须遵守的执行方式

只运行 `--prepare-only`，然后在原 state1 serializer 内**显式运行 `--lane 1`**。不要省略 `--lane` 启动默认双 lane，也不要执行 lane0。lane0 为空且留给根另行运行 HigherMoments；这里的空 lane0 仅满足原 runner 的既有两 lane 计划结构。

建议将本包的 `AUDIT_PLAN.json` 与逐字未改的 `run_parallel_acceptance_multibatch.py` 安装到 `/workspace/p1-complete-proof/20261124-resume/audit24-rebound-inputs-v1/`。以下命令以该新输入目录为准，目录安装由根执行：

```bash
python3 /workspace/p1-complete-proof/20261124-resume/audit24-rebound-inputs-v1/run_parallel_acceptance_multibatch.py \
  --plan /workspace/p1-complete-proof/20261124-resume/audit24-rebound-inputs-v1/AUDIT_PLAN.json \
  --prepare-only
```

```bash
python3 /workspace/blue-build-tools/serialize_validation_lane.py \
  --state /workspace/blue-build-tools/runtime-evidence/state.json \
  --receipt /workspace/p1-complete-proof/20261124-resume/batch1-batch2-normal-supplement-acceptance-rebound24-v1/lane-1/VALIDATION_LANE.json \
  python3 /workspace/p1-complete-proof/20261124-resume/audit24-rebound-inputs-v1/run_parallel_acceptance_multibatch.py \
  --plan /workspace/p1-complete-proof/20261124-resume/batch1-batch2-normal-supplement-acceptance-rebound24-v1/AUDIT_PLAN.json \
  --receipt-root /workspace/p1-complete-proof/20261124-resume/batch1-batch2-normal-supplement-acceptance-rebound24-v1 \
  --lane 1
```

原失败收据目录保持原样；新目录为独立的 `.../batch1-batch2-normal-supplement-acceptance-rebound24-v1`。本计划与旧 Seed90 验收使用不同 plan SHA，Seed90 已完成收据仍绑定原计划及原未变 closure，不重跑、不重新计作新成果。

## 来源纠正

原计划把 Git 选源误当成整条祖先源码快照。本次实际云端列出 13 个差异：10 个 P2 既有基础修补，以及 3 个 P4B 已发布 proof-only postimage。根已在本地 canonical 采用实际云端原字节。本计划逐项将这 13 个期望 SHA 改为经来源审阅的实际 SHA；其余 464 项不变。477 项期望 SHA 已与本地 canonical 全量核对一致。

24 个目标本身的源码 SHA 全部不变，原 normal 的两个日志及其 SHA / 完整 Built 集合也保持不变。只影响其中两个目标的祖先绑定：`P2Winner9SelectedRowRealJacobian` 和 `P4BSmoothPrimeEulerFlowBudget`。13 个模块的 import 列表全保留，故所有目标的项目 closure 成员集保持原样。

计划不再声称拥有 normal 时刻的完整祖先源码快照。它明确绑定原 baseline、既有 donor blobs、当前 actual-blue SHA 清单；当前 `--no-build` 已由根真实运行通过，并会由原 runner 在 kernel/full-owned 前后再次强制运行。

`source_review_head` 为 null，表示根的本次 publication commit 由外置 `PUBLICATION_BINDING.json` 登记，不能把旧 baseline 冒充本次完整来源树。外置 binding 应记录本计划 SHA、13 源复用 manifest SHA、发布 commit 及实际云端 mismatch 清单 SHA；无需因此改动本计划字节。

## 保持的检查门槛

- 原 normal 日志 SHA 和完整 `✔⚠ℹ Built` 集合匹配。
- 当前 477 个项目依赖源码逐一匹配预期 SHA。
- 每个目标的源码和 `.olean`、`.ilean`、`.c`、`.setup.json`、`.trace` 六项快照。
- 原 state1 guard 下的 `lake --no-build build`，审核前后各一次。
- 每个目标按全名运行 `leanchecker --verbose`。
- 原 `PublicAudit.lean` SHA 固定，完整 environment-owned 库存与导出清单一致；包含 private/generated 声明、完整类型与传递公理；只允许三项标准公理。
- 全部快照、依赖源码、normal 证据和 plan SHA 在审核后再次不变。

上述检查实现未改动；本目录 runner 与已发布原 runner 字节完全相同。

## 13 源公开合同审阅

152 个原公开 theorem 名称全部保留；118 个原 def/abbrev/structure 命令保持；13 个 import 列表保持。143 个公开 theorem header 的 token 完全相同。其余 9 个是原已发布包明确记录的表达修正：

| 模块 | 原已发布表达修正 |
|---|---|
| `P2AffineSimplexMomentLaw` | 两个 Haar 类名显式限定为 `Measure.IsAddHaarMeasure` |
| `P2Winner9BarycentricMixedDegreeOne` | 四个 header 的 `9.factorial` 显式注明 Nat；其中 factorial-sum 另补齐原未配平括号 |
| `P2Winner9PhysicalAffineTransfer` | 三个 header 的 8/9 factorial 显式注明 Nat |

另外复用原已存在的一个 local Haar instance、一个 private floor helper，以及两条 `gapTotal` open 指令。它们都已在原 donor 字节中存在。本次没有新写证明或数值 checker。因部分旧表达原本未成功 elaboration，不能把这些 9 个 header 描述成“旧/新已验 Lean 类型逐字相同”；原已验 postimage 的类型完整列在 `PUBLIC_HEADER_EXPRESSION_REPAIRS.json`。

10 个 P2 模块精确对应 `8657cfffef159185f73c6a04ae4d31c846c0d0a9` 已发布包，旧证据为 normal、exact-module kernel、103 个公开 theorem 类型及传递公理审阅；该旧证据不是完整 environment-owned 审计。3 个 P4B 精确对应 `48db3d603d632bc60037e149a55717832e4c04be` 原 postimage；已重读旧 batch043/045 的实际 compile、kernel、axiom 日志，绑定全部源码与日志 SHA，并核对 24/40/23 个完整 serialized/environment-owned 库存。旧证据均不扩张为当前整个 P1 或完整 imported environment 的新验收。

13 源 manifest 与声明审阅位于 `../source-context-diagnosis/actual13/`；其中 `CANONICAL_REUSE_PLAN.json` 是最小逐字复制清单，`PUBLIC_HEADER_EXPRESSION_REPAIRS.json` 保存 9 个旧/现 header 和既有 Lean 签名，`P4B_HISTORICAL_RECEIPT_BINDINGS.json` 保存历史实体日志绑定。四个原 P1 出口 SHA 再次核对未变。

## 固定 SHA256

- 新 plan：`936c9dcefa8c1e94cf6d9c52858c812b5eabb70f6311f6bc9a6a872621b7be84`
- 原 runner：`e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1`
- 13 源逐字复用 manifest：`acd26f9a126424119ccd6cd8c90289c418eeae6f2b7ddbfcb63132c19b0903a7`
- 原 plan（保留）：`b0cc5077081c2048001cf48bdf5e792f81be377060bcebbbddb05fc7648e3934`

## 已确认的发布绑定

`PUBLICATION_BINDING.json` 已绑定根推送并 fetch 确认的 `a0ce69fcf65a1a55e4fe3d70a5196268beb8d860`，tree 为 `0cfdd3a84650bf7b45fdedad45ead2085b9bdf2b`。本地独立从该提交的 Git blobs 重新核对全部 477 个计划源码 SHA，一致；本次另外 3 个 Lean 源更新均在 audit24 closure 外。四个原始 P1 出口 SHA 也按该提交再次核对未变。原计划字节保持不动。
