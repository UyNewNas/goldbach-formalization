# Partition 单 owner formal adapter（本地未绑定）

`run_partition.py` 只处理 `ImbalancedChen.P1SignedExitPartition`。当前 `INPUTS = None`；直接执行会在 Git、helper、文件安装或 Lean 操作之前报 `UNBOUND`。本目录没有真实成功 probe，也没有新的 formal acceptance。由 root 独立审查、补齐真实证据、绑定输入和发布后，再安排远端任务。

## 固定身份与源码边界

| 项目 | 原身份 / SHA256 |
|---|---|
| 原 Dictionary acceptance | `040d46058821746c69c5183b3f6c22792287c4ba` |
| 原 Variation acceptance | `f7e9219f4860a819758d52752c5a9309dd14a8c7` |
| 原 Dictionary 只读证据发布 | `3c9bc8fbb8dcd8adc9e4f69c53aab7f41b8d5508` |
| 原完整 Partition 源码，15982 B | `cb4d4bb096d7de762cb23925af58624736bcfd753251f348b352acc67bdd2ad9` |
| 已审 parser 修补基线，15972 B | `19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c` |
| 冻结 probe helper，19059 B | `e3b4522c78f92c59701f394310d21f28cbc5ebbbfacd8e0707cd67b48c8a01d3` |

唯一允许的原源码定义改动是把 `p1SignedExitStates` 中分成两行的 record literal 合并成一行；adapter 检查精确 old→parser-fixed 字节替换及上述两个 hash。随后以 parser-fixed 原文为基线，只允许原 11 个 theorem 的 proof body 变化。完整 `:= by` 前缀（包括三个 theorem 的 `let states := …` 语句）、四个定义、15 个声明的顺序/名称/kind/private 标志、imports、namespace 和所有原文中 proof 外内容按字节固定。递归 equation-style definition 完整保留，不按首次 `:=` 切割。

接口门禁只适用于这份已固定格式的源码；它不替代 Lean 编译、完整 owned/private/generated census 或 kernel audit。每个最终 candidate 仍需同字节的真实 no-output probe 和原 `g.run_owner` 验收。

## 已有依赖如何复用

冻结 helper 只读取原 Dictionary 正常接受回执、原 `CONTEXT_BEFORE` 和已发布 readonly 回执，逐字节核对原 SHA；不会再次运行 `run_dictionary.py --check` 的 D288 全量回放。引用的 Dictionary acceptance 身份始终是 `040d…`，不赋给新的发布 commit，也不把本次快照称为新的依赖验收。

Partition 直接 project import 为 `ImbalancedChen.FirstExitHistoricalLevels`。其实际传递闭包固定为 40 份已有源码；全部 840 个 artifact 槽位均与原 Dictionary 接受时的精确 pin 核对。新 formal spec 的图恰好是这 40 个依赖加 Partition 共 41 个模块。`g.run_owner` 只调用一次，唯一目标为 Partition。

对完整 D288 保留 289 份源码、6048 个依赖 artifact 槽位、Dictionary 自身所有 artifact、旧接受证据以及额外 sidecar 的前后 stat metadata 快照；它们不被重新编译。Variation 始终通过原 `f7e…` adapter 的 `v.check`、`v.accepted` 和 `v.fixed` 读取并保护。另固定 native `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise` 的源码、`.olean` 和 `.trace`，与真实 probe 的原输入一致。

formal 保护快照明确不包含 probe 的 `target_state`，因为唯一新 owner 的源码和产物会在本次正式操作中出现；其他 probe 保护项仍保留。宽范围 metadata 在本次操作前后必须相同。后续只读检查不因无关 owner 后来被合法验收而要求其历史 metadata 永久不变。

## 真实 probe 门禁与发布内容

成功 probe 必须同时具备内层 Lean exit 0、外层 serializer exit 0、`VALIDATION_LANE_FINISHED`、原 lane/runtime SHA、原 guard 参数、完整前后保护和 Git 状态不变。检查原始 command、driver、exact source 和日志 byte/hash；`--no-build env lean` 不得请求输出对象。成功 probe 不产生 formal credit。

首次真实失败必须原样保留：

| 字段 | 固定值 |
|---|---|
| job | `job_26dda8849e2f4038b3a5eb22f333d49b` |
| source | `cb4d4bb096d7de762cb23925af58624736bcfd753251f348b352acc67bdd2ad9` |
| result | `b87a76b34d3df676d1f65817582711ab83c5e3e6903bdd77abfb9c7d61f55554` |
| log | `f5faaf911b3ac6c4ab71bee14c836b9058a9e37096a66e527cf648f562f0acbd` |
| driver | `e3b4522c78f92c59701f394310d21f28cbc5ebbbfacd8e0707cd67b48c8a01d3` |

`INPUTS.failed_probes` 按时间先后列出所有真实失败，各结果的 `previous_failure` 必须准确引用前一轮；成功 probe 引用最后一轮失败。固定 probe 前缀内发现额外 attempt 或缺失/部分 attempt 时停止，保留现场。当前设计可读取完整的 Lean 失败且前后保护成功的 probe；preflight 或保存中断的 partial probe 需要单独检查，不会被归为普通失败并跳过。

发布目录固定为 `docs/p1/20261127/p15-signed-exit-partition/`，应包含：

- `run_partition.py`：绑定后精确 runner。
- `support/probe_inputs_v1.py`：本目录冻结 helper 的原字节。
- `original-source.lean`、`parser-fixed-baseline.lean`。
- `P1SignedExitPartition.lean`：最终真实成功 probe 对应的源码；仓库 canonical `ImbalancedChen/P1SignedExitPartition.lean` 同字节。
- `probe/`：成功 probe 的下列完整原始记录。
- `failed-v1/`、`failed-v2/` 等：每个真实失败各一份下列完整原始记录。

每份 probe 的原始记录集合如下，路径结构不可压平：

```text
PROBE_RESULT.json
P1SignedExitPartition.lean
probe_driver.py
probe-command.json
probe.log
serialized-probe-command.json
serialized-probe.log
LANE.json
PRESERVED_BEFORE.json
PRESERVED_AFTER.json
GIT_BEFORE.json
GIT_AFTER.json
ImbalancedChen.P1SignedExitPartition/direct-import-stock-readiness-command.json
ImbalancedChen.P1SignedExitPartition/direct-import-stock-readiness.log
```

每个文件必须与对应远端原始 attempt 同字节。原始绝对路径保留在回执中；发布副本不重新归属旧接受身份。示例 schema 仅表达字段，不含虚构验收值：

```python
INPUTS = {
    'source_sha256': '<actual successful source SHA256>',
    'source_bytes': 0,  # Replace with the actual positive count.
    'probe': {
        'job_id': '<actual job_…>',
        'directory': '<original absolute attempt-00000 path>',
        'source_sha256': '<actual successful source SHA256>',
        'source_bytes': 0,
        'result_bytes': 0,
        'result_sha256': '<original raw PROBE_RESULT SHA256>',
        'driver_sha256': '<original raw probe_driver SHA256>',
        'log_sha256': '<original raw probe.log SHA256>',
    },
    'failed_probes': [
        {
            # Same required fields as probe, plus this publication directory.
            'publication': 'failed-v1',
            # Populate all fields from the first original failure above.
        },
    ],
}
```

## 执行边界

审查、绑定、发布完成后由 root 使用新的完整 source commit：

```bash
python3 -B /absolute/path/run_partition.py --source-commit NEW_FULL_COMMIT --check
python3 -B /absolute/path/run_partition.py --source-commit NEW_FULL_COMMIT --run
python3 -B /absolute/path/run_partition.py --source-commit NEW_FULL_COMMIT --check
```

`--check` 只读：不安装、不执行 Lean、不运行 normal/kernel；只调用既有接受读取/校验 API、读取固定来源和输入 hash。尚未运行时返回 `FRESH`；完整正式成功后返回 `REVALIDATED`；部分/失败状态拒绝，原文件保留。`--run` 只允许全新 owner，先以原 `--no-build` 查询检查两项直接 import，再安装精确新源码，调用原 `g.run_owner`，然后用原 `g.existing_owner`、`g.require_completed_existing_owner` 和 `g.acceptance_binding` 验收。已存在 owner 或任何部分目标产物时不会重复执行。

正常构建、owned/private/generated 枚举、标准公理限制及 kernel 导出检查均由原冻结 AG validator 完成。本 adapter 不替换 validator，也不预先声称 owned 数目。新 acceptance 只属于本次新的 source commit；不会改变原 Dictionary/Variation 归属，也不会把 P1.5 标记为完成。

## 本地验证

```bash
python3 -B p15-next-medium-formal/test_partition_boundaries.py -v
```

测试只覆盖本次新增的源码保持、真实 probe 外层完成、旧 identity 和 readonly/partial-owner 边界，不运行 Lean 或旧验收测试集。实际测试输出、文件 hash 和无远端执行标志保存在 `LOCAL_VERIFICATION.json`。
