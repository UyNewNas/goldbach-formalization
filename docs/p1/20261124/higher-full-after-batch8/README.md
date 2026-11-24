# Higher 完整模块：Batch8 探针通过后的单目标 normal 包

**此包尚未运行。** 主任务已经报告新版 Low 和 Middle 均退出 0；本包不会据口头状态安装源码，仍须在主云读取、绑定并复核原始回执。它没有新增 Lean 证明，也没有新增数值检查器。

建议原样发布到 `docs/p1/20261124/higher-full-after-batch8/`。完整 Higher 候选已在提交 `15fbbdd842d11df0ca4db340cae2eddfa7ed39d7` 的 `batch8-repairs/higher-probes/` 目录发布，因此本包直接读取该已发布文件，不重复放入另一份候选。

## 固定输入

| 项目 | SHA-256 |
|---|---|
| 云端 Higher 源码 preimage | `3bc124a836f6637bdb8fd8448a3c76d1ed313756022329221ffa1268838b010d` |
| 完整候选 | `a9a4e532991af5ba3b397b7381fd4a1fdf3302ee25ef27a16ebba04e68a68334` |
| 新 Low 源码 | `50045703c1e682b25a2b85e49ed13d657461267d9d8a6343cdc85f7a97f98bd0` |
| Middle 源码 | `989ba9d558fb5675b457f87c7a127976763cca261a2ded17657cffe3e97c6c4c` |
| 新 Low 原始日志 | `5e10c9a52f8dd5729d250bcf120445a3f9ce365fdd4f83b95438daf20608b6d0` |
| Middle 原始日志 | `a7ebd39f29b098a75e09fb5d5ea1b06d5a339e666bfd9cc0e8edf0a6de527189` |
| Batch8 lane0 原始日志 | `cf40456f806538b0609ff54edb9a3a27b2179cd27bd099981fbd1f4734f6f297` |

计划还固定两个直接项目依赖、完整 8 项项目依赖源码、四个原 P1 出口、既有 helper 的精确 SHA，以及原验证通道路径。

## 外部双通道 coordinator 接口

```python
config = higher.prepare(package_commit, receipt_root)
```

`package_commit` 是发布本包的完整 Git SHA；外部 coordinator 应已从该提交提取驱动。`prepare` 从 Git 的固定发布路径读取计划，因此可将驱动提取到任意文件名。该函数返回可 JSON 序列化的配置，其中包括 `receipt_root`、`executed_driver`、`driver_sha256`、`plan_sha256`、`normal_target`、`worker_argv` 和 `expected_project_dependencies`。

`prepare` 只提取已发布输入、核对并保存现成探针证据，不安装项目源码、不执行 Lean。它要求 Batch8 的 `BATCH8_RESULT.json` 已形成，确认两通道自然结束以及来源检查完成；不要求无关的 lane1 普通目标全部成功。

如果外部 coordinator 的 lane0 worker **已经处于既有最外层 serializer 内**：

```python
exit_code = higher.lane0_worker(config)
```

也可在同一已锁定 worker 内执行 `config['worker_argv']`。两者都只调用原 guard，不再进入 serializer。若从尚未序列化的 coordinator 直接启动，则原样使用一次：

```python
ops.run(lane_directory, 'higher-worker',
        h.serialize(0, lane_receipt, config['worker_argv']), relay=True)
```

`worker_argv` 的精确形状为：

```text
python3 <executed-driver.py> --commit <package_commit> --receipt-root <receipt_root> --worker
```

不带 `--worker` 的 CLI 是单独运行入口，会自行增加一次最外层 serializer；不要把这个入口放到另一个 serializer 内。

**Higher 的云端安装由此 worker 独占。** 外部 coordinator 的 source-update/install 集合应排除 Higher；Git canonical 可按主任务计划发布。其他通道的修改目标及其依赖闭包与 Higher 的互斥，仍由外部 coordinator 最终冻结。当前默认回执根是：

```text
/workspace/p1-complete-proof/20261124-resume/higher-all-factored-full-normal-after-batch8
```

## 安装前的真实证据门

`prepare` 和 `lane0_worker` 各复核一次云端原始文件：

1. Batch8 的驱动、计划、两份探针源码、Git 提取记录及 8 项依赖来源全部匹配冻结 SHA。
2. 两份探针实际 `-command.json` 的命令、工作目录、退出码 0、时间顺序、完整日志长度和 SHA 均匹配；Low 完成后才开始 Middle。
3. `PROBE_RESULTS.json` 与三条实际命令记录逐项相同，包括原 no-build 依赖检查。
4. Batch8 lane0 外层 worker 和 serializer 的真实完成回执均为 0，state SHA 与当前环境一致；原 guard、serializer 和 state 的字节在本次执行前后保持一致。
5. 原四个出口保持固定 SHA，实际 Higher 仍是 `3bc124…`。若已经是候选或其他版本，停止并要求主任务复用、审查已有回执，不自动重编。

这些条件成立后，worker 仍先执行原 `lake --no-build build` 直接依赖检查。成功才调用现有 Batch5 的 `install_sources`，备份 preimage，并调用原 guard 执行唯一目标：

```text
lake build +ImbalancedChen.P2OriginalSixthHigherMoments:olean
```

预算、内存限制、guard 和 serializer 均不改动。Low、Middle、已过 degree6 探针、数值分页及其他 normal 目标不在该命令中。

## 记录与验收边界

完整探针原日志与回执保存在 `reused-batch8-evidence/`；本轮完整 normal 日志、命令退出码及时间保存在 `execution/lane-0/`。源码 preimage 保存在 `source-backups/`。

目标源码及 `.olean`、`.ilean`、`.c`、`.setup.json`、`.trace` 按原独立审核驱动的六路径布局保存执行前后哈希与字节数。已有依赖输出同样如实记录，缺失的附属输出标记为空，不为此补编已通过依赖。依赖可用性继续由原 no-build guard 判断。

`execution/lane-0/NORMAL_RESULT.json` 只有在退出 0、实际 Built 目标恰为 Higher 且六项记录完整时，才写 `PASS_NORMAL_ONLY_PENDING_KERNEL_AND_FULL_OWNED`。即便 normal 成功，独立内核与 full-owned 验收字段仍为 false，P1 完成字段也仍为 false。原 Git HEAD、脏工作区内容状态和四个出口保持不变。

## 手稿、公共合同与实际风险

静态核对以已发布提交的 `3bc124…` Git blob 为基线，不读取正在更新的本地 canonical 作为 preimage。全部 15 个公共定理的签名及证明体、10 个定义、全部声明名字和头部、导入均保持逐字节一致。变化仅为 0–5 阶 42 个私有叶子；6 阶原证明保留。

1106 pin `a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `num:simplex-moment` 给出一般单形矩公式。这里 canonical 是 `Fin 6 → ℝ` 的标准六维单形，有七个重心坐标。多乘一个重心坐标后，系数为 `k! (e_i+1)/(k+7)!`，因此公共积分出口分母为 `7! * choose(7+k,k)`。七个顶点值仍任意，范围仍是 `k ≤ 6`。形式化来源与完整公共接口清单见 `INTERFACE_AND_MANUSCRIPT.json`。

短探针通过尚不能排除整模块的累积 elaborator/interpreter 内存问题，也未覆盖全部 49 个私有叶子。若本轮仍失败，应依真实日志定位具体叶子或模块积累原因；本包不提高资源预算或预先拆分数学对象。完整 normal 也不会自动确认物理单形归属、作者数值归档或四个 P1 最终出口，这些仍由相应后续依赖及验收负责。
# Batch8 dependency context correction

The frozen plan now binds the actual cloud dependency bytes used by Batch8. Three earlier plan values came from older local canonical sources: `P2PositiveAffineSimplexLogJensen`, `P2DegreeSixLogGapSoundness`, and `P2OriginalLogMomentQ96Checker`. Their corrected values match the independently exported cloud files and existing public blobs at `a5a42f8f70418a7b2b8a378713911e829786ec8b`; no new proof or cloud source update is needed. See `DEPENDENCY_CONTEXT_CORRECTION.json` and the sibling `batch8-preserved-cloud-dependencies` package.

The gate now also verifies the complete Batch8 `PROJECT_SOURCE_CONTEXT.json` SHA256 `abb849aec311b84e039b6c3ecfdde710f72517f6ab41064420e96149432d2fa2` before inspecting its eight dependency entries. The existing live-project dependency check remains unchanged. `prepare()` and `lane0_worker()` have identical syntax trees and interfaces to the previous package; only `probe_gate()` gains the exact context-record binding. No probe or compilation has been executed for this package correction.

