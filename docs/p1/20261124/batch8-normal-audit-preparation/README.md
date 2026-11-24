# Batch8 normal：结果驱动补审核计划生成器

当前交付是本地准备脚本，不是已经冻结的审核计划。Batch8 的实际完整 normal 原日志尚未交给本目录，因此这里没有 `AUDIT_PLAN.json`，没有预测成功集合，也没有新增 kernel / full-owned 接受记录。

`prepare_batch8_normal_audit.py` 只读取原始导出、不可变 Git 对象并在新的独占输出目录写计划及证据包。它不调用 Lean、Lake、guard、serializer、审核 runner、cloud MCP，不 checkout / fetch / 改写任何源码。

## 固定复用接口

- Batch8 源提交：`15fbbdd842d11df0ca4db340cae2eddfa7ed39d7`。
- 审核仍用现有 `run_parallel_acceptance_multibatch.py`，SHA `e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1`；没有新 runner。
- 计划 schema 保持 `p1_completed_normal_multibatch_audit_plan_v1`。
- 两 lane 保持 `[empty lane0, selected modules in lane1]`。以后由根代理运行原 runner `--prepare-only`，然后在原 state1 serializer 内显式 `--lane 1`。不能用默认双 lane 启动；runner 自己提供 guard，无需再包外层 guard。
- 保留源码及五产物快照、完整项目源码 gate、no-build 前后就绪 gate、逐模块 named leanchecker、全 environment-owned 声明/类型/公理审核。normal 不重编。

## 目标选择

候选 universe 从本次已发布并在云端实际读取的 `EXECUTION_PLAN.json` 获取。只选择每组完整原日志中的 `✔`、`⚠` 或 `ℹ Built` 行；`Replayed` 行不算新的 Built。整组 exit 1 不会丢掉其中真实 Built 的模块，但以下情形拒绝冻结：

- 日志原字节 SHA / 长度与原 command 或原 archive index 不一致。
- 原 command 没有 finished 记录，或者其 Built / failed 集合与完整日志不同。
- 实际编译超出原 requested scope，或同一模块同时 Built / failed / 出现 leaf error。
- 实际 source install / Git show reads / run config / 全 project source context 与发布源不一致。
- 任一审核目标的项目祖先缺失，或其源字节在 proposed review commit 已改变。
- 下一轮将写入的模块出现在已选审核闭包内。

若 directdeps gate 失败而该组确实没启动 normal，记录为 `SKIPPED_DIRECT_DEPS_NOT_READY`，不计入审核名单。若全部没有新的 Built，退出 2 并仅生成选择/来源报告，不创建 `AUDIT_PLAN.json`。

## 输入

需要下载的完整原 Batch8 树包含：

- `BATCH8_RESULT.json`、`RUN_CONFIG.json`、`PROJECT_SOURCE_CONTEXT.json`、`SOURCE_INSTALL.json`、`GIT_SHOW_READS.json`。
- `executed-driver.py` 与 `inputs/` 下原 execution plan、prior audit plan、source update、helper、ops、e9 runner、17 修改源及 3 preserve 源。
- `execution/lane-1/LANE_RESULT.json`，每组 directdeps 和实际 normal 的完整 `.log`、`-command.json`，以及实际 normal 的 `-BUILD_SCOPE.json`。
- 原导出 `ARCHIVE_FILES.json`，其精确 SHA 由根代理从已经校验的导出记录提供；脚本不会自行把任意现存 index 的 hash 当作独立可信输入。

如本次 audit17 的完整 `VALIDATION_RESULTS.json` 在同一导出内，可通过 `--prior-audit-receipt` 指定。只有它确实 PASS 且精确绑定 prior plan / 全源码 context，才把这 17 个加入已有接受排除列表。如果没有该接受收据，仍排除它们与本次 normal 的重叠，但不会声称这 17 个已通过。

## 本地调用形式

填入实际路径与已经核验的完整 SHA 后，由根代理执行这个本地准备命令：

```sh
python3 /workspace/scratch/638a86a3af73/p1-pending-repairs/batch8-normal-audit/prepare_batch8_normal_audit.py \
  --repo /workspace/scratch/638a86a3af73/goldbach-p1 \
  --evidence-root '<下载后的 Batch8 root>' \
  --archive-root '<原 ARCHIVE_FILES 路径相对的本地 root>' \
  --archive-index '<原 ARCHIVE_FILES.json 绝对路径>' \
  --archive-index-sha256 '<已核验的 64 位 SHA>' \
  --review-commit '<准备执行下一轮时所绑定的完整 40 位源码提交>' \
  --out /workspace/scratch/638a86a3af73/p1-pending-repairs/batch8-normal-audit/frozen \
  --concurrent-module ImbalancedChen.P2OriginalSixthHigherMoments
```

将下一轮每个实际写入目标再各加一个 `--concurrent-module`；这一步不预测它们的 normal 结果，只检查与所选审核闭包的写冲突。`--check-only` 可以先验证全部输入并打印实际选择而不写任何文件。输出目录必须尚不存在，脚本不会覆盖上一版计划。

默认未来云端 receipt root 为 `/workspace/p1-complete-proof/20261124-resume/batch8-completed-normal-supplement-acceptance`，根代理可用 `--receipt-root` 指定新的独占目录。

## 生成产物

通过全部本地证据 gate 后生成：`SELECTION.json`、`AUDIT_PLAN.json`（实际 Built 非空时）、`PROVENANCE.json`、`SOURCE_GRAPH.json`、原字节 `NORMAL_EVIDENCE.tar.xz`、`MANIFEST.json`。原 normal 日志的云端绝对路径保持原值，e9 runner 会在那里再次核验原字节和完整 Built 集合。

生成计划不提供新的 proof acceptance。运行中的下一轮还必须由原 e9 runner 执行实际 readiness、named kernel 与 full-owned gate，收取其完整 `VALIDATION_RESULTS.json`。

## 已完成本地检查

`STATIC_VERIFICATION.json` 记录 Python AST 检查与 9 个证据选择检查。使用了已有 Batch7 first-five 完整原日志，验证 mixed exit 1 保留真实逐项 Built，并验证字节篡改、metadata-only Built、超出 scope、截断、unfinished、Built/failed 冲突和 Built 模块 leaf error 均被拒绝；`Replayed` 不增加 Built。

这些仅检查本地生成器的证据选择逻辑。完整 Batch8 `prepare` 尚未运行，当前没有基于尚未结束任务的通过预测。原 next17 finalizer 是固定一次性来源脚本，本生成器复用其 schema / gate 约束，未改动该脚本。

terminal 的已冻结普通池已证明 38 个候选写模块与整个 Batch8 17-normal 审核闭包 519 不相交；本生成器仍按最终实际 Built 子集重做精确冲突 gate，不把普通池的候选数当作当前通过数。池来源见 `terminal-reconcile/ordinary-frontier-after-batch8/NEXT_ORDINARY_POOL.json`，根代理已持有其原 SHA。
