# Cell05 全 56 行十项几何算术执行器

本目录是一个待绑定的单 owner 执行器。新模块 `ImbalancedChen.P2OriginalSaving19Cell05AllRowArithmetic` 需要 130 个旧项目供应者和三个新检查。供应者包括 Gaps 所继承的 128 个模块、已实证的 Gaps 对象及 canonical FastDetPure 对象。目标在内为 131 个不同项目模块。目标作用域为原解码的 Cell05 几何数据的 56 个有限十项行，全局 original Archive、moment 新 floor、所有权和积分仍开放。新执行结果始终标记 `P2_6_complete=false`。

## 真实 Gaps 结果绑定

root 完成 Gaps 的三项检查、全量证据归档和独立回读后，保留只读 `verify` 的单一 JSON 输出及它所指的精确 `gaps-evidence.tar.xz`。从实际只读任务取得报告 SHA，从此前独立审查取得 Gaps 工作流 manifest SHA。候选阶段没有 `CONFIG.json`、`WORKFLOW_MANIFEST.json` 或 Gaps 成功/对象占位值。

准备一个空的本地发行工具目录；保留以下文件的原有相对位置：`run_arithmetic.py`、`bind_config.py`、`test_run_arithmetic.py`、`DEPLOYMENT.md`、`owned-audits/P2OriginalSaving19Cell05AllRowArithmetic.lean`。用实际文件路径和两个已知摘要设置下列环境变量。绑定脚本离线读取真实报告和归档，输出新 CONFIG 与由各发行文件实际字节生成的 manifest。已有文件内容不同时停止。

```sh
python3 -I -S -B "$ARITHMETIC_TOOLS/bind_config.py" \
  --gaps-archive "$GAPS_ARCHIVE" --retained-report "$GAPS_RETAINED_REPORT" \
  --retained-sha256 "$GAPS_RETAINED_SHA" --gaps-workflow-sha256 "$GAPS_WORKFLOW_SHA" \
  --package-dir "$ARITHMETIC_TOOLS"
```

绑定脚本从归档中读取 Gaps driver、配置、workflow、RUN、SUCCESS、reuse index 和对象。原 retained summary 的 success/index/archive pins 必须分别匹配；SUCCESS 的 RUN/object 必须等于归档的实际字节，旧 Gaps 数量必须等于 128/129 和 1/3。核对 `run_arithmetic.py` 及其发行件的独立审查 SHA，记录脚本输出的 `workflow_manifest.sha256` 作为执行 CLI 的外部锚。这个绑定只适用于创建它的实际 predecessor 结果。

## 部署与执行

固定新阶段为 `/workspace/p26-cell05-all-row-arithmetic-20261127-v1`。将已绑定工具目录完整安装至该阶段的 `tools/p26/cell05-all-row-arithmetic-20261127/`，并放置以下两个输入。

- 新目标源码位于 `project/ImbalancedChen/P2OriginalSaving19Cell05AllRowArithmetic.lean`，6895 B，SHA-256 `8a271737e570b277b2f30a39ec193fe72480f8e685de5860e648b8477918c931`。owned 审计为工具目录内的 2718 B 文件，SHA-256 `27f18c413bc763a619daf32400e7f8d217acfbb32e892242e48f38679afc2e64`。
- FastDet 原 capsule 有 11 个成员；按原相对路径安装到 `inputs/fastdet/`。原 capsule 为 304084 B，SHA-256 `f6ae2abda0d4e215c5903ac2a4c44391e2c5d5f3a9dd6dbf714f7d6b5fad677d`。TRANSPORT 为 9926 B，SHA-256 `a7cd0646913fb7c485f328c0eb97a6e55e76b3a15d730ae628ce3f3ece54eee9`。核对原 manifest 单项、完整原审计/运行时元数据、FULL_SOURCE_CLOSURE 的 JSON 指针、原 argv/cwd/source/object/dependencies/log。该供应者只有原 normal 和原 stock kernel 两条，旧 proof 命令数和新增旧 owned 审计数均为零。

root 的 P2 作业使用 13107 MiB 和 3600 s。每个新 Lean 命令进程树预算为 12 GiB、900 秒。部署前保证新阶段与前驱阶段物理隔离；首次 preflight 复制 130 对源/对象到自己的 project/objects 根，拒绝硬链接到源供应者。项目 import 图必须恰为这 130 个供应者；外部 LEAN_PATH 与 sysroot 下的 ImbalancedChen fallback 被排除。每次执行沿用原环境，只有 LEAN_PATH 首个对象目录变为新阶段。

```sh
ARITHMETIC_STAGE=/workspace/p26-cell05-all-row-arithmetic-20261127-v1
ARITHMETIC_RUNNER="$ARITHMETIC_STAGE/tools/p26/cell05-all-row-arithmetic-20261127/run_arithmetic.py"
python3 -I -S -B "$ARITHMETIC_RUNNER" preflight --workflow-sha256 "$ARITHMETIC_WORKFLOW_SHA"
python3 -I -S -B "$ARITHMETIC_RUNNER" run --workflow-sha256 "$ARITHMETIC_WORKFLOW_SHA"
python3 -I -S -B "$ARITHMETIC_RUNNER" verify --workflow-sha256 "$ARITHMETIC_WORKFLOW_SHA"
```

normal 和完整 owned 必须使用 `--trust=0 -DwarningAsError=true -j1 -M12288 -DmaxRecDepth=1000000 -DmaxHeartbeats=0`；stock kernel 直接以 `leanchecker --verbose ImbalancedChen.P2OriginalSaving19Cell05AllRowArithmetic` 复核同一对象。执行使用独立非阻塞锁和每种模式的独占、落盘启动见证。丢失收据后仍保留见证即拒绝重跑。失败/不连贯状态保留供 root 处理。每次入口、每个 proof 前后及最终导出核对 Gaps retained 和当前 inputs。调用 Gaps 前先校验其整个指定工作流文件清单及额外 Python/字节码候选，再在独立隔离进程运行原 driver 的只读 verify；其原 Shape/recovery 复核保持原 contract。

仅显式调用 normal/kernel/owned 时，也只允许下一个缺失步骤；成功前缀逐字复核。全模块所有 private/generated 声明必须通过序列化和 declaring-module 全清单等价及全类型、传递公理检查。源码 15 个显式 print 的 public/private 展示名需分别唯一对应真实 owned 声明。只有完整三项可以签一个 owner 的 SUCCESS，七组私有行均不单独计为 accepted。

最终 `exports/arithmetic-evidence.tar.xz` 包含新源码、对象、审计、三条原命令与收据、全量 owned、见证、配置、工作流、FastDet 11 个输入，以及 Gaps 完整前驱 archive 和固定 summary。独立 `verify` 只读复核现有 SUCCESS/index/archive。当前作者工作限于本地 Python 夹具、原 FastDet 数据及静态审查；真实 CONFIG、阶段预检、Lean、RSS/wall 和正式 acceptance 都须由 root 后续核验。
