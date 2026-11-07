# P0 第二轮：P1 与运行环境只读回执

观察日期：2026-10-12。精确 UTC 时间、文件哈希和已见进度见 `p1-intake.json`。

## 接收身份

P1 共同证明基线及本地 HEAD 为 `1a80c1bcce67886f699d097fc37fd245cd3620bf`。
本地确有四个新生产模块、两份验证 Lean 文件、交接、根导入补丁和验证脚本；它们尚未提交。
远端预告分支 `chatgpt/chen-p1-history` 的 ref 查询返回 404，完整可见分支列表也未列出该分支。
因此本回执未取得 P1 交付完整提交 SHA；这表示固定交付待取得，绝不表示 P1 没有成果。
`provisional-source/` 只保存带精确哈希的审查快照，不作为已接收集成代码。

四个生产模块：

| 模块 | 当前供给范围 | 接收 Part |
| --- | --- | --- |
| `OrdinaryLowerFourFrontier` | ordinary lower rank-three parent 的实际候选字典及四行仿射区域 | P1、P2、P5 |
| `ActualSelectedPrefixLowerCellSum` | 全实际 lower-fourth correction 与 owned-cell residual differences 的有限恒等式 | P2、P5 |
| `ActualSelectedPrefixLowerOwnCubeIntegral` | 真 Lebesgue 积分、实际 prime sum 极限、有限检查后的 selected lower density 极限 | P2、P5 |
| `HistoricalPrefixCertificate` | 固定有理 common-mesh 3/4/5 层 cap 数据、继承 fallback、有限 level check、实际 telescope、raw odd policy 字典 | P2、P3、P4、P5 |

它们没有提供采用表的具体实例、历史第五真实积分、whole-box 平方/包络许可、boxed compiler、physical support、分布定理、完整 K/c 或 hLower/hUpper。lower-fourth restoration 与 P2 same-mask fibre 的 gain 不能重复计账。

`p1-provisional-types.md` 给出八条关键完整源码声明头；这些不是编译器确认类型。

## 已有验证的精确范围

观察时，`logs/closure/plan.json` 是五目标计划：四个生产模块及 `verification.parts.p1.Part1HistoryAudit`。
该计划包含 9367 个 source modules，8679 个官方缓存 modules 和 688 个本地待编译 modules。
读取回执时 state 已有 491 条完成记录，P1 新生产目标尚无完成记录；closure 最终结果、六目标 kernel replay 结果和最终 receipt 尚不存在。
日志不断出现完整 `FRONTEND_OK` 与 returncode 0 记录，未观察到最终失败，但本审查未取得可用进程列表，不能仅凭日志断言实时进程状态。

当前 `compile_closure.py` 已列六目标，新增 `LevelCheckProbe`；其变化晚于落盘五目标计划。后续不能仅凭当前脚本把旧运行记成已覆盖六目标。P1 自身的 `finalize_receipt.py` 对最终目标集、源码/对象/直接导入哈希、strict 模式和六条 replay 行都设有检查。

本审查未启动、重启、中断或重复任何编译/重放，也未更改 P1 的源码、驱动、缓存、对象或日志。

## 锁定环境

官方工具链为 `leanprover/lean4:v4.33.0-rc1`，Lean githash：

```text
62eed1db4d67327ec8120be05f1a1b0847d74561
```

GitHub 官方发行 API 的 Linux archive asset 478017041 声明 SHA-256：

```text
25e7b3e18ec75a4e2529fc23194be8e3cc3183df99b553f870d8a111c7488210
```

该值与 P1 下载验证记录一致。本审查重新计算 lean、lake、leanchecker 的文件 SHA-256，均匹配其原始记录；重新读取全部 11 个依赖的 Git HEAD 与 tracked status，全部 exact pin 且 tracked clean。

官方发行工具路径：

```text
/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux
```

stock `lean --version` 已有真实诊断 `error: failed to locate application`；stock `lake --version` 能启动。P1 通过独立 Lake script 使用未修改的 `Lean.Elab.runFrontend`，并显式 `trustLevel := 0`、目标 `warningAsError := true`。这是真实官方 frontend API 编译，必须与 stock `lake build` 分别记录。

驱动中 `unsafe Lean.enableInitializersExecution` 是官方 frontend 初始化 API，不是向证明环境加入 unsafe 定理或跳过 kernel 检查。官方 `Lean/ImportingFlag.lean` 说明 frontend 启动时调用此方法；官方 `lake/Lake/Load/Lean/Elab.lean` 也在读取扩展前调用同一方法。约束是每个进程初始化时单线程、不得混载同名模块的两个 native 版本；现有驱动为每个模块启动单独 Lake 进程。

P1 的 metadata shim 只回应 `--print-prefix`，对其他输入退出 64。它仅用于 cache bootstrap；实际编译/重放记录的 `metadata_adapter` 为 false。P0 验证不应把该 shim 放进 PATH。

## 原装 leanchecker 的正常启动方式

官方 `LeanChecker.lean` 的 main 首先调用 `initSearchPath (← findSysroot)`。
官方 `Lean/Util/Path.lean` 中 `findSysroot` 在设置 `LEAN_SYSROOT` 时直接返回该目录；只有未设置时才调用子进程 `lean --print-prefix`。
因此原装 checker 不需要可启动的 lean CLI，也不需要 fake lean shim：

```bash
export LEAN_SYSROOT=/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux
export LEAN_NUM_THREADS=1
# LEAN_PATH 由 P0 自己的对象输出目录及已核对的依赖对象目录组成。
# P0 输出目录在先，且同一个 module 只选择一个已核对源码版本。
"$LEAN_SYSROOT/bin/leanchecker" --verbose MODULE
```

这段代码是供 P0 执行的启动入口；本审查没有运行它。`LEAN_PATH` 应在具体 P0 验证工作树生成并记录，不能把占位 MODULE 视作完成验证。
checker 默认重放命名模块中定义的声明，包括其 private 数据部分；加载依赖不等于对全部依赖声明重新重放。完整公共根检查仍是 P0 的独立门槛。

可复用 runtime 与已完成缓存，但 P0 必须写自己的对象目录；读取共享已完成对象前后核对源码及对象摘要，避免使用仍在写入的对象。不要通过 hardlink 后覆写对象的方式破坏 P1 缓存。

## P5 Buchstab 优先验证

`MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation`、`LiLiuPrereqBuchstabFunction`、`LiLiuPrereqBuchstabIntegral` 和 `LiLiuPrereqBuchstabBase` 不在 P1 当前 688 本地模块计划中。
观察时 TailPropagation 无完成记录、无对象。P1 已完成的 `LiLiuGoldbachBuchstab` 是另一个模块，不能充当它的验证回执。
因此 P0 可以在自己的输出目录验证 P5 所需最小 Buchstab 闭包，并复用已完成的 mathlib cache；无须等待 P1 整体结束。

## 原始证据位置

- P1 handoff：`/workspace/scratch/127408f63891/goldbach-formalization/verification/parts/p1/HANDOFF.md`
- stock CLI 初始诊断：`/workspace/scratch/127408f63891/lean-runtime/runtime-probe.json`
- 逐模块命令与 stdout：`/workspace/scratch/127408f63891/lean-runtime/logs/closure/`
- 主进度：`/workspace/scratch/127408f63891/lean-runtime/logs/closure-run.log`
- 对象和依赖摘要状态：`/workspace/scratch/127408f63891/lean-runtime/logs/closure/state.json`
- 六目标原装 checker 驱动：`/workspace/scratch/127408f63891/lean-runtime/replay_targets.py`
- 最终回执生产器：`/workspace/scratch/127408f63891/lean-runtime/finalize_receipt.py`

本目录 `observed-runtime/` 保存审查时读取到的证据快照，并不修改原件；后续 P1 完成回执后须用完整固定 SHA 重新绑定目标源码。
