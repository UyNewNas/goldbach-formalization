# Part 0：储存 cap、前 64 行和 S1LowerRosser 的分批接收

本批从已完成整根验证的 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` 接入 **4 个生产模块、414 项所属声明**。累计组件接收范围为 **23 个自有生产模块、1,005 项所属声明**。固定依赖的 S1LowerRosser 另有 8 项声明，不计入这两个数字。

组件接收依据是固定源码及已经实际完成的严格编译、同对象原装重放和完整所属声明公理审计。本文件随新集成源码一起提交，因而不预报该新提交的 CI 结果。新提交必须另行通过完整构建、四个明确指定的生产目标、根内核重放、根公理审计、原 Round3 类型门和新增 Round4 类型门。执行结果绑定实际 `GITHUB_SHA`，由原始 Actions artifact 及后续接收回执给出。

## 固定来源与文件所有权

| 用途 | 完整提交 |
|---|---|
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 手稿起点 | `ba6ec11d800eccc54406490631895e174de85766` |
| P0 已验集成父提交 | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` |
| P1 本次固定交接 | `744316efd1887f21c91dd4b63c218fa27704c931` |
| P2 实际证明 | `f0c00f9ccce98e04af439321a92eb9fd0dd26203` |
| P2 成功专项 CI 的源码 | `e6d6d57323cc358cef060fb243ec386c13cb662d` |
| P2 最新交接，仅更新说明 | `101bb2291cd51f9717544ce477122fdd44eda44d` |
| P3 当前固定交接，未变 | `f37f341412eb239f7e7e8937921ee8d01c9c2922` |
| P4 当前固定交接，未变 | `3d5dd058cf6bef5fe90719ee277580baf8b5bf41` |
| P5 本次固定交接 | `7b1283e4a70874e4fb7004bafad0793069bdea71` |

Lean 仍是 `leanprover/lean4:v4.33.0-rc1`。goldbach pin 为 `09b97db5764ade1246bfb77206baa1b124760958`，mathlib pin 为 `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`；全部 11 个依赖 pin 不变。`lean-toolchain`、`lakefile.toml`、`lake-manifest.json`、手稿地图、外部复用说明以及两个最终条件式桥文件保留原字节。

P1 的 `StoredHistoricalBoxPermit.lean` 和 P2 的三个 `PairedV2*64*.lean` 均按固定 Git blob 原字节接收，没有 P0 生产证明补丁。P1 `round2/permit/` 的原始证据、P2 `round3/` 的原始证据和 P5 的 173 个新增证据文件分别按其所有权保存。固定文件逐字节来源清单在 [installed-fixed-files.json](../verification/parts/p0/round4/installed-fixed-files.json)。

P0 独立维护根的四个增量 import、Round4 类型门、分批验证入口和本台账。P2 新生成器原样接收；旧 `verification/part2/CertificateAudit.lean` 仍保留 309 项审计。新的 709 项 owner audit 原字节复制到 P0 的 `CertificatesPrefix64Audit.lean`，仅改变辅助文件路径，避免旧分批入口增加未声明的新依赖。P2 后继 `check.sh` 和旧回执的更新版本只归档；它们冻结的 424 个 P2 父树文件不适用于根导入已改变的 P0 树，原接收器的范围检查没有被删减。

## 实际组件门与接收检查

| 模块 | 严格编译秒数 | 原装重放秒数 | 所属声明 |
|---|---:|---:|---:|
| P1 `StoredHistoricalBoxPermit` | 4.776 | 24.410 | 14 |
| P2 `PairedV2Batch4To64Data` | 7.281 | 4.014 | 72 |
| P2 `PairedV2Batch4To64` | 222.062 | 18.479 | 207 |
| P2 `PairedV2Prefix64` | 36.238 | 36.114 | 121 |
| 固定依赖 `LiLiuGoldbachS1LowerRosser` | 259.896 | 95.498 | 8，单列 |

以上原始调用均退出 0。P1 审计同时包含生产 14 项和 probe 22 项；P2 全部 12 模块合计 709 项，旧 309 项记录逐条不变；P5 审计是 7 theorem 和 1 definition，包含 private 和 generated 声明。仅出现 `propext`、`Classical.choice`、`Quot.sound`。

P1 原 archive 的 130 成员、129 payload、29 固定 repo 文件及 31 条本地直接 import 对象绑定均已核对；13 个旧生产供应源码与 P0 父提交相同。哈希清单引用而未嵌入的缓存二进制仍明确作为摘要引用，未声称本次重新取得全部对象。P2 的 50 条原始 import 对象绑定、实际专项 CI 的 180 个源码输入与两个固定提交的 360 次比较全部相符。709 条类型在生产者日志、CI artifact 和 CI job 原日志逐项一致。P5 目标 `.olean` 归档已经解码，编译输出、重放输入及审计直接导入对象相同；96 个历史本地模块、430 条导入哈希也已核对。

P2 的 [专项 CI 38252572597](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38252572597) 确实执行了 12 模块显式构建和严格检查、12 个重放目标、709 项审计；三个阶段耗时 239、104、43 秒，均成功。其 artifact SHA256 为 `4f0b9cc1232226392515eda5ccf880a40241cc5afc8d6defcbac45206089d663`。P0 没有再触发这个版本的构建。

详细消费者回执分别在 [P1](../verification/parts/p0/round4/intake/p1-intake/REUSE_RECEIPT.json)、[P2](../verification/parts/p0/round4/intake/p2-intake/P2_INTAKE_RECEIPT.json)、[P5](../verification/parts/p0/round4/intake/p5-intake/P5_FIXED_INTAKE.json)。这些回执不冒充本机执行 Lean。原生产者官方 frontend 的 `trustLevel=0`、严格 warnings 及后续 stock replay 保留；归档的初始化 helper 使用既有 `unsafe Lean.enableInitializersExecution`，它不被生产证明导入，本批没有执行该 helper 或引入证明绕过方式。

## 数学接口与未闭合输入

### P1：任意实际储存 cap 的许可

`storedMeshCapCheck_actual_square_gates` 将有限表 `J/I/old/nu/cap` 的有理 checker 成功转为同一实际素数元组的严格前缀平方门和所选子乘积平方门。cap 可以是许可区间内实际储存的值，原 midpoint 情形仍是特例。完整 12 个公开声明头与 14 项编译器类型分别见 [KEY_INTERFACES.md](../verification/parts/p0/round4/intake/p1-intake/KEY_INTERFACES.md) 和 [COMPILER_TYPES_PRODUCTION_14.json](../verification/parts/p0/round4/intake/p1-intake/COMPILER_TYPES_PRODUCTION_14.json)。

调用方仍须供应实际采用表、checker 成功、`old j` 与继承历史的等式、覆盖、物理载体和支持。old/new 的 own-cube 门继续分别处理。该许可没有假定积分上界、K 或 c，也未证明这些解析目标。接收方为 P1/P2/P3/P4-A/P5。

### P2：原始 `[4,64)` 追加到 `[0,4)`

采用证书仍是 **same-mask-v2**，17,572 行及原始序号保持。新增 60 行和已有 4 行都是 E0。

| 实际积分和 | 精确下界 | 精确上界 |
|---|---|---|
| `Prefix4.integral` | `12676565261567 / 10^20` | `12676572571081 / 10^20` |
| `Batch4To64.integral` | `190579962282066 / 10^20` | `190580072663307 / 10^20` |
| `Prefix64.integral` | `203256527543633 / 10^20` | `203256645234388 / 10^20` |

`source_ordinal_coverage` 证明原始行号恰覆盖 `n < 64`；`rowIndices_injective` 另外证明实际网格坐标单射。`integral_eq_parts` 使用 `Fin.append` 与 `Fin.sum_univ_add`，使旧四行只计一次。`integral_semantics` 给出真实四重积分有限和，核是 `1/(t*u*z^2*w)`，系数是 `K/80`，已经包含 `(K/4)*(1/20)`。这里的证书 K 恰为既有有理值 `8452171/1250000`；它的数值实例化不证明实际 rho 的 K 密度界。

完整编译器接口在 [KEY_INTERFACES_COMPILER.json](../verification/parts/p0/round4/intake/p2-intake/KEY_INTERFACES_COMPILER.json)，其通常记号在同目录 `.md`。新增 400 项都有原始完整 `pp.all`。接收方为 P1/P2/P5/P0；P4-A 上界证书范围没有扩展。

仍缺 E0 `[64,6091)`、E1 `[6091,17572)`，合计 17,508 行，以及 saved-floor 语义、几何并域、历史许可、计数与积分身份、Y6/Y11 全配对及误差总账。有限行号无重复不替代实际几何并域和历史 mask 证明。

### P5：有限 Rosser 主项减 AP 前缀误差

固定依赖 `MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser` 已供应两个公开定理：`goldbachS1BoundingSieve_lowerErrSum_le_prefixSum` 和 `goldbachS1_lowerRosser_mainTerm_sub_prefix_le`。它们保留真实差集单位权、严格端点 `ceil((1-ε)N)-1`、筛计数、Rosser 权、totient 主项和 AP 前缀误差。完整编译器类型见 [PUBLIC_TYPES_COMPLETE.md](../verification/parts/p0/round4/intake/p5-intake/PUBLIC_TYPES_COMPLETE.md)。

8 项均有实际 explicit 和原始 Expr 完整输出；它们不是 `pp.all`。一个 generated 默认类型含证明省略，因此不得把所有默认打印称为完整。该依赖不计作新自有模块，本批根 CI 也不自动覆盖未进入根依赖闭包的目标。其接收依据仍是本次绑定的固定生产者三门。

下一独立模块 `LiLiuGoldbachS1MainMass` 的源码 SHA256 为 `4fdcdd6001278a1c7636a40ba8f2e2e6c685a20331a4b0c803c0146f516a4533`，本批仅阅读源码，未执行它。AP 误差归一化支付、Beta 主质量/密度/尺度、InitialSource 同对象补审计、InitialMean、十一项完整均值、解析 c 和 hLower 仍开放。**P5 只需要 P4-A，不等待 P4-B。**

### P3 / P4 与最终入口

P3 固定长槽分布和归一化接口继续供应；实际 rough/prime、相位、Brun/Mellin、restricted medium 和 two-long 仍缺。P4 专项 run `38227776544` 的已有失败是依赖构建 1,800 秒超时，目标尚未进入且无目标 Lean 诊断；本批未重跑或把旧根成功作为五个 P4 候选已验的依据。

实际 same-rho 的 K 密度、hUpper、完整 Chen 均值/c/hLower 均未齐备。当前 `current_theorem_1_1_of_manuscript_bounds` 仍具有真实 `hLower` 和 `hUpper` 输入；Round4 门完整打印其类型并记 `hLower_hUpper_discharged=false`。没有把它们藏进结构或类型类，也没有增加伪装成完整结果的最终入口。

常数仍是 `currentK = 8452171/1250000`、`currentC = 49044063/25000000`；先固定实数 `1/2 < b < 1`，再取 N 极限。实际权、计数、方向、平方情形、factor-four 和 `singularNormalization` 的定义均未改动。

## 第五层固定候选与原始诊断

P1 两份续作现在已有固定提交 `744316efd1887f21c91dd4b63c218fa27704c931`：

| 源码 | SHA256 |
|---|---|
| `HistoricalUpperFiveCellGeometry.lean` | `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b` |
| `ActualHistoricalFifthCellIntegral.lean` | `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de` |

geometry 与上批快照相同，integral 只比上批 `dd9afad8…` 多了说明注释。四个目标（含 probe、audit）均未开始 frontend；恢复队列停在 162/683，不能记为单模块编译成功。源码仅以 `.lean.txt` 身份保存，不加入生产 import。先前独立报告的“继承前层选择、仅过单模块编译”候选仍缺对应固定源码和原始回执；它与这两份续作不能合并身份。

P2 首个真实目标诊断是旧 `PairedV2Prefix64.lean:142:0` 在 200,000 heartbeats 下 `whnf` 超时；P2 仅将该局部定理预算改为有限 1,000,000 后通过三门，原始失败仍在。P5 辅助 audit 的首个错误是无法合成 `MonadWithOptions CommandElabM`；修复只涉及辅助审计。消费端历史对象搬迁/附件格式比较的失败也保留，并与 Lean 错误分开记录。P0 本批没有生产修复。

## 已验父提交、类型口径和可执行入口

已恢复并逐字核对父 SHA `28fd630…` 的 [核心 run 38250288277](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38250288277)：

| 阶段 | 实际结果 |
|---|---|
| 完整 lake build | 9,798 jobs，35 秒，exit 0 |
| stock 根 leanchecker | 365 秒，exit 0 |
| axiom-audit v0.1.2 | 5,458 项根声明，25 秒，exit 0 |
| 原 Round3 类型导出 | 198 项及主桥，473 秒，exit 0 |

父 artifact SHA256 为 `6927d09d7e2b4cd7dd201f21169c07111ff4325f77478682f5c316f551940e42`。恢复证据无需重跑已经完成的同版本构建。旧 591 项的正确格式是 **586 个完整 pp.all 和 5 个完整默认 Meta.ppExpr**；5 个 Buchstab 声明的原始默认打印不会被重标为 pp.all。本批接收时新 P1 的 14 项同样是完整默认打印，待新 Round4 实际通过才取得统一 pp.all。原始回执保留，格式修正在新映射中表达。

本机 PATH 未提供 Lean；对仍存的官方 Lean 文件作正常 `--version` 尝试，实际退出 1，`error: failed to locate application`。没有启动 Codex CLI/任务、重复工具链恢复或干扰 P1 构建。新集成使用现有正常托管 CI、原锁定工具链和缓存，保留所有既有门。

在正常、固定工具链和 manifest 依赖就绪的 checkout 中可执行：

```bash
bash verification/parts/p0/check_batch.sh p1-permit
bash verification/parts/p0/check_batch.sh p2-prefix64
lake build
lake env leanchecker --verbose ImbalancedChen
python3 verification/parts/p0/check_round3_types.py --timeout-seconds 540
python3 verification/parts/p0/check_round4_types.py --timeout-seconds 1440
```

上述两个分批入口显式覆盖目标，并保存第一处真实错误所在原始日志、源/对象哈希和退出码；已有同源码验证可按回执复用。最终整根公理审计仍使用 workflow 中固定 lean-action 的 `run_axiom_audit.sh`，不得由类型脚本替代。任一门未运行、超时、跳过或失败都不算新集成成功。
