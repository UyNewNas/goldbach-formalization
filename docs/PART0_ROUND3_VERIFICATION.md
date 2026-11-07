# Part 0 分批集成与验证：round 3

本批接收 **8 个新生产模块、198 个所属声明**；累计接收 **19 个生产模块、591 个所属声明**。接收以固定 Git 源码、真实严格编译记录、同对象原装内核重放和完整所属声明公理审计为依据。各 Part 正在续作的候选另外列出。

这里的“接收”指组件三门已通过。包含新公共导入的集成提交仍须经过其自身完整 CI；旧根成功不覆盖新增导入。CI 会在精确 `GITHUB_SHA` 上保存完整构建、根内核重放、根公理审计，以及本批完整类型导出的实际结果。

## 1. 固定版本和保护项

| 用途 | 完整提交 |
|---|---|
| 共同证明基线，来自 `codex/variable-envelope-boxes` | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 手稿基线 | `ba6ec11d800eccc54406490631895e174de85766` |
| P0 首轮文档 | `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` |
| P0 前轮完整回执 | `80aca6710c83b5160f4c5fdd05d180e507990e95` |
| 本批实际集成父提交 | `cce2334906f068fda2f58c400646366f2aa2d417` |
| P1 固定证明；最新交接仅另改 CI 时限 | `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f`；`7f894bfb57b7aa561360e335c6d610b7c30614e0` |
| P2 固定证明；最新交接 | `6acf61cc28f227a9154363f2347c386ec01dffb0`；`076473720210ee602e6e9735902e16bb6c5f1398` |
| P3 固定交接 | `f37f341412eb239f7e7e8937921ee8d01c9c2922` |
| P4 固定交接，五生产源码仍属首轮候选 | `3d5dd058cf6bef5fe90719ee277580baf8b5bf41` |
| P5 固定交接 | `bf54caeb5e708474cacefac13a171d307b4c64f2` |

`cce23349…` 相对 `80aca…` 只把核心 CI 的 job 时限改为 150 分钟、完整构建步骤时限改为 90 分钟；原三道检查保留。本批从它快进，不覆盖该修改。

Lean 仍为 `leanprover/lean4:v4.33.0-rc1`，全部 11 个依赖 pin 保持。`lean-toolchain`、`lakefile.toml`、`lake-manifest.json`、手稿地图、外部复用说明、`CurrentMainTheorem.lean` 和 `CurrentNumericalTransfer.lean` 已逐字与共同基线比较，见 [protected-sources.json](../verification/parts/p0/round3/protected-sources.json)。没有新增数学公理、未完成证明或非内核决策替代。

## 2. 新接收模块及真实门

下表秒数是生产者已完成的实际调用时长，P0 没有再执行同版本生产编译。完整源码 SHA256、对象 SHA256、命令、原始日志及接收检查见 [逐模块台账](../verification/parts/p0/round3/ledger/MODULE_LEDGER.md)。

| Part / 所有文件，均在 `ImbalancedChen/` | 严格编译 / 秒 | 原装重放 / 秒 | 所属声明 | 公理审计 |
|---|---:|---:|---:|---|
| P1 `OrdinaryLowerFourFrontier.lean` | 200.131 | 68.232 | 27 | PASS |
| P1 `ActualSelectedPrefixLowerCellSum.lean` | 214.859 | 28.921 | 9 | PASS |
| P1 `ActualSelectedPrefixLowerOwnCubeIntegral.lean` | 94.948 | 48.552 | 8 | PASS |
| P1 `HistoricalPrefixCertificate.lean` | 93.780 | 47.087 | 96 | PASS |
| P2 `Certificates/PairedV2Geometry.lean` | 4.919 | 3.160 | 10 | PASS |
| P2 `Certificates/PairedV2Prefix4Data.lean` | 3.696 | 3.105 | 11 | PASS |
| P2 `Certificates/PairedV2Prefix4.lean` | 7.675 | 3.496 | 35 | PASS |
| P3 `Part3LongSlotNormalization.lean` | 9.477 | 2.785 | 2 | PASS |

P1 的 140 项生产声明与 10 项 probe 声明分开计数。P0 验收实际核对其 2,196 个归档成员、689 条编译记录、1,350 个内部 import 对象连接及 6 次 checker 记录。P2 三新模块的 56 项与原六模块 253 项组成 309 项联合审计；正常托管专项 CI 的 309 项记录与固定生产者记录逐项全等。P3 归档中的 35 个成员、4,957 模块/29,642 文件生产导入库存和增加目标后的实际审计库存已交叉核对。

原始失败继续保留：P1 probe 的缺失对象与早期 `decide` 诊断，P2 Geometry 的 `mod_cast` 及 Prefix4 的定义重写诊断，P3 审计入口的两次 module/legacy 格式诊断。这些失败没有改写成后来版本的通过结果；本批没有修改任何 Part 的生产证明。

P0 修改公共 `ImbalancedChen.lean`，显式导入这 8 个模块，并维护本批统一台账、验证入口和类型导出。其他 Part 的源分支未被修改。

## 3. 数学接口及精确范围

### P1 → P2 / P4 / P5

普通 lower-fourth 的实际有权素数和、严格处理顺序、保留的第二 cube 门、两侧各自的第四 own-cube 指示、有限 Ico ownership 和精确 fallback 消去已经接到真实 Lebesgue 积分。有限历史 cap 数据还给出祖先投影、可计算的有限 level check 和实际第三至第五层 telescope。

完整的 52 条生产 theorem 声明头及其原始编译器输出对应见 [SOURCE_HEADERS_BOUND.md](../verification/parts/p0/round3/intake/p1-intake/SOURCE_HEADERS_BOUND.md)，14 条关键完整接口见 [KEY_THEOREM_TYPES.md](../verification/parts/p1/KEY_THEOREM_TYPES.md)。采用表的 license、整体覆盖、真实 boxed rho、物理支持、完整历史积分和全局数值端点仍是后续输入。P2 的单方接口草案尚未自动成为 P1 的已确认定理。

### P2 → P1 / P5 / P0

采用证书仍是手稿固定的 **same-mask-v2**，17,572 行、原始序号不改。本批只闭合 **E0 的第 0–3 行**：

\[
\frac{12676565261567}{10^{20}}
\le \operatorname{Prefix4.integral}
\le \frac{12676572571081}{10^{20}}.
\]

Geometry 给出实际开纤维的端点、顺序、非空、E0 residual 门和 Buchstab 参数至少 `7/3`。本批有限和**包含此前首格**，不可再次加上首格收益。`K/80` 已包含 `(K/4) × (1/20)`；不能重复乘付 Buchstab 增益。完整编译器类型见 [prefix4 的类型单](../verification/part2/round2/prefix4/key-theorem-types.txt)。

剩余各行、E1、saved-floor、历史父许可、并域积分和覆盖、不重计、Y6/Y11 完整配对及误差总账未闭合。P0 再运行了固定生成器的 `--check-generated`，两个生成文件逐字相符；该 Python 结果只证明数据对齐，数值证明依据另列的 Lean 三门。

### P3 → P4 / P5

`part3_eventually_longSlot_logAccuracy` 与 `part3_eventually_longSlot_singularNormalization` 在固定 `theta < 1` 后，统一选择 N 阈值，再量化所有 `M D L U a` 和复系数 `alpha rho`。保留实际的 `(a,q)=1` 模数集合、系数支撑上的范数界和 `M D ≤ N^theta`。两条完整编译器类型见 [COMPILER_TYPES.md](../verification/parts/p3/long-slot-normalization/COMPILER_TYPES.md)。

本批只处理无 rough/prime 筛选、零相位的整数 long slot。实际 policy 推出乘积长度幂次间隙、rough/prime 长槽、相位、Brun/Mellin 成本、restricted medium、two-long 均仍需供应。

### P5 Buchstab 与 S1Carrier

已接收的 Buchstab `11/20` 解析界继续供应 P2。固定 goldbach pin 中的 `MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier` 另有可复用三门：118.928 / 41.873 / 366.102 秒，36 项所属声明全部通过公理审计。它是既有依赖的验证结果，**不计为本批新增生产模块**。17 项公开定理有完整 `pp.all` 与精确 Expr；默认打印的全部 36 项中有两项含证明省略，不能称 36 项类型已全部完整导出。见 [S1Carrier 固定交接](CHEN_P5_S1CARRIER_HANDOFF.md)。

`CurrentChenInitialSource` 的固定修复在 `a03a57265a49d542e6fac8ba72094dd673e5ed7d`，源码 SHA256 为 `4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956`。生产者三门已经完成，但旧 schema 没有记录审计导入对象的前后身份；P0 按上一批相同标准仍需补同对象审计绑定。不能补造历史字段。当前环境缺缓存，该补查未运行；它继续作为明确的固定候选，未加入公共根。`CurrentChenInitialMean` 也未通过本批验证，`(33/4) log 3` 更不等于已采用 L1 或完整 Chen 均值。

## 4. 第五层候选的实际身份

已取得 P1 当前两份未提交源码：

- `HistoricalUpperFiveCellGeometry.lean`，12:07:42 UTC 快照 SHA256 `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b`。
- `ActualHistoricalFifthCellIntegral.lean`，同次快照 SHA256 `dd9afad8cae4c977b8c6916e12ac38d0c4edeb5f7b1e0d42768958bae30f031a`。

它们含历史 joint-cell 的真实源码和 `tendsto_fifthPrimeCorrection_ceil` 目标，但没有固定提交或匹配编译回执；当时对象不存在。P1 自己的同时点说明也将它们与先前报告的独立第五层积分候选分开。因而，**先前“仅过单模块编译”候选的固定提交、文件和原始回执仍未对应**。本批没有把检索不到推成没有成果，也没有把当前续作误当作该旧候选。快照及检索范围保留在 [FIFTH_CANDIDATE_SCOPE.json](../verification/parts/p0/round3/intake/p1-intake/FIFTH_CANDIDATE_SCOPE.json)。

## 5. 完整 CI、本地启动与类型口径

实际父提交 `cce23349…` 的 [核心 CI 38227766990](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38227766990) 已完成：

| 原始阶段 | 实际结果 |
|---|---|
| 完整构建 | 9,790 jobs，exit 0，3,226 秒 |
| 原装 `leanchecker --verbose ImbalancedChen` | exit 0，506 秒 |
| 固定 axiom-audit v0.1.2 | 5,260 项根声明，exit 0，31 秒；仅标准三公理 |

原始 artifact SHA256：`d9564a4138840c7ac620988cbd957616d662750e361b005e1aa7c21fc7bec2cb`。日志、timing 和 outcomes 已保存在 [prior-ci](../verification/parts/p0/round3/prior-ci/)。`80aca…` 的核心构建最终 cancelled，后两门 skipped；其 VE 工作流成功。这些状态分别归属各自完整 SHA。

本机于 2026-10-12 12:02:34 UTC 对哈希不变的官方 `lean --version` 作正常启动尝试，退出 1：`error: failed to locate application`。随后只读全工作区查询没有找到 Mathlib `.olean` 缓存。没有重复启动依赖闭包、修改工具链、触碰其他 Part 的任务或以无步骤 CI 重跑代替验证。

本批初始入账时，P1 的默认打印有 7 项 `⋯`，其余 Part 的新 58 项已有完整显式编译器类型。新的 `Round3Audit.lean` 复用 P0 已通过的审计代码，只补当前 198 项类型及现有条件式主桥的完整类型；它不会把 `hLower` / `hUpper` 消去。CI 的类型步骤保留 exact SHA、实际对象/源码前后哈希、原始输出和失败诊断，只有真正执行成功才写 PASS。**本文件中的组件通过不预告该新步骤或新整根 CI 已成功。**

## 6. 可直接执行的入口与后续输入

在正常、固定工具链且依赖已按 manifest 准备的 checkout 中，以下入口显式覆盖新增模块；它们不会更新 pin：

```bash
bash verification/parts/p0/check_batch.sh p1-history
bash verification/parts/p0/check_batch.sh p2-prefix4
bash verification/parts/p0/check_batch.sh p3-normalization
```

它们用于需要重新验证的环境；同源、同对象且已经完成的三门可以按本批原始回执复用。新的完整 CI 在当前 Git SHA 上执行全项目构建、原装根重放、根公理审计和类型导出，不能被上述小批入口替代。

P4 专项 run `38227776544` 的真实失败是依赖构建 Python 子进程 1,800 秒超时，止于 9,326 / 9,404；五目标尚未进入，原日志没有 Lean `error:`。核心 CI 成功没有导入这五个叶。P4 的本地修复仍未固定，不接收为已证明 K 或 hUpper。

实际 same-rho 的 K 密度界（P4-A）、hUpper（P4-B）、完整十一项 Chen 均值/c/hLower（P5）、完整证书和真实历史构造/分布仍未齐备。**P5 只等待 P4-A，不等待 P4-B。** 原 `current_theorem_1_1_of_manuscript_bounds` 与条件式数值桥保留；当前仍没有去掉 hLower、hUpper 或等价未证输入的完整最终入口。

真实常数仍为 `K = 8452171/1250000`、`c = 49044063/25000000`；实数参数仍是固定 `1/2 < b < 1` 后取 N 极限。实际权、计数、素数删除、配对方向、factor-four 及 `singularNormalization` 没有由本批改写。
