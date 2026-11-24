# P1 原 seed 下界的最小接线候选

状态：**源码接线已准备，尚未在 P1 联合环境编译；完整 selected_checked 尚未验收。**

## 已确定的依赖切点

四个原始 P1 出口实际需要的是原 seed cell 的下界：

```lean
(archived seed : ℝ) + (savingLower slot21 : ℝ) +
  (savingLower slot22 : ℝ) ≤ cellIntegral seed
```

其中 `seed = .remaining (.nine 11)`，`cellIntegral` 仍是原
`P4AOriginalFull87SourcePrimeTests.cellIntegral`，两个 saving 仍为原账本的
`77410436074156865471 / 2^96` 与 `481322793305152847935 / 2^96`。

旧 `FieldFacts` 的 70 个 mixedMoment 字段、7 个 mixedTerm 字段、correction、
curvature diagnostic/total/raw 的精确舍入没有下游消费者；旧 T10Q6 只投影
`mixed_total.1`、`mixed_raw.1`、`raw_monotone`。旧 LogBranch 只使用
top guards、`gaps.1` 和 `selected.1`，没有使用 parent 或严格上端。
因此，这些强字段不是四个 P1 出口声明的义务。

接线复用既有
`P2Winner9CompleteSeedTerminal.complete_seed_ledger_le_original_full87_nine11`。
它的左端为原 `adoptedLogTotal` 加同两个 saving，原
`original_seed_log_selected` 将其接回 `archived seed`。没有新增假设，
没有删行、换分母、换积分或降低不等式目标。

## 六个 overlay 文件

| 文件 | 修改性质 | SHA-256 |
|---|---|---|
| `P4AOriginalFull87SeedRefinements.lean` | 原 owner 的 import 与两处下界接线；原 24 个具名声明全部保留 | `2265797c08e4eb06a140a3bbb2530be4e034983c5320507c37a972eb4d4d881f` |
| `P2Winner9CompleteSeedTerminal.lean` | 既有 terminal 全部证明不变，仅用现有 Chronology owner | `300532533e2b432104c4edfba2c6fd61617c2f462708d5957d12820def7c73fc` |
| `P2Winner9OriginalFull87Bridge.lean` | 既有 bridge 全部证明不变，改为 import P1 原完整 owner | `559fefb985a4e763bfbafc95195b678a944ce0c65c17ea98a39074771474e90d` |
| `P2Winner9T10TailJensen.lean` | 逐字复用已验 P2 文件；保留原 17 个具名声明头，补既有 5 个 binomial 声明 | `d0336d72641f7d3dc8fa40b4c046653b0a34f2e9b3eb30d6254019511a8f2ba1` |
| `P2Winner9SelectedPhysicalMeansJensen.lean` | 逐字提取已验 P2 的 4 个 Jensen 声明；原 SelectedPhysicalMeans 文件不动 | `f97687fce83a49145aa6b492e081bfb02c97bd05b80d1239cbfa46e4eafe5c5b` |
| `P2Winner9PhysicalCurvatureProbability.lean` | 既有 P2 文件仅增加上述补层 import，证明不变 | `395a4007727f40544ed4b3b102f40c2d483cc97eb78c11164cc585054160dfc6` |

Jensen 补层复用 `storedJacobian`、`jacobian_eq_stored`、私有
`actual_jensen_arithmetic`、`actual_Jensen_factor` 的完整已有代码。包括原先
`decide +kernel` 的那段证明也逐字复制，没有写新 numeric checker。
来源与原验收证据在 `COMPATIBILITY_SUPPLEMENT_RECEIPT.json`。

T10 新版把 `binomial10` 与 `binomial10RemainderNumerator` 从旧
SelectedAnalyticRemainders 的引用改为自身命名空间内的定义。两个定义文本均
与旧定义完全相同；17 个原声明头文字相同，涉及该名字的类型按定义展开相同。
旧 SelectedAnalyticRemainders 文件仍保留，没有删除其声明。

安装预条件：保留 P1 原 SelectedPhysicalMeans owner。不要同时安装完整 P2
SelectedPhysicalMeans 替换版与本补层，否则四个补充声明将重复归属。该原
owner 的必须匹配 SHA 写入 `INSTALL_PLAN.json`。

## 唯一中间 statement 表示变化

原 `selected_floor_sum_le_seed_integral` 左端的
`P2Winner9CompleteSeedSelectedFloors.selectedFloorSum` 展开为：

```lean
∑ i : RowIndex,
  ((entry i).mixedSelected : ℝ) / ((2 ^ 96 : ℚ) : ℝ)
```

这是原 `selectedFloorSum` 与原 `MomentDecoder.q96` 的定义展开；索引仍为
同一 `Fin 11026`，行仍为同一 `entry`，字段仍为 `mixedSelected`。保留
Rational `2^96` 的 cast，接入 Chronology 的 Nat Q96 时仅证明两个相同整数
分母的相等。其余 Full87 声明头均与原文件逐字相同。

## 数据和声明归属检查

- 四个原 P1 root 文件与 `terminal-reconcile/original` 的精确快照逐字节相同，
  overlay 中没有这四个文件。
- Full87SeedRefinements 的 15 个公开 theorem 全部保留，只有上面获准的
  中间表示展开；所有原量词和数据绑定保留。
- 原 bridge 所需的 62 个定义，与 P1 原 owner 的声明文本全部相同。无需安装
  P2 隔离验证使用的 11 个定义核或 13 个原 owner refactor。
- Seed90 文件在原复用包、当前 P1、当前 P2 三处全部字节相同。
- Chronology 使用已集成的单一 owner；不安装重复声明同命名空间的
  `P2Winner9LedgerBridge`。
- 原 MomentDecoder、T10Q6、LogBranch、SelectedFloors、GapReserve 源文件均
  保留。它们已从候选四 root import 闭包消失。
- 静态闭包无缺失源码、无环。已查到的 missing-name 缺口由 Jensen 补层与
  现有新版 T10TailJensen 供应。联合 Lean elaboration 和对象签名仍需核验。

## 可安装清单与发布分类

`INSTALL_PLAN.json` 是逐文件、逐 SHA 的安装清单：**872 个现成 P2 源文件 +
6 个 overlay，共 878 个条目**。其中仅 Full87SeedRefinements 与 T10TailJensen
覆盖已有 P1 路径；其他条目是新增的模块路径。不要遍历 P2 仓库覆盖 P1 的
其他同名文件，`IMPORT_BOUNDARY.json` 保留这些边界的两边哈希。

现成 P2 文件按 Git blob 而非仅路径分类；某些当前 active 文件的相同 blob
已在 source-only 路径提交，因此可以直接复用该 blob。

| 分类 | 文件数 | 含义 |
|---|---:|---|
| 已知 remote tracking commit 中存在同一 blob | 42 | 有原 GitHub commit/path/blob 可直接引用 |
| 本地 HEAD 中存在同一 blob，发布未在此核实 | 827 | 本地 `a5a42f8f70418a7b2b8a378713911e829786ec8b`；不能冒称已发布 |
| 当前字节不在以上已知 commit 中 | 3 | CompletePullingGeometry、RowArithmeticChecker、SelectedArchiveChecker |

这三个当前字节均有实际私有验证记录，但“已验证”与“已发布”是独立状态。
每个条目的完整 SHA-256、Git blob SHA-1、来源路径、已知 remote 引用、
编译和 replay 证据均写在 `P2_REUSE_FILES.json`。六个 overlay 的来源发布
状态另列于 `MANIFEST.json`。

## 验收边界

已读取实际 `context-recovery/p2-private-41880b-completed.log`：119 个模块的
独立 kernel replay 与 full-owned audit 均通过，两 worker exit code 均为 0。
结合此前 page0000 的独立验收，数值部分目前为 pages0000–0015 与 Check00，
即 **256 行**；几何部分有完整原支持 null-overlap 的实际验收。

872 个复用文件在本报告中的证据分类是：142 个有既有 normal + kernel 验收，
718 个是尚未验收的数值供应源码，12 个通用模块未在这里找到独立直接收据。
后 12 个不能因此标成失败或未编译；应核其既有私有缓存/导出签名，避免重复工作。
这些旧环境证据均不自动验证本次 P1 组合后的依赖对象。

**完整 `P2Winner9CompleteNumericalChecks.selected_checked` 仍未验收。**
还包括 674 个已有数值 pages、43 个余下 block aggregator 及完整 aggregator；
对应余下 10,770 行。原完整 terminal 与这次 P1 接线不能提前记绿。
父任务刚核过私有队列为空，不能假定其余页正在另处自动完成。

本次只准备接线、复用清单和静态核对；未启动 Lean、云端任务或全量数值页。

## Root 后续核对

GitHub REST 已确认 `a5a42f8f70418a7b2b8a378713911e829786ec8b` 公开存在，原先“发布未核实”的827个现成blob现可直接引用。完整原始清单保存在 `REUSE_EVIDENCE.tar.gz`，本目录 `SOURCE_UPDATE.json` 是累积的下一次云端精确安装清单。P2私有环境随后开始任务 `b7039f3f188b4b4ea9c214097bbdf401`，正在接续 block01；该进行中的范围不能提前记绿，也不能据此声称所有剩余页均已运行。
