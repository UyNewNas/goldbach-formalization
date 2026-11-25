# 原有限 Λ/log 字典的源码分层

本目录记录原 source-only 有限字典的声明迁移，**没有新增 Lean 接受或证明信用**。9 条原声明的名称、statement 与 proof bytes 完全保留，没有把结论改为假设。没有运行 Lean、Lake、kernel checker 或云任务，也没有改变缓存。

## 已执行的精确变化

新增 `ImbalancedChen.Part3FiniteLambdaOverLogCore`，literal imports 只有 `Mathlib`，项目 imports 为空。它在原 namespace `ImbalancedChen.Part3.FiniteLambdaOverLogDictionary` 中唯一拥有以下 9 条原声明：

| 原声明 | 在当前完整 AllK／Family 中的作用 |
|---|---|
| `lambdaOverLog` | 原 Λ/log 系数定义；直接引用 |
| `lambdaOverLog_zero` | 保留原字典 API；当前完整 AllK／Family 没有具名引用 |
| `lambdaOverLog_one` | 保留原字典 API；当前完整 AllK／Family 没有具名引用 |
| `lambdaOverLog_prime` | 原素数系数等于一；直接引用 |
| `lambdaOverLog_prime_pow` | 原真素数幂系数为 `1/e`；经 `proper_term_has_prime_exponent` 间接引用 |
| `lambdaOverLog_off_prime_powers` | 原非素数幂系数为零；直接引用 |
| `lambdaOverLog_pointwise_split` | 保留原点态字典 API |
| `finite_lambdaOverLog_split` | 保留原精确有限和恒等式，含一次自然数计数与原系数 |
| `proper_term_has_prime_exponent` | 原真素数幂坐标及精确 `1/e` 证书；直接引用 |

旧 canonical `Part3FiniteLambdaOverLogDictionary` 仅删除这 9 个声明的精确原区间，并增加 `import ImbalancedChen.Part3FiniteLambdaOverLogCore`。其余原文，包括原有 imports、namespace、comments 和末尾 `sorted_prime_chart_one_slot_lambda_split`，全部保留。旧 provider 因而仍通过 import 提供原 9 条声明，并保留 sorted 专用定理；不会与 Core 重复定义。

`Part3AllKLambdaChartCorrection` 只将第一个旧 Finite import 替换为 Core 与已有 `Part3ActualOriginalProperPowerChartBridge` 两个 imports。后一个 import 恢复过去经完整 Finite 间接获得的 integer-word、proper-chart 与 box 接口。其余全部原字节，包括其他 imports、全部定义、恒等式、假设与证明体，保留。

`Part3AllKFamilyLambdaCorrectionBound` 整份文件原字节不变。完整 Family 的估计、量词顺序、整数 bank 幅度推导及所有假设都保留；没有制造替代的 ReserveData，也没有把估计变成输入。

## 为什么这个边界可以切开重链

旧 Finite 的前 9 条声明只使用 Mathlib 的自然数、素数幂、von Mangoldt、实数对数、复数和有限和接口。末尾的 sorted 专用定理才使用 `sortedWord`、`carrierCap` 和 `sortedWord_prime_data`，从而要求 `P5SortedPlainPPExactPrimeCharts → Typed/Sorted → W16` 链。

完整 AllK 与完整 Family 对该有限字典的直接具名引用只有 `lambdaOverLog`、`lambdaOverLog_prime`、`lambdaOverLog_off_prime_powers`、`proper_term_has_prime_exponent`。两者都不引用末尾 sorted 专用定理。

当前 `P5OriginalPrimeAllGroupHBDiscrepancy` 仍使用原 `lambdaWord`、`roughWord`、`properChartWords` 和完整 `licensed_atlas_all_k_prime_plus_proper`，所有整数 licence、eta/psi/rough 因子、载体与 signed kernel 保留。完整 AllGroup 最后一条 all-rank theorem 仍需要原 `AdmissibleAllRankIntegerGeometricFamily`。`SourceWordDictionary` 自身没有具名调用 AllK/Family 的声明，但其原 Family import 链仍然保留；本次没有为进一步缩小闭包而改变它。

## 来源与保护范围

原 Finite、AllK、Family 均用提交 `d20acdf13882e17d97833064f5e7c54f3192b03c` 的精确 Git 字节绑定。操作前的 P1 保存查询 `job_785a8a6b4b4c4949975aef3e52d7229e` 中，Finite 与 AllK 的源码 SHA 均匹配，而 `.olean`、`.trace`、`.olean.private`、`.olean.server` 均为空。此前有限范围的发布记录核查也没有找到这两个 owner 的接受 receipt；这不是全局未编译的断言。

root 明确授权对这两个 source-only canonical provider 做本次重构。这里没有迁移一个已可靠接受的对象，也没有拿旧失败或 source-only 状态兑换新接受。后续 Core／AllK 与 receiver 上的编译和验收仍须按各自阶段完成。

`preimages/` 保存三份原全文；`postimages/` 保存 Core、旧 Finite 的互补 postimage、AllK import-only postimage。`ADOPTION_MANIFEST.json` 记录每条声明的原／新行区间、UTF-8 byte 区间、SHA256，完整 source blobs，唯一 owner census，以及 P1 来源观察。

## 阶段图与现存工作边界

`STATIC_GRAPH_REVIEW.json` 明确区分保留的旧 386 项阶段和下一阶段：原 5 个目标加 Core 共 6 个目标，其当前项目源码闭包为 168 项。额外 45 项中，3 项仍在新闭包：

- `P5AdmissibleAllRankIntegerGeometricFamily`
- `Part3AllKLambdaChartCorrection`
- `Part3AllKFamilyLambdaCorrectionBound`

其余 42 项脱离这组目标的项目 import 闭包，源码和已有工作均保留。它们包含仍有数学用途的旧完整 Finite provider 及 sorted/W16 链；离开当前闭包不代表这些模块无用、未接受或从未有人处理。

旧 386 项 metadata 没有在这里被改写，完整原字节保留在 [source386-before-finite-layering 快照](../p15-original-atlas-proper-power/snapshots/source386-before-finite-layering/SOURCE_CLOSURE.json)。本目录的 graph review 绑定该历史快照；对应 owner 会显式建立下一阶段 168 项／6 目标的清单与执行范围。项目源码图计数不等于 native 依赖计数或已完成的编译量。

## 只读静态核验

在仓库根目录执行：

```bash
python docs/p1/20261125/p15-finite-lambda-source-layering/verify_layering.py
```

脚本核对原 Git 字节、9 条声明精确迁移、唯一 canonical source owner、互补 postimages、完整 AllK/Family 保留、保存的 source-only 观察和实际 import 图。它只读本地文件和 Git 对象，不执行 Lean，不提供 elaboration、kernel 或新 owner 接受结论。
