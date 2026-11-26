# P1.5 当前状态与继续工作（AE 实际 partial + collector 后续快照）

**21 个 formal targets 中已有 16 个接受；ReserveBranches normal 失败，AtlasRoughPrime
未启动，另三个 proper-power owner 继续 P3 HOLD。整体 P1.5 仍未闭合。**
本后续快照在真实 AE 两次结果与 actual metadata 上补入实际成功的 read-only collector。
仍不声称下一次 probe 成功、AF 发布或新的 owner 接受已经发生。原冻结快照保留不改。

AE：`ca13f51c65d37870b96a6b1eb32ac30e92019fa2`；AD source anchor：
`e91af3a5c407bdeea243af7dd3c4248949d83e9b`。

## 21 个目标的实际状态

| 模块（ImbalancedChen. 前缀省略） | 当前状态 | Owned / public | 原接受提交 |
| --- | --- | ---: | --- |
| P1OriginalSingletonProperPower | P3 HOLD | — | — |
| P1OriginalHistoricalProperPower | P3 HOLD | — | — |
| P5IndependentPrimeSourceWordDictionary | 历史接受保留 | 15 / 15 | `2779eb7b` |
| P5OriginalPrimeAllGroupHBDiscrepancy | 历史接受保留 | 15 / 15 | `2779eb7b` |
| P1OriginalSingletonSmoothLicence | 历史接受保留 | 11 / 11 | `6484b348` |
| P1OriginalSingletonAtlasProperPower | P3 HOLD | — | — |
| P5OriginalSingletonLowerTrimPaid | AE run0 接受；run1 复用 | 10 / 10 | `ca13f51c` |
| P1OriginalSingletonAtlasTrim | AE run1 接受；批次部分失败 | 11 / 9 | `ca13f51c` |
| P1OriginalSingletonSupportData | 历史接受保留 | — | `3d292e4c` |
| P1OriginalSingletonCutoffData | 历史接受保留 | 16 / 8 | `237b5c5c` |
| P5OriginalPrimeAtlasReserveBranches | AE run1 normal 失败 | — | — |
| P1OriginalSingletonAtlasRoughPrime | 未启动 | — | — |
| P5OriginalPrimeChartHBWitnesses | 历史接受保留 | 7 / 7 | `080d4178` |
| P5LicensedOriginalIntegerProfile | 历史接受保留 | 33 / 33 | `54c6e727` |
| P5PerGroupIntegerHBAtlasPushforward | 历史接受保留 | 68 / 58 | `dc1e74ee` |
| P5AdmissibleAllRankIntegerGeometricFamily | 历史接受保留 | 42 / 42 | `44520167` |
| Part3AllKLambdaChartCorrection | 历史接受保留 | 34 / 31 | `44520167` |
| Part3AllKFamilyLambdaCorrectionBound | 历史接受保留 | 27 / 27 | `18e41c4a` |
| P5OriginalPrimeEndpointLogPayment | 历史接受保留 | 24 / 24 | `f6e63d1b` |
| P5OriginalSharpPrimeSynthesis | 历史接受保留 | 28 / 28 | `9f2013ad` |
| P5PrimeDivisorMeanCorrection | 历史接受保留 | 22 / 22 | `ae373b97` |

Support 的 AE historical-prior row 没有声明 owned/public 数量，本表保留空值；
不从声明头数或其他 owner 推断数量。所有历史 prior 均保留原提交与回执身份。

## AE 原始执行与证据

LowerTrim 首次任务 `job_d3c60cd1867242fab3195258062e2290` 成功，接受 **10/10**，
audit `e45153f0bb3e3268967a`，normal/kernel/full-owned 均通过且只有标准 axioms。
它保持原 `runs/attempt-00000` 和成功 final stock；原闭包119/118、三个历史 supplier。

later4 任务 `job_698d39e25f9d4800a912dc27a0bfe84b` exit1：LowerTrim 复用原接受，
AtlasTrim 首次接受 **11 owned / 9 public**，audit `25adbe91b10ca6f615bb`，
normal/kernel/full-owned 通过且只有标准 axioms；随后 ReserveBranches normal 失败，
AtlasRoughPrime 未启动。原 later4 闭包157/153、27 historical suppliers，**没有组
final stock**。AtlasTrim 的接受来自这个 partial run1，不能重写为成功整批。

`ACTUAL_AE_METADATA.json` 为13520 bytes，SHA256
`6145eb2f0ebb8e1d6d3d0968e711d93478705bf01f44c08906eaa9ea74955fed`。
两个 capture 去除包装字段后重建的 RESULT，以及重建 WORKER，均已逐字指纹命中
actual metadata；ledger 记录原路径和 pins，未将带包装的 capture 冒充原 raw。
LowerTrim 在 later4 的 acceptance binding 与首次完全相同。

实际 collector 已成功，联合只读 scope153/151，own closures 分别119和153。
它不得改变原 run0 的119 scope 或原 partial run1 的157 scope，也不生成新接受。

## 下一轮正式工作与 AG 结构

ReserveBranches 当前只确认一处 line43 的 rpow rewrite normal 错误；其修补、成功
probe、AF 发布仍未绑定。下一轮只在真实成功证据就绪后发布 AF，再配置 AG。

AG 采用原 U 双owner的三个 fixed generic 函数：登记 LowerTrim@AE 和 AtlasTrim@AE，
保留14个旧 prior。64个旧函数中62个逐字保留，仅 `source_manifest` / `preflight`
增分类和分派，新添三函数；其他359源、imports、303 fixed和19 P3 HOLD不变。
原两个 owner 的结果、六回执、context、source+5/full21 与接受 run 必须分别保全。

**新选集的真实闭包已缩小，不能沿用旧157范围：**

| 下一选集 | Sources | Dependencies | Watch | Historical suppliers |
| --- | ---: | ---: | ---: | ---: |
| 首 ReserveBranches | 140 | 139 | 152 | 21 |
| 后两项 ReserveBranches + AtlasRoughPrime | 144 | 142 | 152 | 24 |

两个选集均不含 LowerTrim 或 AtlasTrim 的模块闭包；它们继续保留历史登记，但按照
原机制，不在实际 active closure 时不强加 live owner/audit 复查。新双prior自身的
隔离验证与实际 collector scope仍需保持119/153以及joint153/151。
详见 `AG_NEXT_ENTRYPOINT_PLAN.json`；AF commit及next-acceptance均明确未绑定。

## 数学与依赖边界仍然开放

三个 proper-power owner 继续被19项 unaccepted P3 dependencies阻断，既有P3
read-only device HOLD未解除。Ledger逐项保存精确模块名和source hash；源码存在
或历史对象不能单独推出当前接受。它与FixedM缺源是两项不同阻断。

`Part3TwoLongFixedMRectangularCore` 的准确原字节仍缺失，期望SHA256为
`2be2789f712144fc7411849340caafe2c5caa2dc6de9ad96125590a9e9374b8b`。
本轮未再次搜索缺源或重复P3诊断，也没有把别的实现代作原供应者。

Literal historical medium 的同源字典和 full signed bound仍未交付。必须保持同一
物理N、Q/rho、历史S/R、eight/six、selector/omission与smoothing kap；source-only
residual减去literal historyMedium的界不等于估计medium本身，也不能将带外视为零。

`P5OriginalSharpPrime.original_sharp_prime_logAccuracy_of_smooth_and_actual_lowerTrim`
仍显式使用`hSmoothSignedPP`前提。Conditional theorem的formal接受不支付这个解析
前提；需要原物理/历史参数下的真正supplier。

Outer remaining Type-I payment、exact-medium residual、AD的trim log-accuracy
预算相加修正均保持 **SOURCE ONLY**，未计作本次或原owner验收。旧AA稿与AD修正
分开记录路径/hash。Same-kap额外门`kap < kappa/(4*(1+kappa))`是实际应用限制，
不是任意预选kap的事实；actual counts仍为`u * singularNormalization`。相关proper-
power依赖继续HOLD。即便剩余两个可运行target后来均通过，以上边界仍不会自动闭合。

本快照只整理真实结果与元数据；没有云、Git、Lean执行，没有重跑旧测试，也未修改
生产源码。当前来源与新文件指纹见`LEDGER_INPUTS.json`。

## 本次补入的实际 collector

`job_59ed19c844224b6482c5b5af45a84235` exit0，46.023462秒。实际读取153/151，
重验25个当前历史supplier，并保全八个原证据树、10个extra evidence、21个target
源槽与441个target artifact槽。没有normal/kernel命令、没有再次执行final stock，
也没有生成新Lean接受。16/21的实际接受计数不变。

READ：45763 bytes / `b630616bbcfe7e1b073ff0046efa7c606f4319ca66442286db7a7898d611075f`。
LowerTrim public：11615 bytes / `fac4e9665c918179f4f72fae8fc009a5ccb912f4674bc8d56dbf256906470681`。
AtlasTrim public：7359 bytes / `18201db1ec50df50b023d894abaae0f4675650f4c3a9e8efe619b344c9ada325`。

完整后续数据在`STATUS_LEDGER_AFTER_COLLECTOR.json`；原`STATUS_LEDGER.json`与
`CONTINUE_WORK.md`仍作为此前实际partial、collector未绑定时的冻结历史保留。
