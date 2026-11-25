# Saving19 cell00 原始行算术接口：只读设计审查

## 结论与本轮边界

可以先为 cell00 建立真正的小有限数据接口，再用各 cell 的闭合证书组装原全称定理。输入应是**真实 Schema 的 `GeometryRow`、其原 `vertexIds` 顺序选择的九个八维有理坐标，以及对应 `MomentRecord`**。接口不需要其他十二个 cell 的 parse/shape/数值 guards，也不应导入尚未通过的 `Original28918` 或全量 `Archive`。

当前阻塞是模块边界，而不是缺少新的 determinant 或 moment 算法。`Original28918` 把纯有理计算、全 28,918 行闭合 guard 和后续连续线性映射放在同一 owner，且先导入全量 Archive。现有 `rowchecks` 候选只把两个 determinant 表达式改写为已存在的 `fastDet`；它仍请求一次完成全行 `decide`，不能作为 cell00 的独立入口。

本轮只读源、原回执及 manuscript，未创建 Lean 候选、未编译、未执行原件数值检查、未修改主仓或提交 P1。下述新模块名与签名是可实施设计，不是已经 elaborated 的接口。本轮没有给任何 RowDataChecks/FloorChecks 新增通过信用。

## 已核来源与可用性

| 原供应者 | 本次核查到的事实 | 使用边界 |
|---|---|---|
| `P2OriginalSaving19ArchiveSchema` | 实际 5923 B，SHA `b877c0c35ace12cd76e0ed737b3a4b1ff3917fa15c4cc32b961450ee4761418b`；项目源闭包 2 | 复用真实 `Geometry`、`GeometryRow`、`MomentRecord`、`Moments` 和原 decoder；新的 P1 owner 验收由 Root 另行处理 |
| `P2OriginalLogMomentQ96Checker` | 13091 B，SHA `49dddfb3fd522baed9938278d1711030ce204e0954c83758590b173e4197925c`；闭包仅 3，且在 bd718 facade 成功运行的真实依赖快照内 | 不必抽出/重新实现 evaluator，也不必重编 216 个分析供应者。消费时核当前 ready/context；依赖快照不是本次新 owner 的 full-owned 回执 |
| `P2Winner9RowArithmeticChecker.fastDet_eq` | donor 21102 B，SHA `bef1fb6c8358849f8a1cfdd320a30624235facad9ae1d7a285f1e773e1c14138`；当前实际 P1 来源闭包 52 | 泛型 ℚ 矩阵正确性可直接复用，但当前 P1 对象 readiness 尚待只读核查，不能引用旧 P2 验收代替 |
| `P2Winner9HomogeneousRecurrence` | 原 8441 B，SHA `4234d0ccf486c9d53f13bee20a2a48b1751edd572fcbbb7b6cf057169803591d`；闭包 1 | 现成 prefix table，不另实现 |
| `PrefixInterface` / `PrefixMoments` | 既有独立本地 normal/kernel 记录；项目闭包 2/3 | 这不是 P1 full-owned 信用。当前五 owner strict runner 已交付 Root，不能预先称该轮通过 |
| `HigherMomentsPrefix` | 2774 B，SHA `714b2e83b9e09d6881da59b8c63c287ae48fb22e7d74431b1da186c9fa427c34`；闭包 228，原 facade 224 供应者按旧真实回执复用 | 专用 `normalizedMoment_eq_encoded` 还须自身正式编译/审计；不再造一套 prefix/duplicateH 证明 |
| `Moment00Decoded` | 1986 B，SHA `8a269a5a9e0387deb15c7a145cf1a1bbdc94fe106babf84d20827c8c7ebb8151`；已有完整本地 parse+typed decode 记录，42 源闭包 | 只绑定真实 cell00 的 56 条记录，不证明任何 Q80/Q96 的数学正确性 |
| Geometry00 typed 终值 | manuscript agent 正构造 `Geometry00Decoding.concreteGeometry00`，当时最终 glue 尚未生成/通过 | 本报告只据稳定 Schema 设计输入，不假装该最终值或其 decode 证书已接受 |

fastDet readiness 的历史差别由 Root 本轮明确确认：以前调查的是旧 P2 115 源闭包，实际 P1 为 52 源，十项 source 不同；相同的 donor 文件不能转移旧 object/acceptance context。本次只读 import lexer 重算得到 52，无缺源。本地常用三个项目对象目录也没有这个 donor 对象；这不等价于云端 P1 没有对象。

Q96 实际旧依赖指纹来自：

`/workspace/p26-facade-retry-evidence/facade-retry1/ImbalancedChen.P2OriginalSaving19HigherMoments/normal/ImbalancedChen.P2OriginalSaving19HigherMoments/NORMAL_PASS.json`

源 commit 为 `bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3`；Q96 `.olean` 是 451584 B / `fe96b3ced4dbaa8e1de1a1465ce7c452a6b213bf9e6284b27881a7ca83546273`，`.trace` 是 3588 B / `ec729afe3afbc92310786534a7249795f9280cf45cd767c2180577b1ee37a9d3`。没有把这个旧 receipt 改成新 commit。

## 最小表示调整：保留原 FQN，拆开纯数据与全称验收

建议一个小 owner `P2OriginalSaving19RowNumerics`：

1. 从未通过的 `Original28918` 机械移出 `QPoint`、`comparisonQ`、`newQ`、`thirdQ`、`totalQ`、`gapQ`、`factorsQ`、`PhysicalQ` 及其 Decidable instance。**保留原 namespace `ImbalancedChen.P2OriginalSaving19Original28918`、原声明名、类型和定义体逐字。** `rawVertex` alias 与涉及 ℝ 的 `realPoint`、cast 定理留在原 owner。
2. 同一新文件可在独立 namespace `P2OriginalSaving19RowNumerics` 增加参数化的 `edgeOf`、`gapSumOf`、`massOf`、`meansOf`、`topsOf`、`computedMeanOf` 与 `RowDataChecksFor`。这些接受 `v : Fin 9 → QPoint`、`g : Archive.GeometryRow`，完全按现有表达式替换参数，不改系数、乘除顺序或数组字段。
3. 直接导入真实 Schema 与现有 Q96 checker。`RowDataChecksFor` 的规范仍使用 `Matrix.det`，因此小接口不必导入 fastDet donor 的 52 源闭包。按目前 import 图，该 owner 的项目闭包为 **6**：新 owner、Schema/SourceJson、Q96 checker 及其两个既有依赖；Mathlib 不计入项目模块数。
4. 后续原 `Original28918` 只改 import 与移出的定义所在位置，保留所有原 row-specific 定义、`RowDataGuard`、`RowDataChecks`、原全称定理陈述及后续 analytic 接口。用一个确切定义展开桥把 `RowDataChecksFor (rawVertex r) (rawGeometryRow r)` 与 `RowDataChecks r` 关联。设计上两边定义逐项相同，应只需要定义展开；**该桥此时尚未编译，不能登记为已证明。**

这个拆分不要求重编已经接受的 Q96 或 HigherMoments 供应者，不改其源。原 `Original28918` 本来仍未接受，不能用此次纯定义 owner 的验收给它整体补信用。匿名 Decidable instance 的最终环境名称、全部 generated/private 声明应由新 owner 自己完整审计；源迁移比较同时核原公开声明，不假定环境 inventory 自动相同。

Floor 可另设 `P2OriginalSaving19RowFloorChecks`，导入 `RowNumerics` 与原 `HigherMomentsPrefix`，定义 `momentsFor v g j k` 和 `FloorChecksFor v g m`。其 `momentsFor` 必须仍是原 `rationalMoment` 对原 gap 与 `1-factor/top` 的调用；prefix 只在证明中改写，不能把规范悄悄改成未经关联的另一张表。原 `FloorBinding.momentsQ`、`FloorChecks` 及所有后续声明保留，通过对应的定义展开桥消费小接口。

## 十项 RowDataChecks：没有可省的合取

记 `v : Fin 9 → QPoint`，`g : GeometryRow`，`E i j = v j.succ i - v 0 i`，`G = ∑ i, gapQ (v i)`，`V = g.physicalVolume`，`mass = V * g.meanGap`，`means j = g.gapWeightedMeans[j.val]!`，`tops j = g.factorMaxima[j.val]!`。规范必须完整保留：

| # | 原检查 |
|---|---|
| 1 | `E.det ≠ 0` |
| 2 | `∀ i : Fin 9, PhysicalQ (v i)`，含原全部顺序、边界与 cap 条件 |
| 3 | `0 < G` |
| 4 | `V = abs E.det / (8.factorial : ℚ)` |
| 5 | `g.meanGap = G / 9` |
| 6 | 每个 factor 的 mean 等于 `((∑ i, factorsQ (v i) j) + (∑ i, gapQ (v i) * factorsQ (v i) j) / G) / 10` |
| 7 | `∀ i j, factorsQ (v i) j ≤ tops j` |
| 8 | `∀ j, ∃ i : Fin 9, factorsQ (v i) j = tops j` |
| 9 | `g.jensenBound = oldEvaluator mass means` |
| 10 | `g.jensenFloorQ96 = oldFloorQ96 mass means` |

第 7 项不能替代第 8 项，第 4 项不能因为文档中保存了 physical volume 就跳过，第 2 项也不能由只验证 gap/factor 正性代替。

fastDet 只用于第 1、4 项，通过现成精确等式：

```lean
P2Winner9RowArithmeticChecker.fastDet_eq
  (A : Matrix (Fin 8) (Fin 8) ℚ) : fastDet A = A.det
```

应逐 row 产生精确 determinant 计算证书，再从该等式分别取得非零和 volume 等式。可以先按一 row / 一合取进行实际资源诊断，再组合 56 行；本报告不预判性能。现成 `withRowNumerics`、`BasicChecks`、`basic_sound` 是 Winner9 `RawRow`/其 geometry 约定的接口，**不是这十项 Saving19 合取的替身**。不要仅因已有这些名字就把 Schema 的新 record 强制转换后迁移结论。

## 五项 FloorChecks：同一原 rationalMoment 与双向 floor 约束

记 `M j k = rationalMoment (fun i => gapQ (v i)) (fun i => 1 - factorsQ (v i) j / tops j) k`，`m : MomentRecord`。完整规范为：

1. 每个 `j` 的 `M j 1 = 1 - means j / tops j`。
2. 每个 `j` 的原 `m.factorFloorsQ80[j.val]! = factorFloorQ80 (M j)`。
3. `m.oldFloorQ96 = g.jensenFloorQ96`。
4. `m.oldFloorQ96 = oldFloorQ96 mass means`。
5. `m.newFloorQ96 = max (oldFloorQ96 mass means) (newFloorQ96 mass means M)`。

第 3、4 项即使可由其他等式推导，也必须在合取组装中保留。第 5 项保持原 `max`；不能以 only-new、old+new 或一个下界替代。

实际性能路线直接用已有 `normalizedMoment_eq_encoded`：对每个 row 的九个 gap 与每个 factor 的九个 deviation，提供正整数公共分母和精确整数编码等式，然后一次前缀表求出 degree 0..6。这里“提供”等式指后续每个实际坐标的**闭合 Lean 证书**，不是 theorem 参数中留给用户的最终数据假设。

精确编码义务是 `s ≠ 0`、各 factor 的 `d ≠ 0`、每个原 gap 等于 `(gᵢ:ℚ)/s`、每个原 deviation 等于 `(zᵢ:ℚ)/d`，以及 `k ≤ 6`。`gᵢ,zᵢ : Nat` 不许可把负数截成零；如某坐标没有此非负编码，必须报真实失败，不能使用 `toNat` 默认行为。编码与计算可由 host 产生候选，但所有等式和 floor 最终必须由 Lean 证明。

`factorFloorQ80` 仍读取所有 k=2..6 及 k=1。需要一个有限次数的普通 congruence 改写，把已证 `M j k = normalizedMoment ... k` 用到这六个次数；不用重建或重新证明 prefix 算法。Q80 不能降成单侧 lower-bound 证书。若采用交叉乘法核 floor，设 `x = gapEvaluator (M j)`、原存储整数 `q`，必须证明两边：

`q * x.den ≤ x.num * 2^80` 和 `x.num * 2^80 < (q+1) * x.den`，

其中 `x.den` 用正整数分母嵌入 ℤ，符号处理保持原 `Int` 除法。或者直接证明原 `q = fixedNumerator 80 x`，再使用既有 `fixedNumerator_eq_floor`；这个精确等式不能改成 `q ≤ fixedNumerator ...`。Q96 同理，保持 96 位与原有 cubic evaluator，不做 Q96→Q80 换算。

## cell00 绑定：不允许隐藏 getD / 数组越界默认值

独立闭合数值 owner 使用真实 `Geometry00Decoding.concreteGeometry00` 与已经存在的 `Moment00Decoding.momentConcrete00`。九个点必须从这份 Geometry 的**原 row.vertexIds 顺序**取出，而不是从另一份宿主数学数组输入。对应 row/moment 用同一原 row index；不得排序重排后丢掉原 ID 对应。

最低前置证明是 cell00 版原 `CellShape` 与全 56 行版原 `RowShape`，不是新简化 shape：

- `dimension=8`、`physicalJacobian=1`、两份 rows size 都为 `originalRowCount 0 = 56`；vertices/vertexValues 的尺寸、每点 8 坐标与每个 saved factor array 10 项。
- 原 moments 的 cell ID、source witness、dimension、verticesPerSimplex、factorCount、logDegree=6、expDegree=3、`logDenominator=2^80`、`finalDenominator=2^96` 全部保持。
- 每行两个 simplexId 均等于该 index；九个 vertex IDs、Nodup、每个 ID 在该 Geometry 的 vertices 内；maxima、means、Q80 arrays 各 10 项。

这使现有 `!` 索引实际处于范围内，不能用它的默认数值凑出某个检查。最终 decode 的成功等式负责排除 `geometryParse.toOption.getD default` 的 fallback；shape 则另行排除内部数组索引的 fallback，两种义务互不代替。

可直接证明以 `Fin 56` 为索引的全部 `RowDataChecksFor` / `FloorChecksFor`。先单独留下它们的闭合结果，不导入原全称 Archive guards。等新 Core 和 packed map 有实际接受证据时，只用 index 0 的定义与已证 parse/decode，把 `geometry 0`、`moments 0` 改写成这两个 concrete value，再定义展开得到原 row-index `⟨0,i⟩` 对应的原谓词。该接头只需 cell00 的等式，不要求 `∀ c, geometry_parse_success c`。

原 `VertexValueGuard` 是另一条保存字段与原坐标函数相等的闭合义务，不在上述十合取之内；若同时做 cell00 的 28 个 saved vertex values，可作为独立小证书，但不能把它标成原 `∀ c` guard 已通过。原 all13 shape、all28918 rows、global old/new totals、pulling 与 endpoint 仍分别开放。

## 立即可推进的最小事项与尚待的门

Root 可先授权上述小 owner 的机械抽取与静态 source/FQN 比较，再只验收新增 owner；不必等其他十二份 parse，也不必重编 Q96、HigherMoments 或已有 generic geometry。这个 owner 自身不包含任意具体 row 的 PASS。

等 Geometry00 typed 终值与其 parse/decode 等式到位，先验 cell00 的实际 shape/ID 绑定，再测试一行的非 determinant 十合取部分，或在 fastDet donor 当前 readiness 确认后完成一整行。按原数据逐行/按项封装，成功证书组合成 56 行，而非再发起全 28,918 行 `decide`。这只是避免重新处理已经封存的证明；是否某个实际单项仍过重，必须看实际 normal/kernel 回执。

Floor 部分等待 `HigherMomentsPrefix` 本轮严格接受后直接消费；若其独立 owner 失败，保留该门，不降级成原数学结论作为 premise。当前设计不复制 fastDet，不引入新 polynomial/adjugate 算法，不扩张到全覆盖或新积分估计。

## 手稿范围

本次只读定位的 manuscript 是 `chen-imbalanced-semiprimes` commit `a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en/`：

- `numerical-appendix.tex` 177–196 给出有理多胞体、原不等式 vertex 检查、pulling 与 simplex barycentric moment law `num:simplex-moment`，并区分 positive saving 的可省略非负贡献。
- `argument.tex` 278–291 的选定第八层 saving 是 `4(M−R₆)/((R₆−S₈)(M−S₈)∏tᵢ)`，且明确没有 Chen quarter 或 ordering factorial。原有 `oldEvaluator` 中的 4 与几何 volume 的 8! 各有原义，不能互相删除或补乘。

手稿并未把 fastDet Gaussian 算法、prefix 表或 Newton/duplicate-node 计算写成独立 theorem。本设计把它们如实作为已有精确有限代数表示与原算术 evaluator 的复用；不称它们为稿外新估计，也不伪称手稿逐字给出了这些实现。Q80、exp3、Q96 的精确 evaluator 来源仍是项目原 producer 对照与既有 Q96 checker，不单凭稿件 metadata 证明其数值成立。

原件路径、hash、原谓词切片以及实际源闭包/旧对象引用见 `SOURCE_REVIEW.json`。该文件和本报告只记录本轮只读时点。
