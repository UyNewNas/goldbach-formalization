# upper_jensen F：真实 affine 薄层与原始索引 reserve

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT。六份 Lean 共 960 行，文本闭合且局部步骤完成。`goal_complete=false`、`task_complete=false`、`batch_target_complete=false`、`batch_target_source_complete=false`；`compiled=false`、`formal_credit=0`。没有编译、执行 checker、归档逐行判定、数值重放、额度检查或新子代理。E 及更早批次保持原字节冻结。

完整派发目标仍是：控制实际 archive canonical residual、extra-gate rejected owners 和 changed-parent difference regions 的真实 buffered proper-affine 薄层，取得 prescribed full adopted-bank trim reserve。本轮没有缩小这个目标并宣称完成：真实 invalid-history、pointwise-invalid 和改变祖先后的 gain 支付仍未闭合。

## 本轮实际消除的义务

先核对原始实际第五层 gate 的独立 affine 表，而不把 rejectedCost 小作为前提。每个原始 mask 保持相同 selected slots、全部 full-square gate 和补集 selected-square gate；tent 的 A/C 两侧都保留。每个真实 mesh cell 的 lower point 与实际点的 candidate 损失不超过 15h/2。原始 quantitative gate 定理只需 17h margin，而实际点的 32h margin 足够支付该损失。因此在原始 pointwiseSupport 内，真实 `gateCheck e=false` 必落在某个原始 tent-minus-gate affine strip，宽为 `2e+32h`。

原始非空 mask 的每条 allowed affine row 都有绝对值至少 1/2 的坐标系数。空 mask 的半门 A 侧确实退化，处理方式是证明其 pointwiseSupport 为空；没有把恒等于零的行冒充 proper wall。对实际五维 unit cube，在证明出的非零坐标上做 Fubini，单条 strip 的体积不超过 4δ，原始 22 条 gate pieces 的并不超过 88δ。这里的 22 是固定原始 gate 表大小，既不是 moving owner 数，也不是 child 数。

将 E 的真实 `gateRejectedDomain` 精确、互斥地拆成 support core 与 pointwise-invalid core。真实 M×volume 成本也精确相加。逐原始 `ArchiveIndex` 求和保持 292633 个源位置及重复行，每个位置仅付一次。support core 成本有真正推出的 rate：

`supportCoreBankCost S ≤ 88*(Σ i∈S M_i)*(2e+32h)`；若 `h≤e/20`，则不超过 `352*(Σ i∈S M_i)*e`。

随后直接处理 canonical 过滤，避免把 E 的 sufficient raw-wide mask5/6 check 误作必要条件。定义同一真实零缓冲 source 域

`unfilteredZeroDomain = ownerUnion(raw,0,decodedLabels)`。

实际 canonical omittedParent 恰为两个互斥区域：`fixedParent \ unfilteredZeroDomain`（真实 history-invalid）与 `unfilteredZeroDomain \ adoptedDomain(0)`（canonical owner 过滤损失）。对后者，从同一个 decoded cell 的实际 mesh 端点直接证明两端 `cells`、`selectedFifthCells` 和 `firstStop`。只需离两个真实 order wall 超过 2h、离原 rho-stop 超过 4e+h；rough activation 由真实 BASE 的 `lo2≥1` 及 `omega,h≤1/800` 支付，不删除 child 投影。实际被过滤部分因而落在三个 proper affine strips，统一宽 `4e+2h`，体积不超过 `12*(4e+2h)`。其源索引 M 成本在 `h≤e/20` 时不超过 `64*(Σ M_i)*e`。

最终真实 `licensedTrimCost` 精确拆为四个实际区域的源索引成本：history-invalid、canonical-filter、gate-support、gate-invalid。两项已证明薄层的成本合计不超过 `416*(Σ M_i)*e`，所以

`licensedTrimCost ≤ canonicalHistoryBankCost + invalidCoreBankCost + 416*(Σ M_i)*e`。

前两项是保留的真实残余，绝非待证总成本换名后的“小量假设”。upper_mesh 消费这一独立几何接口，将线性项加入同一旧 source B13 的连续 envelope，再选共同 e→q；本作者不重复该参数聚合。双方 F 源依赖单向：upper_mesh 可导入本批几何，本批不导入任何 upper_mesh F 文件。

## 改变祖先的独立控制

独立 E 原始 archive-bound `exponent5` 与 NEW common `exponent5` 使用同一真实 row/gate/candidate bank，但继承两个不同的第四层 seed。复用已有 finiteMax nonexpansiveness，证明实际

`|newExponent5-oldExponent5| ≤ parentExcess`。

实际新增的严格 LOG own-cube 查询区域因而位于旧 cap 图的 `parentExcess` 宽邻域，并且包含于已定义的 changedParentPrefixes。这是两个原本独立 finite maxima 的证明，不是给它们同一个候选定义。该旧 cap 图会随 source/prefix 改变；本轮没有把它声称为一个全局固定 proper affine wall，没有证明 parentExcess 随 e/mesh 消失，没有额外宣称 LOG 查询区域等同完整物理 prime query，也没有把旧 kernel B13 直接套到 NEW gain。

## 冻结源

统一 module/namespace 前缀为 `ImbalancedChen`，源均在本目录，目标安装位置为 `ImbalancedChen/<同名>.lean`。

| 源文件 | 行数 | 原始字节 SHA256 |
| --- | ---: | --- |
| P5ActualFifthGateStripLocalization.lean | 188 | f0798c805205a58eb17e946053c01c65e83348a452df852cd4bf6b6abf3a6096 |
| P5ActualFifthGateStripVolume.lean | 190 | cd0c039b578bc240cbe7116381a418dca72fe9a522fd3f9e4e26c40831d14450 |
| P5HistoricalRejectedCoreReserve.lean | 146 | 8ee5b0ba12bb3a33c5e5ac55f15640f36d485b7f6e3abe50946f797ec62ac37e |
| P5HistoricalChangedParentCapControl.lean | 88 | 454bb2b6a09debd9483d75f02c40e6989852fa08731cb6c86b7528de11c29ef6 |
| P5CanonicalOwnerFilterStrips.lean | 224 | e93566c4a7d2785d47c14b6a8e95ca65ebcc9721f3858c88d9f86eff1279f5ea |
| P5HistoricalCanonicalFilterReserve.lean | 124 | be7bdccb351817f25a319f0ba1aee47c0d3d9702c99b8ca23661a5442be78263 |

精确 source/import 路径、原字节 SHA、完整传递安装映射和 E freeze/review guards 见 REGISTRY。先安装 frozen E / 生产前驱，再按 Localization→Volume→RejectedCoreReserve、Volume→CanonicalOwnerFilterStrips→HistoricalCanonicalFilterReserve 的顺序；ChangedParentCapControl 独立依赖 E CommonAncestorExcess。没有实际执行安装。

## 仍未完成的完整目标

- 没有证明全 archive 的真实 history-invalid 区域或第五 pointwise-invalid 区域为空、体积可任意小，或 kernel 在这些区域不贡献。它们明确保留，没有靠 proper-wall 口号删除。
- 未以仅 named 两父格的 D all128 Jensen/reassembly 或 sufficient mask5/6 子族代替完整归档；也没有新的无关 Jensen proxy。完整源位置、mask、原始 half-open owner 与 clipping 都保持。
- 改变祖先的实际 excess 控制没有完成 chamber/source-form realization、properness、全局新旧 gain 比较和 prescribed reserve 支付。完整 NEW common parent 的差域不能仅由 cap 包含被宣布小。
- 本批几何 source theorem 不假设 upper_mesh F 的 typed all-BASE/key-injectivity 结论。该作者的独立源若被编译接受，可将既有 BASE 条件实例化为 full bank；其有限 decide 提案未在此执行。
- 原 typed archive 与独立 NPY 的完整字段形式真实性仍开放；SHA 不构成该等式证明。实际全局 numerical total、K、完整 W/adopted L5/L6、PP 及最终定理均未完成，且不被外置为 primitive。

原稿依据保持原始 causal old/new parent、非领先 pair gate、strict histories、proper-affine trimming 及先 finite policy 后 N 的量词。本轮展示的是实施进展，没有新的数学反例或原稿缺陷认定。审阅仅为源码逻辑审阅，不提供编译或内核信用。
