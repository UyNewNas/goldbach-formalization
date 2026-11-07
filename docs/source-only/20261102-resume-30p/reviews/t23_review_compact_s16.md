# Task 23 — compact endpoint / saving16 独立源码复核

复核日期：2026-11-02。复核者：/root/t23_review_compact_s16。范围为 O+P 的 compact_total_endpoint、saving16_pulling_ownership、saving16_weak_face；先读 P/BRIEF，再读原稿 360–509、1354–1369。只读作者/冻结/生产源码；唯一 reviewer 写入为本报告。没有运行 Lean、lake、编译器、Git、数值 producer、有限 guard、数学重放或子代理；未重证、未修改作者文件。

仓库根 R = E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation。
以下 O、P、N、M、K、J 分别代表 R/docs/source-only/20261102-resume-30o、30p、30n、30m、30k、30j；L 代表 R/docs/source-only/20261102-certificates-l。原稿为 R/../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex，原始 SHA256 ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd，已独立重算。

## 逐任务结论

| 任务 | 限定源码结论 | 尚不能据此声称 |
| --- | --- | --- |
| compact_total_endpoint | SOURCE_REVIEW_PASS，适用于 O 两个消费者连同 P 的 namespace 修复副本。O 单独因限定名称缺失为 SOURCE_REVIEW_HOLD。 | 未确认任何 rfl/decide/norm_num 有限体为真；未认证完整 Python primitive-assertion/call-trace refinement；未闭合 current K、物理密度或 All22。 |
| saving16_pulling_ownership | SOURCE_REVIEW_PASS，适用于 O 三个局部几何/积分模块及 P 的单 token canonical-moment 修复。未采用该 P 替换的冻结 import 链仍 SOURCE_REVIEW_HOLD。 | 未认证有限档案、Q96 总和或资源可行性；未建立更强的完整 polytope/active-eight 穷尽；未关闭 common policy、signed compiler。 |
| saving16_weak_face | SOURCE_REVIEW_PASS，适用于 O 的 ordinary、w=0、原始全 family 一侧负部支付及 M 精确保留源组合；P 正确选择复用。 | 不是绝对 complement 为 o(1)，不是有限 N 精确非负，不是 positive-presieve、完整 compiler/reserve 或 All22 定理。 |

这些 PASS 是数学表达、依赖使用、量词、符号及已检查 API 的限定静态结论；完整传递链安装/验收继续 HOLD，特别保留 ownership 的 SOURCE_REVIEW_HOLD_OTHER_OBLIGATIONS_RETAINED。全部 compiled=false、kernel_verified=false、formal_credit=0；有限体 UNEVALUATED，broad targets OPEN。不能把“源码存在”与“成功 elaboration/kernel 验证”合并，也不能把已确认源码错误藏在“仅未编译”中。

## compact_total_endpoint

1. **完整原始表达确实出现。** O/compact_total_endpoint/P2OriginalCompactWholeFunctionalEndpoint.lean:85–95 明写
   4/(299/500) + originalFirstIntegral + actualExtendedThirdIdealFunctional
   等于固定源（同一首积分、同一完整原始 tail）加一次 compact。:110–120 的无参数最终接口使用 N fixed supplier 与 L actual forest bound；没有要求调用方提供全泛函、tail、compact、leaf 或历史 total 的目标等价假设。
   R/ImbalancedChen/P2FirstIntegralSeries.lean:38–43 将首积分定义为 (4/theta)∫从2至theta/rho−1 log(s−1)/s；R/ImbalancedChen/P4AOrdinaryRootFirstIntegral.lean:110–114 是其原 ordinary-root 精确字典。O:143–147 只消费该字典。

2. **Q80 原始 tail 未换成后来的 Tnew/P112。** R/ImbalancedChen/Part4ActualThirdFiniteDensityReserve.lean:39–65 是 compact 加原始 manuscript-tail 的精确分解；同文件:68–83 的 Tnew 结论没有被 O 调用。N/compact_fixed_bindings/P2OriginalCompactQ80FixedBindings.lean:193–206 使用原 dInteger 10、logI、I80 原运算顺序；:230–240 得到原 manuscript-tail 上界；:262–269 连同原首积分供应完整 fixed bound。L/compact_q80_encloser/P2OriginalCompactQ80Encloser.lean:431–448 保留 firstSeries20/21、Q80 rounding、tailInterval 与 fixedUpper 的原公式。共享 import 包含 later-tail 声明这一事实在 O/P 报告中披露，不能误写成它们未进入 import 图；但本证明路线未使用这些 later-tail 结果。compact 与 tail 各计一次，没有 quarter、factorial 或额外 correction。

3. **实际完整 forest，不是 heap 子集。** O WholeFunctionalEndpoint:53–72 在实际 originalRun.state.forest 上调用 L soundness，历史 candidate 供应 upperSum 与 2000021 完整 entries 长度。L/compact_run_certificate/P2OriginalCompactConcreteLoop.lean:133–149 的 orderedUpperCharges 来自 entries 的 map；:158–190 的历史 guard 同时检验 budget stop、2M splits、原整数 total、active heap occupancy 与 sourceAssertions 标志。1852040 是 heap 诊断，未充当积分域。L/compact_q80_encloser/P2OriginalCompactQ80CompleteSoundness.lean:76–82 从实际 entry/evaluator 与继承 geometry 推导积分界，:124–128 给完整 forest 界；没有遗漏 exact/empty 叶。

4. **有限 guard 没有被状态文字替代。** L/compact_run_certificate/P2OriginalCompactCachedEndpointCandidate.lean:20–30 是未执行的 closed rfl 与 cache 等价转移；O/compact_total_endpoint/P2OriginalCompactArchivedTotalCandidate.lean:26–44 是另一未执行 fixed-plus-compact 等式。O WholeFunctionalEndpoint:123–139 的小比较仅声明 archived upper < 681/100，并明确旧 6809/1000 在 archive upper 下方。原档 R/../goldbach-research/certify_extended_prefix.json:8–11 的 strict_upper_target_verified=false 与 upper_exact 一致；本审阅未重新计算其数值。不能报告 6.809 已证。

5. **确认并修复了实在的 namespace 错误。** 原 R/ImbalancedChen/Part4ActualThirdOriginalClosedSplitAggregation.lean:19–25 只有局部 open OriginalThirdFiniteReserveSourceOnly，没有 partition namespace 内的同名定义或 export。canonical def 在 R/ImbalancedChen/Part4ActualThirdFiniteDensityReserve.lean:33。L ConcreteLoop:153 却显式引用 OriginalThirdCompactPartitionSourceOnly.originalCompactThirdCorrection；K/compact_priority/P2OriginalPriorityForestLedger.lean:23、114–118 和 L CompleteSoundness:36、124–126 也依赖该 partition 名字。
   P/compact_total_endpoint/Part4ActualThirdOriginalClosedSplitAggregation.lean:27–32 只插入注释及透明 abbrev，直连 canonical def。删除该插入块可逐字节还原生产原文；原生产文件未变。该同 module 替换须在依赖模块之前 staging，后置 shim 不能修复已 elaborating 的 import。它改变源码 API，不增加积分或证明前提。原 source hash 27c9daffb5b47294f4f73b954f2512c12a77102655488d6b300726d581749a98；修复 hash 见下表。

### P2.4 四个黄叶的代码覆盖口径

按 R/../1_+_1.748_lean_proofs/main.md:35–38 的四项数学义务，含 P alias 的候选集合已经有无目标假设的具体源码；可以标记为“蓝：源码已实现、未编译/有限体未验”，不得绿。

| main 原叶 | 实际已在场的源码 |
| --- | --- |
| 实例化原始 adaptive ClosedCutTree | L ConcreteLoop:49–60 定义具体 runFuel/originalRun；K/compact_priority/P2OriginalPriorityForestLedger.lean:34–50 保存 literal originalAxis/originalMidpoint 子树，:100–103 构造 completeTree；L ConcreteLoop:199–218 实际 originalChargeTree 及 erase 绑定。 |
| 完整 charge 列表并保留原叶序 | K ForestLedger:75–110 的 entries 与 completeTree_closedLeaves；L ConcreteLoop:134–149 的完整 map/长度；:199–205 attachCharges；O WholeFunctionalEndpoint:53–61 消费实际历史 candidate 得到 2000021。 |
| 每个实际叶积分上界 | L CompleteSoundness:76–82 的 forestEntry_contains_integral 无外部叶 geometry；:124–128 全 forest；O WholeFunctionalEndpoint:65–80 实例化于 originalRun。 |
| 整数 charge 总和达到历史端点 | L CachedEndpointCandidate:23–30 closed finite candidate/transfer；:38–42 original_complete_chargeTree_viaCache_candidate；L ConcreteLoop:207–213 total identity；O:53–61 消费实际 total。 |

**另有确实未完全形式化的义务，不能伪装成已覆盖。** L Encloser:473–483 的 sourceAssertions 明说是部分 inventory；L ConcreteRun:202–212 的 sourceCheck 同样不声称所有 Python primitive guards；L CompleteSoundness:15–19 保留完整原 Python primitive-assertion/call-trace refinement。这比上表四项数学积分/charge 义务更强。若 P2.4 标题继续包含完整 Python 执行认证，应另保留/增加这一黄叶并保持 broad OPEN；不得把上表的蓝解释为原 producer 全断言已认证。这项缺口与“尚未编译”是不同原因。

## saving16_pulling_ownership

1. **归纳输入是 primitive incidence，不是重包目标。** O/saving16_pulling_ownership/P2OriginalSaving16PullingFaceInduction.lean:25–49 的 pull/Shape 只要求原 vertex-ID 的 pivot、支持 facet 交、child antichain 与递归形状。:91–113 由 gate 非负与零集 incidence 推出 omitted pivot 严格为正。:120–209 的两个分支分别构造 g(p)a−a(p)g 与 h(p)g−g(p)h；两侧符号及 proper separator witness 均由原顶点事实导出。没有 disjointness、coverage、integral 或 endpoint 假设。

2. **绑定到同一原档与 39741 行。** O PullingOwnership:35–55 解码 M 原 faceLedger；:66–107 的 pivot/children/originalPull/savedRows 和 closed Shape/ordered/Nodup guards 使用同一 archive。M/saving16_q96_endpoint/P2OriginalSaving16OriginalArchive.lean:43–50 是 IDs0..14 except7；:257–303 将原 facet incidence 绑到 96 实际 rows；:305–319 是逐 simplex Q96 floors 与39741计数的未执行证明体。
   原 author producer R/../goldbach-research/eighth-prefix-family-20261009-exact.py:59–68 保留按排序 maximal intersections、max(face) 的 recursion，:76–85 按 tri 顺序保存 vertex_ids，:89 保存 ledger。这支持 O 的有序绑定表达；独立 verifier :149 的无序集合比较单独不够。未解析/replay witness 来认证这些 guards。

3. **ownership 及积分方向正确。** O PullingOwnership:154–166 用上述归纳得到原 row separator；:172–218 先证明 evaluator 对应，再将顶点符号经真实 barycentric map 传到 rowSupport，交集落入 proper affine 零集。:220–226 是 within-cell AE pairwise 与 measurability。
   O OwnedIntegral:30–118 删除同 cell frontier/overlap 的零集，保留 AE 相同积分；:96–105 结合 M 原跨 cell separation 得到 pairwise disjoint；:129–148 用有限积分可加性、region inclusion 及非负 density 给出 sum of actual simplex integrals ≤ original source integral；:153–157 才消费 M 历史 Q96 bound。原稿1354–1356允许正 saving 使用合法子集，所以此方向不需要完整 cell coverage。全8维、factor4、mask129、cutoff53/13824与分子1222997719565324892497827/2^96未变。

4. **M19 是通用数学 API 使用，但实际 import 不能抹掉。** O PullingOwnership:3 导入整个 P2OriginalSaving19OwnedSource；:172–179 与:215 只调用其 eval/interpolate/affine-zero-volume。没有替换成 saving19 archive/endpoint，但其模块的 Original28918、parser、moments 与所有 closed guards 仍在实际 import 链中。P REPORT:21 及 REGISTRY 的 actual_import_caveat 已明确记录。有限 face parse、Shape、有序 rows/Nodup、M96行、determinants、Q96 aggregate 均 UNEVALUATED。

5. **继承 canonical-moment 的确定源码错误已单独处理。** 冻结文件
   R/docs/source-only/20261028-paper-first/cohort04/certificate/sources/2a511a7246bf9dd54d79649c171c34cf741ca4a0fbd10b2701ba42e6e615239e/P2Winner9ActualEightSimplexMoment.lean:123–127
   在 monomial_cons 后以反向 integral_const_mul rewrite，而下一行 change 要求将常数提到积分外。实际 Mathlib MeasureTheory/Integral/Bochner/Basic.lean:288–290 的公式方向是 integral(r*f)=r*integral(f)。这个旧 HOLD 是具体 proof-script/API 错误，不是单纯未编译。
   root 在原 task6 内授权 P/saving16_pulling_ownership/P2Winner9ActualEightSimplexMoment.lean:124 仅将该 rewrite 改正向。独立检查原文只有一次该反向 token，替换后全部字节与 P 副本一致；旧7420 bytes、原hash不变，新7416 bytes。签名、假设、结论及其余源码均不变。该确定 blocker 在选用 P 替换时已做源码修复；不因此解除其他 Q96、finite、M19、O 采纳、资源及 kernel HOLD。不能声称整条链已经闭合。

### saving16 的代码覆盖/改色边界

原 main:41 若含义是“原14档、39741合法单纯形的所需几何许可及其Q96 source积分下界”，O+P 修复已经有严格源码候选，可蓝。若继续声称“完整 cell 等于 candidate-facet polytope、active-eight 穷尽、完整 face-lattice coverage”，则这些更强结论并未由 O 三模块建立；宜将合法内部并集项单列蓝、较强完整性仍黄。P2.5 broad OPEN。

main:42 的完整共同旧策略/银行许可/旧收益保留、main:43 的实际 signed compiler/同一物理 rho 全包络仍黄。下面 weak-face 只能将“ordinary w=0 全 family 的一侧补项支付”单列为已有源码；它不是上述整个 compiler 叶的替代。

## saving16_weak_face

1. **同一 action、parent、原 admission mask。** O/saving16_weak_face/P2OriginalFourteenWholeFamilyLower.lean:27–37 的 fullSelectedFamilyGuard 与 R/ImbalancedChen/P2OriginalAscendingEighthCapDictionary.lean:505–521 一致，为单一 existential selector 加 CurrentParentGuard；不是逐标签重复加 gain。CurrentParentGuard 在 dictionary:261–262 是 H7<current 且 current≤R。O:40–65 保留精确 signed complement；inactive action 继承同一 actual parent，使 old−new 残余精确为零。没有假定 current=R。

2. **原 prime 子集先作逐点支付，符号正确。** O:84–95 从实际 admitted 条件推导 target-deleted box inclusion；:99–124 定义非负 D，并证明 −D≤C。:128–134 的 sourceGain 在全 CellGuard 上正；J/saving16_compiler/P2OriginalFourteenUniformResidual.lean:57–95 对全 CellGuard 与 CurrentParentGuard 给 uniform lower comparison，未要求 t∈strict region。其 N0 先于 cell/planes/t/current/P/y/cap。O:139–203 先用 gamma 逐点压住 max(0,−residual)，再乘非负权，并只在非负总和处扩大到实际 box mass；不会把 unrestricted signed cancellation 错用于子集。

3. **结论是一侧负部 o(1)，不是绝对值或有限非负。** O:207–215 得到任意 epsilon>0 后，统一 N0 对所有后续 even N、所有 OriginalData、cap、z≤cap 使 C>−epsilon。正 complement surplus 仍留在 C。它不需要把常量 identity 误当 proper wall，不会以 Lebesgue-null 墙抹去有限 prime histories，也不要求 strict source=weak selector。原稿453–458所强调 open inherit/equality regions 保留。

4. **量词和 normalization 未换序。** O:220–252 消费 M/saving16_retained_riemann/P2OriginalFourteenSignedRetainedLower.lean:362–380 的 epsilon/2 retained endpoint，及 M:173–193 精确 charge=source+complement 恒等式。最后的次序为 epsilon→n,e0→e,chi→m0,N0→data,N,cap,z，保留 data.e/data.chi/m/omega 条件、N^mu≤z≤cap、lambda6 data N、policy5 data N、literalPattern、ordinary presieve=0 与 log N/singularSeries N。M 原 trim estimate 此时更强，O:250 合法弱化到 epsilon/4。没有新增 negligible-complement、sign、retained convergence 或目标等价假设。

P 的报告/registry 正确选择复用而未另写同样消费者；复核指出的两个 metadata 行号（M sourceFrontierAt_eq_admitted_sum=91；TupleOwnership normalized_charge_eq_admitted_sum=60）已由作者修正。

## 静态 API、哈希与未解除的边界

独立读到的本地 API 签名与调用一致：Lean 4.33.0-rc1 source Init/Data/List/Pairwise.lean:331–333 的 List.getElem_inj（h₀/h₁），Init/Data/Array/Lemmas.lean:4454–4456、4473–4474；Mathlib MeasureTheory/Integral/Bochner/Set.lean:136–141 integral_iUnion_fintype、:740–743 setIntegral_mono_set；MeasureTheory/Measure/AEDisjoint.lean:28–29；Data/Fintype/BigOperators.lean:145–150 生成的 sum_sigma；Algebra/BigOperators/Group/Finset/Defs.lean:674–676 生成的 sum_neg_distrib，O weak-face:116 的反向用法正确。Mathlib 的读取根是 //wsl.localhost/Debian/home/slava/codex-lean-ve/native-packages/mathlib/Mathlib；这不认证运行时版本或任何完整 import closure。

直接 ImbalancedChen imports 均查到对应源模块；发现的两个确定接口/方向缺陷已在本报告分别列出。对新/复用 scoped Lean 的静态扫描未见 sorry、admit、axiom、unsafe、native_decide。hash 只认证字节，不认证任何 archive 数学。ownership registry 的29项复用/critical-source/原14 fixture raw pins，weak-face registry 的登记源，以及 compact registry 的 sources/reused_sources，复算未发现缺失或hash不符；不冒称认证全部传递依赖。

| 复核 Lean | SHA256 |
| --- | --- |
| O compact / P2OriginalCompactArchivedTotalCandidate.lean | 8bfa1d0d1521b12795c3214dc78b5c22a9757b01943e7c3c6577ddb065b31f9a |
| O compact / P2OriginalCompactWholeFunctionalEndpoint.lean | 606cb2277c031d440cc379aedd4029a8f386f9925d93ccfcb77cf37557d80185 |
| P compact / Part4ActualThirdOriginalClosedSplitAggregation.lean | 0eb47009874916d49c577f3aeacc45c35f603e5480410cbdf078b3653302b30e |
| O ownership / P2OriginalSaving16PullingFaceInduction.lean | 8be89f68730007dd2a59f5afde0ed532deeb65f05a9f3115159cf0176b0d26b8 |
| O ownership / P2OriginalSaving16PullingOwnership.lean | a291896dc3ee13823ae1fe18326dbbe07583aa04e3304dacfc9353c814fa5ecb |
| O ownership / P2OriginalSaving16OwnedIntegral.lean | 5aa1cfb7b3080e4bc3ff0152901ac234d7451da4788fee364a7d5bcc1aeb8047 |
| P ownership / P2Winner9ActualEightSimplexMoment.lean | 6c50d79875f94da6d89d6485fa553647496a2cdaf661ebe138e07fe0782f6834 |
| O weak_face / P2OriginalFourteenWholeFamilyLower.lean | d030b9ee6c9606d16409708fc029fa16f8ca0f4e6fc995a171e56442ec1da38c |

最终 P 元数据也已读到稳定版本（raw SHA256）：

| 元数据 | SHA256 |
| --- | --- |
| P compact REPORT.md | 09acb8add7a233b9a8481f12c806707e5b9561542722d8c823969d8b52724dcd |
| P compact REGISTRY.json | af809efddc20a479f8cabe5e46518e5f014e78c2fb1430a444886a36fa0a0648 |
| P ownership REPORT.md | 61377e0bf08cc5929693d9523e6f8be541757430b1291fe4b918c17605ce10f5 |
| P ownership REGISTRY.json | bde78c6d43f6ad1cd5a3bda3443865a0c12c16e3d600be5059b75b2a112f24e8 |
| P weak_face REPORT.md | 24edaa76e3ba66826a186c5534f5251fe5a48217309c7f6f427e500f6a0a23ed |
| P weak_face REGISTRY.json | a4d815c17f4815ef7bc7d194bb759f9b1e06b487251d188758a05c7b6b30e36d |

最终边界：这次解决/确认的是源码层的明确局部义务及两处最小继承 API 修复；既没有把 closed finite candidates 当成已执行事实，也没有因“未编译”否认已经在场的具体代码。原始生产执行完整对应、强全cell覆盖、共同策略其余部分、positive-presieve/signed compiler、两笔 reserve、current K、分布与最终 counting 均未被本报告关闭。
