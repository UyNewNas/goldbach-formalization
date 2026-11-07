# t26 — policy / common history / two reserves 独立源码复核

日期：2026-11-02。范围：t12 `adopted87_policy`、t21 `all22_common_history`、t22 `actual_two_reserves` 的 O/P 材料。仅静态读源码、检索声明及 metadata/SHA256；未运行 Lean、lake、编译器、CI、数值重放或 finite guard。未改任何作者文件。本文的 **PASS 仅指所列窄源码实现与原目标的静态对应**，不是 elaboration/kernel 验收；全部 `compiled=false, kernel_verified=false, formal_credit=0`。

路径缩写：`O/` = `docs/source-only/20261102-resume-30o/`，`P/` = `docs/source-only/20261102-resume-30p/`，仓库根为 `E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation`。所有 `文件:行` 指本次实际读到的源行。

**总判定：HOLD。** O/P 的有限恒等式、实际系数构造、原 H3 rows 转换、rank3 restoration 与固定 proper-wall 局部支付有可复用的窄 PASS；它们没有闭合原稿的全 87 分支、真实四正项减 22 saving 共同源账，也没有支付两笔完整实际误差。作者已收到此边界反馈。

## 原稿基线及必须保留的含义

`../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` SHA256 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`，与 BRIEF 一致。

| 原稿落点 | 本次验收条件 |
|---|---|
| 280–297 | 冻结同一有限 causal policy；物理 level 决定 density/residual。辅助 support cover 不改变物理 cap 或整数系数；full/selected-complement squares 和短/继承分支不可遗漏。 |
| 371–374、435–449 | 30+15+13+29 个原 eighth 域；逐级 new-minus-current-parent，改积分界仅为 replacement/increment；实际 parent 残差在 (1,3)，saving 不带 Chen quarter 或排序 factorial。 |
| 453–482 | pre-N finite causal partition；open inherit/equality regions 保留；偶 outer、奇 inner 后同一 beta-attached rho；presieve projection 为上界；支持膨胀小于 1/1000。 |
| 484–509 | density 与 compiler 各花独立的 u，严格小于其各自 allowance，然后才用 E+2u<K 得同一物理 rho 的密度界。 |
| 1327–1337、1354–1369 | 四个正项减 22 个真实 saving；完整第三 tail 替换一次；同域加强只计新旧差；负成本须全域覆盖。有限算术/几何 guard 未运行不得称验收。 |

辅助原文 `paper/source/modules/global-positive-upper-completion-20261010.txt:55–127,183–242` 还明确：rank5 可恢复旧排除节点；first-failure 指旧 sufficient minorant 的失败，不是真树 first exit；seed/family cell11 不能再计；`C_policy` 先于 fine atom count；eta/omega/J0/tau 等均在 N 前固定。

## O：实际已实现的窄结果

### adopted87_policy — 窄 PASS，完整原 policy HOLD

- **PASS：原 fourth 字节载体与 fifth archive 的具体输入绑定。** `O/adopted87_policy/P5OriginalFourthFifthSourceInputs.lean:26–49,56–91` 将原 17-byte rows 的 payload 读成透明 byte literal，构造无 empty fallback 的解码，并给 wire-row/source reconstruction。`:93–113` 定义原 row 集合及 `integerGeometryAccept` 过滤，推出其几何；`:118–143` 的 `heldData` 接实际 fifth indexed-owner archive。payload 实测 62,885,159 bytes，SHA256 `561f5dc9ff2f6d64ba739de830511f6f68bf1f7be0c724655a8435c7edb914da`。`:62–63` 的 `by decide` 长度证明未求值；metadata hash 不替代该 guard 的 kernel 检查。
- **HOLD：它不是 complete adopted87 supplier。** 同文件 `:16–19,115–117` 如实声明 sixth 仍为 eleven-cell held stage、eighth 不是已绑定的 original87。底层 `docs/source-only/20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedConstructor.lean:102–125` 仍只把 eleven sixth family 接入 `lambda6`，再调用旧 `familyPolicy`；`:57–68` fallback 仍用理想 `v`，不是完成的 buffered finite fallback bank。
- **HOLD 的具体来源，不是缺一个泛型 ceiling lemma。** `.lake/proof-continuation/source-reviews/drafts/20261028-Coefficient-Sol6-EighthMask-Phase3/P5OriginalAdoptedEighthPhysicalMasks.lean:91–96` 只划分 `Fin 87` 的索引区间。`:101–116` 的 `PhysicalRows` 把 actual-parent bound、first/third/fifth/seventh histories、full squares、selected-complement squares 装为字段；`:189–198` 的 guard 是 `∃ i : Fin 87, PhysicalRows ...` 后 `Classical.choose` cap。尚未由原各 affine-cell rows 推出这些字段、原 cell 的分离/覆盖及真实 current-parent 关系。guard 中写入目标性质不等于实现了原 87 域。
- **短/继承分支仍不能丢弃。** `docs/source-only/20261102-resume-30m/actual_pp_physical_support/P4BActualEighthPhysicalSupport.lean:152–188,193–228,233–248` 只针对 descending17/ascending19 两个已有 local actions；最后结论仍分成 `length≤8`、继承 `lambda6` 上界、selected branch `<N^(599/1000)` 三个分支。这不是所有原 87 分支的 global physical support，也不是原 8 个 selected-complement squares 的实际源供应。

### all22_common_history — 有实际 telescope，完整 all22 HOLD

- **PASS：真实 current-frontier 的 second/third 拆分。** `O/all22_common_history/P4AOriginalCausalHistory.lean:39–65` 定义 secondStage 并证明 common third 是在其 rank3 之后 splice；`:77–97` 给 rank3 本身的实际新 admission/旧节点恢复规则；`:99–122` 对 small third 保留完整旧 signed continuation。`:126–168` 的 `secondChange` 使用旧 rank2 frontier，`thirdChange` 使用 **secondStage 当前 rank3 frontier**，不是把旧 rank3 frontier 当作全部来源。incoming sign、mass、remaining carrier 和 List multiplicity 均未改。
- **PASS：原 fourth/fifth signed gain 保持。** 同文件 `:181–198,212–249,285–333` 用实际 fifth archive 在 `t1>mu` 的 separation 和 `t1≤mu` 的政策相等，推出对任意 terminal test 的完整 signed gain 保持，未从 signed monotonicity 偷换结论。`:338–367` 接入真实 `attachedLeafTest`/`roughPrimeUniverse`，同一 `OriginalData`、N、cap、w、z、L、G 的系数总和得到旧源、second/third correction、原 fourth/fifth gain 及真实 sixth/eighth `sourceChange`。`:371–373` 只是同源 bound replacement 的 ring identity，不能另算 saving。
- **PASS：确有一个 pre-N 的窄 schedule。** `O/all22_common_history/P4AOriginalCommonArchiveSchedule.lean:38–57,68–96` 选同一 `e,chi=e/20,q,omega`，`:97–125` 将 whole fourteen selected-family lower 与旧 history 的两项 resolution 取共同 `q=max ms mh+1`，然后 `∀N≥N0`；第四/第五 signed gains 的保持是结论，不是输入。其 schedule 正确读祖先自身 prefix label，没有在该定理中由 N 反选 q。
- **HOLD：schedule 的范围确实只到 fourteen + 已接 fourth/fifth。** `CommonArchiveSchedule:69–70` 仍输入 fourth rows/licence/geometry；O/adopted87 的具体绑定可作为这些输入复用，故这里不是声称原 fourth payload 在仓库缺失。该 schedule 自身未完成的关键仍是 `:14–18` 所述 finite buffered fallback bank 和 full87。`CausalHistory:352` 的 sixth/eighth 仍是未关联的 `sourceChange`，并没有等于 22 个 manuscript saving，也未导出它们的正性/各 quoted endpoint。rank3 恢复规则的局部定理还不自动给 catalog5 的完整 signed source 与 ordinary residual 的解析对接。
- **HOLD：四个实际正项与 22 份实际 saving 的 endpoint 总账。** 生产 `ImbalancedChen/P4AAll22ActualCompactPositiveBinding.lean:37–55` 确实定义真实四正项并接 ordinary root；但 `:71–78` 其余 saving 仍是 quoted gain list，`:91–95` 显式保留 first-integral/compact excess。`ImbalancedChen/P4AAll22OriginalKLedger.lean:104–129` 只实际替换 tail 与 slot5 coarse integral；`:68–84` 的 E+2u<K 是精确标量算术，不是实际 common-policy density。没有把 `twoSupplierLedger` 或 `fourSupplierLedger` 误称 complete all22。

### actual_two_reserves — 同一 rho 构造/误差恒等式 PASS，两笔支付 HOLD

- **PASS：实际 parity compiler，而非把误差预算当输入。** `O/actual_two_reserves/P4AUpperTaggedParityCompiler.lean:31–58` 对真实 rough squarefree carrier，用 whole support 的 even outer/odd inner tests 定义系数；`:122–141` 从定义推出 raw≤compiled；`:151–172` 给同一 tagged cell 内的 raw witness，`:187–209` 给 mixed cell 两种相反 support 决策。`:212–239,252–287` 证明 literal reciprocal-totient coefficient norm **恰等于** `changedMass`、≤`crossingMass`，且 signed rough density 增量也是该非负 mass。没有额外 factor2。
- **PASS：同一 beta pair 的具体 physical rho。** `O/actual_two_reserves/P4AUpperTaggedBetaAttachment.lean:24–31` 定义一个 rho；`:57–84` 证明 enlarged-carrier raw attachment 与旧 actualSmallRoughRho/其 density 相同；`:87–106,108–129,131–172` 分别提供包括零与负整数的 majorant、唯一 small/rough 分解、绝对值≤1、squarefree/coprime target。它们不能被读成 exponent support `<N^theta_*`。
- **PASS：same-rho error identity/slope supplier。** `BetaAttachment:176–207` 将生产实际 small-weight slope 直接用于这一 rho，右侧为 `(B/(nu*epsilon^2))*changedMass*(C_N/log N)`，B 先于系数、tag、fine width/atom count。`O/actual_two_reserves/P4ACommonPolicyTaggedCompiler.lean:31–60,62–106` 将 tag、held raw 与 compiled rho 绑定到同一 `OriginalData`；`:99–106` 是旧 raw physical function 的字面相等，不是相似命名。
- **PASS：presieve correction 未被抹掉。** `CommonPolicyTaggedCompiler:110–119` 精确保留 `-p4aActualPresieveCorrection`；`:123–144` 的 stopFirstOdd 例子表明它不能普遍当成0。生产 `ImbalancedChen/P4AHistoricalPhysicalSavingsReserve.lean:43–69` 已给完整 raw = Euler×presieved + correction 且 correction≥0，故用于 **单个上界 projection** 时方向有利；对 old-new saving，`:115–180` 仍保留 correction 差，不能逐项自行消去。
- **HOLD：actual finite-density allowance 没支付。** `ImbalancedChen/P4AAll22OriginalKLedger.lean:139–153,176–187` 已把 actual finite-third approximation 的 `u_d/4` 单列；其余 density errors 只剩 `3u_d/4`。O 没有实际 complete common-policy tail/wall/cap convergence 的总误差上界，未得 `<u_d`。
- **HOLD：compiler allowance 没支付。** `coefficient_error_eq_changedMass` 是精确对象识别，不是 changed/crossing mass 小性。`ImbalancedChen/ActualCompilerDensityReserve.lean:196–214` 的旧 budget 接口仍以 raw-density bound 和 literal coefficient-error budget 为输入；O 用真实 changedMass 取代不透明表达式，却没有证明冻结 `C_policy` 后的 wall/crossing 估计、eta/omega/J0/tau 的共同 pre-N 选择，也没有支持膨胀 `<1/1000`。不能把一次 arbitrary `epsilon` 或小权重 β slope 当成两笔 u 已付。

## P 候选复核

### t12 adopted87_policy — 原 12 个 H3 cells 的源码语义转换 PASS

新数学源码为 `P/adopted87_policy/P4AOriginalFirstFailureH3SourceSemantics.lean`。`P4AOriginalFirstFailureH3Literal.lean` 是冻结 `docs/source-only/20261028-paper-first/cohort04/upper/sources/97ac074bbef4df78305f7664c542824c480371081ee6585f70c52e9edcade141/20261028-Upper-Sol6-Phase10-FirstFailureH3Literal12.txt` 的完整 Lean 段机械提取，旧 `.txt:3–5` 有非 Lean 的孤立 hash/prose 行，不能直接作为 import。独立静态比较确认从首个 import 到 namespace-closing end 的文本逐字不变，两者 literal row 数均为1188；该提取不是新定义原域或重证旧政策。

- `SourceSemantics:41–65,71–87` 明确原99行分为37个公共严格 slack 与62个 old-mask plane；只省原恒等的 winning mask9，`:89–108` 证明枚举覆盖所有1..63且不含9。`:112–138` 是全部99行的双向转换；没有用 sampling/中心点代替全域 membership。
- `:140–163,165–210,212–270` 将8个 full-square row、5个未选 slot `{0,2,4,5,6}` 与其余实际历史/old-plane row 逐项装回 `StrictH3`，并证逆向。`sourceAffineGuard_iff_StrictH3` 的输入只是原 literal affine-domain membership，不再把相同的 selected-square/history 语义作为额外前提。
- `:274–288` 从原行推出真实 `M8<v(selected138)` 和 `M8<153/256`；`:293–321` 将全8 full squares 与全部5 selected-complement squares 接入已有 physical integer square conversion。仍为同一 N、tuple、M8；辅助 support cover 没有替换物理 cap。
- `:326–350` 对已有 `ActualH3Guard`/`h3Exponent` 做精确字典，仅消掉重复 `StrictH3` conjunct；保留 `H7<lambda6(actual ancestor)` 及 `lambda6≤R6` 两个尚未供应的真实父条件。没有更换 policy、rho 或 rough universe。
- **边界 HOLD：** 这只覆盖 first-failure H3 的12个源域。其实际 sixth parent、其他75个域、full87 source separation/dispatch、所有短/继承分支支持及后续 causal approximation 均未实现。`:71–87` 的 `fin_cases/norm_num/ring` 全1188行恒等式 proof bodies 未执行；源码 PASS 不表示这些 guard 或 Lean API 已经通过。

`SOURCE_RECEIPT.json` 另记录原 release ZIP navigation 的1188行 row-name/coefficient-string 与12组 left masks 文本匹配；本复核独立确认了冻结原 `.txt` SHA及完整提取文本，未执行该档案的几何、体积、积分或 proof guards。t12 的最终 REPORT/REGISTRY 如实区分机械复用与新语义转换，直接 import 路径、两个新 Lean SHA 与本次读取一致，full_target_status=OPEN，compiled/kernel_verified=false。

### t21 all22_common_history — 实际 before-test restoration 与有限源码重组 PASS

- `P/all22_common_history/P4AOriginalRankThreeRestorationSource.lean:35–41,45–108` 构造只执行原 rank1/2 决策的 beforeThird 枚举政策，于第三节点入选测试**之前**列出候选。`signed_difference_before_third` 用该真实 frontier 的 `admittedTest fresh−admittedTest old` 表达完整差，未以旧 rank3 admission 为前提排除恢复项。该 enumeration helper 不取代原 sieve policy。
- `:110–176` 证明 activeSecond 在第三祖先后的所有后代保持、level 始终由同一第二祖先给出；inactive 分支完整继承。`:183–248` 把每个真实 candidate 分成 old-admitted 的 new−old continuation 与 old-rejected/new-admitted 的**完整** new continuation，保持旧 occurrence、sign、mass、remaining carrier 和任意 terminal test。支持的旧 admission→新 admission 由真实 cap 比较推出，未使用 signed monotonicity。
- `:252–264` small-third source 项精确为零。`:268–312` 对真实 prime carrier 用 `actualPrimeFrontier_geometry` 供应 rank3/sign/mass/remaining carrier，复用 `firstExitRetainedPolynomial_frozenParity_frontier_density`，把恢复项识别为 `−s.mass * actualSmallRosserMinusDensity(..., Q/prod pre)`。实际 LOWER residual 的符号与第3奇数秩一致，不含 Chen quarter/factorial；旧 rejection 留在 restoration mask，未被当成 old residual 对象。
- `:318–389` 进一步给 old-admitted 半边的实际 lower-density difference：`s.mass*(Minus(old rawLevel/prod pre)−Minus(new Q/prod pre))`。原 `frozenLevel_eq_rpow_seed`、真实 old3 admission 与 `old_third_continuation` 供应旧 coarse level；新 admission 由 cap 比较推出。与恢复半边合在一起是完整的有限 second-action residual 字典，未用“两个无关 sieve bound 相减”。
- `P/all22_common_history/P4AOriginalFiniteSignedHistoryRefinement.lean:34–78` 的有限 `nativeTests d` 无 N 参数，各 test 读 own-rank ancestor；rank 尚未到达为 `none` 而不是删除。其第三 mesh owner 使用全 `Finset.univ`，保留 unselected/false/equality/inherit 标签。`:81–107` 的 `refinedSum_eq` 对 **List occurrence** 分组，不把状态转成 Finset 丢 multiplicity。`:120–166,194–214` 只将上述实际 restoration 分项和 O 的 new-minus-current-parent telescope 用同一 bank 重组，仍为同一 physical rho、cap、w、z、L、G。
- **HOLD：** `one_preN_native_refinement`（`:170–175`）是 pre-N **标签银行及精确 source reindexing**，不是 all22/buffered finite policy existence；没有选择够小的各 causal margin，也没有恢复 catalog5 endpoint prime-pair integral 的完整解析等式或误差支付。原 finite coarse cap/disabled history 误差、sixth/eighth source 与全部22 saving 的关联仍缺。不能把 generic exact regrouping 再计成一个 saving 或完整共同 approximation。
- 本复核发现并由作者修复两处 Lean 表达/API 问题：未知 list 的递归 `evenListLength` 不能仅靠 `simp [length=3]` 得 false，现复用已有 `signedTreeCoefficient_evenListLength_eq_negOnePow`；`signedTest_one_eq_polynomial` 原在 `P5OriginalCommonFourthSourceLedger`，现明确 open。作者也移除了 `refinedSum_eq` 中可能在 simp 关掉目标后继续执行的多余 rfl。均为表达/API 类问题，未运行编译器验证。

### t22 actual_two_reserves — 同一 rho 的固定 proper-wall 局部支付 PASS

- `P/actual_two_reserves/P4AUpperTaggedMixedWallPayment.lean:28–81` 将实际 rough support 绑定 canonical `FirstExitValidSelection`，并让被求和的点 d 自身得到同 tagged-cell 的相反 selection。没有只定位另一个 witness 却误给 d 的质量收费。
- `:84–144` 定义 O upper compiler 的真正 changed/mixed **canonical-wall** mass，literal norm 等于 changedWallMass，≤mixedWallMass，后者≤真实 prime strip mass×**完整** residual Euler mass。复用的是 `docs/source-only/20261028-resume-30e/transfer_trace/P2CanonicalWallFullResidualPayment.lean:113–194` 的 policy-independent 原算术载体和 prefix/tail totient 分解；没有借用 lower coefficient 的估计冒充 upper compiler。
- `MixedWallPayment:149–173` 对固定 proper affine wall family `L,c`（前提仅 `L_i≠0`）、正 omega<v、给定 eta，先选 δ>0，再 N0，最终统一于所有 cap/keep/tag/tau；没有 fine atom count 因子。`:177–198` 靠唯一 small/rough decomposition 证明 wall-carrier rho 在其支持处正是 O global rho 的同一 entry。`:215–260` 接已有实际 beta slopes，将这同一 rho 的 wall 编译改变量严格付为 `<eta*(C_N/log N)`，eta 是任意正局部 allowance，不是调用者给定的 target error bound。
- `P/actual_two_reserves/P4AUpperTaggedContinuationAccounting.lean:22–46,50–119` 精确拆 `changedMass=Mplus+Mminus` 和 `physical compiled−physical raw = Dplus*Mplus + Dminus*Mminus`。负 rough 改动是 −1→0，故差为 **+beta-minus density**；没有偷假设 beta-minus density 非负或以 absolute norm 代替该 signed identity。
- `ContinuationAccounting:123–140` 的完整有限恒等式为 `compiled = full raw + beta error + signed changed terms − actual presieve correction`；`:145–187` 直接消耗生产 `ActualNormalizedRhoError.lean:124–173` 的真正 beta reserve supplier，使同一个 epsilon、N0 统一于 keep/tag/tau，仍显示未付的 changed terms 和 favorable correction；`:191–211` 固定回 O 的 same `OriginalData`、heldRetain 和 historicalTag。没有另构方便的 rho。
- **HOLD：** 尚无实际 held/original policy 的所有 mixed cells 被一组固定 proper canonical-prefix walls/tails 覆盖的证明，未给 tau→δ 统一关系，也未处理所有 open equality/inherit regions、rank/support ceiling 与原87 branch 表。上述局部支付不能推出总 changedMass 小，尤其不能把任意 proper-wall family 当成 complete covering 输入来宣称 compiler u 已付。beta 已可任意小不等于完整 compiler reserve；density `u_d/4` 仍已使用，剩余 `3u_d/4` 与 compiler `u_c` 的全局分配/共同 N 前选择均 HOLD。

## 汇总边界

| 义务 | 源码判定 |
|---|---|
| 实际 original fourth/fifth 输入、窄 pre-N schedule、current-parent telescope | PASS（仅所列 held/fourteen/第四第五范围） |
| P 原12个H3行→语义；before-test rank3 restoration；同源 occurrence reindex | PASS（局部接口，未编译） |
| same `OriginalData` 的 raw/compiled physical rho 与 literal compiler norm | PASS（构造、恒等式、majorant 层） |
| 固定 proper canonical-prefix walls 上 same-rho 编译误差严格支付 | PASS（尚未供应总 mixed-cell 覆盖） |
| 原 87 affine domains →实际 branches/parents；所有短/继承/selected 支持 | HOLD |
| 共同 raw source = 实际四正项−22 saving，原 endpoint 与无重复计算 | HOLD |
| density `u_d/4+remaining< u_d` 与 compiler `<u_c` 分开支付 | HOLD |
| 同一最终 rho 的 `<(K+o(1))*C_N/log N` 及 `<N^(599/1000)` 支持 | HOLD |

缺口分类：已有 telescope/字面误差对象主要是 Lean 表达与有限代数层；原87 row→physical histories/squares、causal finite fallback、all22 source association 是实际尚缺的内部数学供应；冻结 policy 后 mixed-wall 估计、finite density reserve 和支持膨胀控制尚未实现。源码未给出足以认定原稿矛盾的反例，故不把“未实现”升级为“原稿错误”。P1.4.history/gates/integral、P3.6.same_rho_PP、P4A.4.actual_all22、P4A.5.hdensity、P4B.4.hUpper 的 broad nodes 均保持 OPEN。

## 静态元数据

本轮 O 六份和 P 六份 Lean 的 admission 检索未命中 `sorry`、`admit`、`axiom`、`unsafe` 或 `native_decide`。`by decide`/finite guard 存在不代表已求值；原 provenance include 宏亦未执行。三目录 O 当时无最终 REPORT/REGISTRY，引用 prior registry 仅作溯源，不增加证明信用。

P 三目录的最终 REPORT/REGISTRY 已读；共六份 Lean 的 SHA256 和直接 import 清单均与最终文件独立比对一致。三份 registry 均保留 full target OPEN、compiled/kernel_verified=false、formal_credit=0，分别将 H3 原行语义、有限 signed source 分解及 proper-wall 局部支付与其尚缺的完整供应分开列出。t21 最终 refinement 文件为217行，以下记录其删去多余 rfl 后的最终 hash。

| 文件 | SHA256 |
|---|---|
| `O/adopted87_policy/P5OriginalFourthFifthSourceInputs.lean` | `a869d1264bdd6444be8346342a2d0806b7673902a5958503173e1d8806c8beb8` |
| `O/all22_common_history/P4AOriginalCausalHistory.lean` | `bd5ac9207e4be0e119f3acfc3b5e15fe35b3f9f29a8d9a114658ac9350e21877` |
| `O/all22_common_history/P4AOriginalCommonArchiveSchedule.lean` | `686cbb4a435819025bf43446259b695a5ea95fa11485aeb90eefb2ebd8c79024` |
| `O/actual_two_reserves/P4AUpperTaggedParityCompiler.lean` | `1f89fa7972687bfb7ba3905e483e3ab85a7248f79844718b539827170d5d965c` |
| `O/actual_two_reserves/P4AUpperTaggedBetaAttachment.lean` | `3c678f8655a7d00d4fd18924980f343b3fb83d3dc1e21959bfb89cbc92798037` |
| `O/actual_two_reserves/P4ACommonPolicyTaggedCompiler.lean` | `297ffc4ea894e50ed24fcaf78d54bb4399b353f8108f51798b2869b61598724b` |
| `P/adopted87_policy/P4AOriginalFirstFailureH3Literal.lean` | `2154c6be4be885c15ec779f232616e3506add090d6370f758bb4c6b1ecc91f9f` |
| `P/adopted87_policy/P4AOriginalFirstFailureH3SourceSemantics.lean` | `744b58311fb693e0751d7c7d18bf8f60c01111b3f6e5026244cc36da0c208664` |
| `P/all22_common_history/P4AOriginalRankThreeRestorationSource.lean` | `21f70edccf8e29bbeef411ed8dd9b2bb7e464bbd764bf5856a95abefd160242a` |
| `P/all22_common_history/P4AOriginalFiniteSignedHistoryRefinement.lean` | `ccc877b63fa01551c0ba937acea7542c6944a170014cdc59c08a50c8610757f7` |
| `P/actual_two_reserves/P4AUpperTaggedMixedWallPayment.lean` | `f35e43631e01a6ca56188d8f71a5c0d66806ede6e151e16a5dfa8818fd078cc6` |
| `P/actual_two_reserves/P4AUpperTaggedContinuationAccounting.lean` | `66fccf58bbd090023c999ffe4f6ab49860f21aac569a943a682897b14c577337` |
