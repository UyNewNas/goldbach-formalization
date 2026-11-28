# P2.6 最终端点与原稿接线：只读审计

日期：2026-11-28。只读基线为 `/workspace/p26-proof-continuation-20261127` 的既有源和已发布1577检查点；原稿为 `/workspace/chen-imbalanced-semiprimes` 的既有 release。没有读取当前8h运行attempt的输出，没有执行Lean/lake/MCP/seed/packager/owned/G，没有修改provider、源码、看板或旧报告。本目录仅新增本报告。

**`original_full_snapshot_verified:false` 原样保留。`formal_credit_added:0`、`P2_6_complete:false`。** 本审计确认源码陈述、原稿出处和有理数算术，不认证尚未接受的末端证明。

## 1. 找到了精确目标；“19”是saving的序号

原稿 slot19 的可读目标是

`357686854 / 10^14 = 0.00000357686854`。

更强的原始28918行完整Q96替换总界是

`q19 = 283388722705335806564439 / 2^96`，其中 `2^96 = 79228162514264337593543950336`。

因此不是“0.19”“19%”，也不是任意选取的容差或Cell06的单胞常数。准确现有接口如下（全名均在 `ImbalancedChen` 下）：

| 层次 | 实际文件、lemma与行号 | 精确结论/边界 |
|---|---|---|
| 原13胞数值积分端点 | `P2OriginalSaving19OwnedIntegral.lean:149`, `original_endpoint_le_selectedSaving` | 无参数：`(283388722705335806564439 : ℝ)/(2:ℝ)^96 ≤ selectedSaving` |
| 原稿可读下界 | `P2OriginalSaving19ActualEndpoint.lean:83`, `paper_saving_le_selectedSaving` | 无参数：`(357686854:ℝ)/(10:ℝ)^14 ≤ selectedSaving` |
| 唯一纯数值比较 | 同文件`:80`, `paper_saving_le_q19` | `(357686854:ℝ)/(10:ℝ)^14 ≤ q19`，源码体 `norm_num [q19]` |
| Q96常量定义 | 同文件`:33`, `q19` | 上述完整Q96总界，未把old/new两次加计 |
| 原13胞到Full87来源的识别 | 同文件`:40,46,51` | `original_cell_integral`, `selectedSaving_eq_original_cell_sum`, `original_q96_le_original_cell_sum` |
| 对Full87积分和的比较 | 同文件`:58,76` | `selectedSaving_le_full_source`, `original_q96_le_full_source`；额外源积分仅以非负性纳入 |
| 普通实际密度差导出 | 同文件`:89`, `exists_ordinary_q96_gain` | 保留原全部先于N的共同选择、原sixth/new-union policy和q19−eps差界 |
| 正预筛实际密度导出 | 同文件`:118`, `exists_positive_presieve_q96_gain` | 保留nu/eps/betaMax、beta范围、19/96、原ordinary sixth parent和同一完整new tree |

上述OwnedIntegral/ActualEndpoint的数值末端当前**不在已发布1577 accepted catalog**，不能把它们的闭合源码体当作已接受定理。本地精确目标和原稿常数已找到；不是“缺少目标常数”。

## 2. 原稿直接出处和原始密度语义

原稿仓库当前HEAD正是文档所钉的 `a988cba584d803ae2856a0de50efb582f4f3dd6a`。只读Git检查显示下列两个release文件无工作树变更，Git tree给出：

- `paper/release-20261106/en/numerical-appendix.tex`，blob `428e5fb4cd92b01b72119d795b8eeb01c67e3ccd`。
- `paper/release-20261106/en/argument.tex`，blob `90234d94460f1d7d59982635d7bf54c9b19250da`。

`numerical-appendix.tex:235–245` 明定每个整数表项是 `G_j ≥ m_j 10^-14`；`:270` 原文为 `19 & Eighth-rank third-coordinate moments & 357686854`。`:177–195` 给有理顶点、原不等式验证和simplex-moment公式（label `num:simplex-moment`在188），并明确正saving可以在证明省去贡献非负后省略内片。这里不是把负成本上界的“整域覆盖”条件套到正saving下界。

`argument.tex:278–291`（label `eq:current-eighth-saving`在286）给

`4(M−R6) / ((R6−S8)(M−S8)∏_{i=1}^8 t_i)`，

说明R6是较大的保守parent、没有Chen quarter或ordering factorial，cutoff为 `t8 > 53/13824`，全部full/selected-complement square条件仍在。`:213–218` 明定successive replacements、保留原祖先决策，以及 `30+15+13+29=87` 个原域。

这与现 `P2OriginalThirdMinorantLogDictionary.lean:9–32,44–60` 的原物理字典一致：`R=A(t1+t4)`，`M=A(t2+t4+t8)−10^-6`，十因子 `(R−S8,M−S8,t1,...,t8)`，mask138。这里不能把R直接当真实current sixth cap相等；原残差比较的history/cap条件必须由实际策略来源供给。

本结论还与 `docs/verification/20261125-p26/history/REPORT.md:78–83` 的原稿pin及 `docs/source-only/20261102-resume-30q/saving19_instance/REPORT.md` 的既有实例审计相互印证。未调用外部服务或访问无关资料。

## 3. 全13胞闭合后，数值积分端如何接回现有源码

当前已接受的 `SourceMeasure.selectedSaving_eq_sum_cells`（`:243–247`）为

```lean
selectedSaving = ∑ i : Fin 13, ∫ t in cell i, conservativeDensity t
```

其中 `selectedSource := ⋃ i : Fin 13, cell i`（`:225`），`selectedSaving`是该原域的真实积分（`:227`）；不是一个可自由代换的实数。原域通过 `OriginalAscendingThirteenCellOwnership.cell` 和原exported97 gates固定。

全13原胞分别接受其真实 `A_i / 2^96 ≤ ∫cell_i density` 后，还要在Lean内核接受：

1. 原13个实际保存分子之和等于 **283388722705335806564439**；不能以host求和或文档数字替代这条绑定。
2. 以真实13胞界相加，并用上述已接受的exact additivity，得到同一 `q19 ≤ selectedSaving`。
3. 用 `paper_saving_le_q19` 得原稿表19界；若消费的是full rational enclosure，应继续用q19，不能只把略小的paper小数塞回q19原接口。

已有旧全量源码并非“尚未写出的family”：`Original28918FloorBinding.lean:60,81` 已具体构造 `algebraicMomentRow`/`fullMomentRow`；`:106–125` 写有 `saved_new_total` 与 `original_floor_total`；`OwnedIntegral.lean:124,136,141,149` 已写从实际simplex积分和、原保存Q96到selectedSaving的无caller-endpoint组合。这些都是现存**未接受源码路线**，并非本任务新证明。

但当前逐胞拆分成果没有自动替换该旧单体路线：旧OwnedIntegral仍import旧 `PullingOwnership` 和 `Original28918FloorBinding`，后者仍经旧全量Archive。新的Cell00/01/05 SourceAttachment定理各自成立，不会因同为13胞数据便让旧Archive、旧28918闭合guards或 `saved_new_total`自动接受。将全部分拆证明明确汇总、绑定同一原数据和总分子，并接回上述公共末端类型，是全13胞完成后仍需完成的接线。可以复用既有接口/证明体，不能假设所需结论作为参数。

Cell06的单胞候选 `8004390162743539242/2^96`只是 `A_6`，不等于q19；当前未计入已接受的三胞下界。

## 4. 导出不是只有积分：ActualEndpoint的完整实际policy陈述

`ActualEndpoint.lean:35–54` 先用原ownership join证明

`cellIntegral (.ascendingPair i) = ∫cell_i conservativeDensity`，

再把原13胞和识别为 `selectedSaving`；`:58–77`用其它Cell积分非负把它纳入Full87源和。该识别的方向、index `.ascendingPair i` 和原literal source dictionary不可省略。

普通导出 `exists_ordinary_q96_gain` 的现有准确statement骨架为（namespace/open简写与原文件相同）：

```lean
theorem exists_ordinary_q96_gain (eps : ℝ) (heps : 0 < eps) :
  ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
  ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
  ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1 / 100 →
  ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
  ∀ (cap : ℕ) (z : ℝ), (N : ℝ)^mu ≤ z → z ≤ cap →
    q19 - eps <
      normalize N (raw (sixthPolicy n e q om (N : ℝ)) N cap 0 z -
        raw (policy (width r) n e q om (N : ℝ)) N cap 0 z)
```

正预筛导出 `exists_positive_presieve_q96_gain`（`:118–134`）额外要求 `nu,eps,betaMax>0`，先选同一个

`0<beta<1/8`、`beta<betaMax`、`beta^2≤(19/96)/nu`，

再保持同一 `r,n,e,q,om,N` 的先后次序；对 `cap ≥ N^(19/96)` 令 `w=N^(nu beta^2)`、`z=N^(19/96)`、`L=N^(nu beta)`，结论包含 `1<w≤z` 以及

`normalize N (physical (policy (width r) n e q om N) N cap w z L) < normalize N (raw (sixthPolicy n e q om N) N cap 0 z) − q19 + eps`。

这两个定理的caller没有提供所需gain/积分下界；源码体分别复用 `P4AOriginalFull87UnionActualGain.exists_ordinary_source_gain`（`:245`）和 `exists_positive_presieve_source_gain`（`:310`）。它们依赖实际共同历史、有限实现、signed/absolute density与原complete policy链。这些suppliers和ActualEndpoint尚不在published1577 accepted catalog，所以即便全13数值积分端通过，仍不能直接标全P2.6导出完成。

还有一个明确的root导出缺口：对当前repo生产 `.lean` 的精确import搜索，**未找到任何 `import ImbalancedChen.P2OriginalSaving19ActualEndpoint`**；仅该文件自身namespace出现该名。`UncompiledContinuation.lean`虽import若干quoted budget/slot结构，也没有导入该ActualEndpoint。故当前有末端模块源码，但没有观察到它被现生产聚合入口消费。未来应显式选择/接受该模块并接入实际导出入口，不能把namespace存在当成已公开主定理。

## 5. 哪些不是完整原稿端点

| 已有内容 | 为什么不能替代q19/原稿导出 |
|---|---|
| `MomentFloorConsumer.original_family_floor_sum_le_integral_sum`（`:273–278`） | 参数是任意 `rows : OriginalRowIndex → MomentRow`；自身不提供真实原28918 family或source-cell归属。旧全量candidate确已把它实例化，不能一边忽略实例，一边把consumer当已接受endpoint。 |
| `SourceMeasure.selectedSaving_eq_sum_cells`与普适非负性 | 正确且已接受，但只供加法和零下界，不供所需数值总saving。 |
| `P4ASlot19ActualParentIntegral` | `conservativeSaving_le_actualParentSaving`（`:41`）保留任意D/parent及hRows/hHistory/hCap/integrability；`:72`仍给含真实deficit的ledger比较，未给原13胞q19 enclosure。该文件不在published1577 catalog。 |
| `P4ASlot19ChargedFrontier.slot19_physical_frontier_charge`（`:138`） | 已接受的结构charge可以保留同rho signed mass，但文件`:16–17`明确guard不等于原13历史域，也未供原moment floor。不能由结构恒等式跳过当前13胞任务。 |
| `P4AAll22OriginalKLedger.finalFourGains 0`（`:26`）和已接受预算恒等式 | q19在这里是字面quoted槽值，类型/算术成功不等于该字面值由实际积分获得。文件`:8–17`明确两supplier ledger不认证全部actual integral functional。 |
| `P2OriginalCertificateBudgetAssembly.component_error_bound`（`:73–85`） | 接受caller给每个component的有向误差不等式，未自行证明19号实际enclosure；纯预算不能供缺失的目标分量。 |
| `Full87ArchivedIntegralRows.paidNumerical` | 同时含slots16/17/19等其它已引用数值，并经未接受的实际archive链；不能把更大和作为本P2.6已闭合替代品。 |

完整原稿all22/currentK/最终c还需要其它槽、同policy历史、有限count/mean/compiler、原reserves和总账接线。P2.6的本地q19原积分端点不能单独承担整篇稿件所有这些义务；相反，不能把“剩余全局工作”误写成q19数值常数本身没定义。

## 6. 未完成“洞”的准确位置和性质

三个数值终端文件ActualEndpoint/OwnedIntegral/Original28918FloorBinding内未见显式`sorry`、`admit`或新`axiom`占位。未完成处主要是**现有闭合源码尚未接受，以及新分拆路线尚未汇总接线**，不是可以用desired endpoint假设填掉的caller参数。

旧全量路线的关键未验闭合义务包括：

- `Archive.lean:205–206` 原完整text parse success；`:230` 全13 CellShape；`:249` 全28918 RowShape；`:260`原行数。
- `Original28918.lean:153` `original_data_checks`；`:169`保存vertex值，含真实行列式、体积、原ordered vertices、means/tops等。
- `Original28918FloorBinding.lean:48` 全行degree6/Q80/Q96/max(old,new)；`:106` `saved_new_total`；`:110–119`原old总界及替换increment。
- `OwnedSource.lean:49` 原13×97 gate有限检查；`PullingOwnership.lean:59,91,100`原pulling绑定、支持多项式faces和不同顶点集；以及其依赖模块的实际内核/owned接受。
- 新分拆工程中的各余胞有限/几何/source attachment、全13exact sum，以及与现公共终端的一致选择器/namespace/source身份接线。
- Full87 common history/actual gain链与最终ActualEndpoint本身的normal、官方kernel和完整owned接受；最后实际入口导入。

旧polytope完全覆盖是比正saving下界更强的另一项性质；合法内部AE无重计并集足以给所需≤方向。这个数学事实不授权删掉本任务已明确承诺的原13域、全部28918行、原顺序/ID、Q80/Q96、97 gates和真实历史接线，也不允许以少数胞的零补项作为“完整证书任务已完成”。

## 7. 仅用已接受cells0/1/5与普适非负性，原目标能否推出

以下仅对已公开1577 catalog中的实际statement做有理数算术；没有编写或运行Lean，也未引入未证明cell界。

| 已接受原胞端点 | 实际定理位置 | Q96分子 |
|---|---|---:|
| cell0，56行 | `Cell00SourceAttachment.concrete_cell_integral_bound`, `:95–104` | 1055527309463438251 |
| cell1，144行 | `Cell01SourceAttachment.concrete_cell_integral_bound`, `:95–104` | 282451447802500037895 |
| cell5，56行 | `Cell05SourceAttachment.concrete_cell_integral_bound`, `:83–92` | 269254868222475389 |

已接受 `cell_density_integrable`/`cell_density_nonneg`（SourceMeasure`:168–172`）给其余胞积分≥0；配合 `selectedSaving_eq_sum_cells`，这三胞可合成的已知下界是

`L = 283776229980185951535 / 2^96 ≈ 0.00000000358175957859800829947`。

目标Q96与该已知下界的精确算术差为

`q19 − L = 283104946475355620612904 / 2^96 > 0`

`≈ 0.00000357328678958552208664`。

原稿小数目标与该下界的精确差为

`357686854/10^14 − L = 1727935459895625149113474506006841 / 483570327845851669882470400000000000000 > 0`

`≈ 0.00000357328678042140199170`。

原始Q96比原稿表19小数多出的精确余量为

`q19 − 357686854/10^14 = 4431496558728957134618159 / 483570327845851669882470400000000000000 > 0`

`≈ 9.16412009494013235702×10^-15`。

所以**三胞界加其余非负性不能推出任何一个原目标**。这不是证明真实selectedSaving不足，而是这些已知lower bounds尚不强到所需水平；其余胞实际贡献仍未知于现已接受界。已知L约为q19的0.10013674%。

Cell06候选 `8004390162743539242/2^96`没有计入L。即便以后加入Cell06的真实接受界，也不能由此跳过余9原胞和28918任务。更不能拿旧/新full bounds相加：原 `69876938299079768108917/2^94`被新q19替换，只有差额 `3880969509016734128771/2^96`是增量（FloorBinding`:110–119`）。

## 8. 已公开状态、证据限制与本次只读边界

已发布1577 catalog确含SourceMeasure、MomentFloorConsumer、cells00/01/05 SourceAttachment、OriginalAscendingThirteen ownership/export join和Slot19ChargedFrontier；不含ActualEndpoint、OwnedIntegral、Original28918FloorBinding、旧Archive/ArchiveCore、Full87UnionActualGain/ActualCommonHistory/ActualGain/UnionHistory。这里依据静态公开catalog，不运行旧成功normal/kernel/owned/G，不由源码注释反推或覆盖既有接受状态。

公开1577 wrapper本身未重新声明original_full_snapshot_verified；其README明确保留旧 `original_full_snapshot_verified:false`。本审计不改变这个资格。当前运行job和activeattempt输出未读。没有向用户提问，没有访问无关来源。

本地未发现可直接阅读的当前看板 `1_+_1.748_lean_proofs/main.md`；既有Q09报告引用它并把P2.6 broader common-history/full-family义务标OPEN。因此本报告不擅自把P2.6看板所有子项缩为一个弱积分consumer。现可确证的是原稿slot19常数、完整Q96数值端点及现有实际ordinary/positive导出候选的准确类型和未接受依赖。

## 9. 本报告实际读取的源/文档pin

下表是本次局部只读身份记录；不是全snapshot验证或新的G扫描。

| 文件 | bytes | SHA256 |
|---|---:|---|
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19ActualEndpoint.lean` | 7126 | `7669c693fd9fa65a7f1cfbd757345eb48efcac34d9e18364c8d85c01bf562a89` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19OwnedIntegral.lean` | 6659 | `ab58f4acc2a2ea93919d0ee37e5c63e1dba1f07fd704833fefc042d0bb61bafc` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19Original28918FloorBinding.lean` | 5800 | `c4f5765cf575b3faacafe0e765c358373e975a960ab8a7c87d742660510e51b1` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19Archive.lean` | 10816 | `f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19Original28918.lean` | 11245 | `05a98da484b41a8e5e0842c31b86b74df0a94bfc2e51ff4c64b9daddf092dd4f` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19OwnedSource.lean` | 6423 | `e18f481c54879b7a51346db7f3549c1ac12f393a194b79322a600e7bf89c1c8b` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19PullingOwnership.lean` | 10846 | `87fd625fc864128a001ba49deab415fd82eb944ee3c23bda036762c199f94dde` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19SourceMeasure.lean` | 10895 | `877df6385e28866432276e78b234f9d5634e5c6d529757b393741698444cd3bb` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19MomentFloorConsumer.lean` | 13920 | `0e332cbd300f14e811a564d129c20030f1ab6bae24f9f98f4ccf7bec2d7132f0` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19Cell00SourceAttachment.lean` | 4351 | `3a9c1e71fd2daa24401be77dc8bf31782127a9ff70883d204b70cb379c432100` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19Cell01SourceAttachment.lean` | 4314 | `0e4b7165e84e7ceed33c6b1c7c6181830d2dcb85d2bcd9ea6dc847e48cdb7879` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalSaving19Cell05SourceAttachment.lean` | 3791 | `cc4be442e0da6c2fefc3b6d096115c10ca4bb66f8f780e3402268953ebc451ae` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P4AOriginalFull87UnionActualGain.lean` | 20983 | `6f92a62137361cf77a5063f2f7c78c0df1288e891f9b90057aea31c712ed7c7c` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P4ASlot19ActualParentIntegral.lean` | 3776 | `5bcdc6d85d6654cc07a1d1d9079370b4f406227f78e72475b939d0c4cfe847b6` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P4ASlot19ChargedFrontier.lean` | 9046 | `fa457ee89dabde751e9dce99c07e461c79ff15a0cb57dff25ae9121f929d9ef4` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P4AAll22OriginalKLedger.lean` | 9181 | `f6d8cbee7226df90750d57771f223e8634a19107720c3a961d46481848f1e03c` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/P2OriginalCertificateBudgetAssembly.lean` | 8813 | `cda79544b6a3d36f468f981d20a811e9f2e4a0cf79e5d12a490dc4155402090b` |
| `/workspace/p26-proof-continuation-20261127/ImbalancedChen/UncompiledContinuation.lean` | 144384 | `8b4604f442156fb50f17ea74ad8ea067b7e3f9e32bafab0333dc3a48fa4bfacb` |
| `/workspace/p26-proof-continuation-20261127/docs/verification/20261125-p26/history/REPORT.md` | 5796 | `03dec08b4d1e16e277b1faf2164b3d25e07d87c0a9c52618593d01c9a69747db` |
| `/workspace/p26-proof-continuation-20261127/docs/source-only/20261102-resume-30q/saving19_instance/REPORT.md` | 17753 | `d5fd3f0368bc3bca044070c6200b9347f0c7cd2b1e2e7ba1de3a6c88f7f712b7` |
| `/workspace/p26-proof-continuation-20261127/docs/verification/20261128-p26-cell06-through1577/CURRENT_ACCEPTED_CONTEXT.json` | 1334062 | `f15132afa73282caf1115d897829cd807d046c11b95bbe722446a44fbf9fc8d8` |
| `/workspace/p26-proof-continuation-20261127/docs/verification/20261128-p26-cell06-through1577/README.md` | 4447 | `880ec8ed258539dc60e017eb31a11c6ebf584db61d37cc622de38a8023317a13` |
| `/workspace/chen-imbalanced-semiprimes/paper/release-20261106/en/argument.tex` | 55378 | `87f5b5f2e25082e00b2b04d8ecc684630d64846912457dc0adade1a36fd67182` |
| `/workspace/chen-imbalanced-semiprimes/paper/release-20261106/en/numerical-appendix.tex` | 42662 | `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232` |
