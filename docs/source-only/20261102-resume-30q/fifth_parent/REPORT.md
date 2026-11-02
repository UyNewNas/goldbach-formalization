# Q07 — 真实第五档案的历史入选与扣债全父包络

**SOURCE ONLY；未编译，kernel_verified=false，formal_credit=0。** 本次新增四份严格 Lean 源码。286 个新的有限证明体及全部继承 guards 均为 **UNEVALUATED**；写出 `by decide` 不等于该断言为真、能在给定资源内完成、或已经核验。P1.4 的完整原 floor、真实数据认证及全局策略仍 OPEN。

本任务仅覆盖原第五档案。没有重写 P 的 H3 十二域，也没有处理非第五的其余 75 个 eighth 域。只写本目录；未运行 Lean、Lake、编译、CI、数值 certifier、有限 guard、Git 或子代理。

## 先读原始对象，再去重

已读 Q/BRIEF、q01 清单、P/adopted87_policy 的 REPORT/REGISTRY、P/reviews/t26_review_policy_reserve，以及 I/J/K history 的报告、源码和 K 独立 review。q01 对第五旧稿的清点并不穷尽已有供应。本次在生产、历次 source-only 与显式包含 ignored/hidden 的 `.lake/proof-continuation/source-reviews/drafts` 中继续定位后，复用下列已有结果，不另造通用 refiner 或 PhysicalRows：

| 已有来源 | 精确复用及边界 |
|---|---|
| `30g/upper_jensen/P5HistoricalTypedGateAdmissibility.lean:20–1318` | 143 个原 zero-buffer correlated gate 封闭证明请求及 `archiveRow_original_zero_gates`；尚未求值。 |
| `30h/upper_jensen/P5HistoricalUniformExtraGatePayment.lean:29–192` | 全档案有限正 margin、同 e/q 下每个 decoded row 的 0/e gates、原 mask、`licensedOwners_eq_adoptedOwners`；无需另给 all-gates 假设。 |
| `30h/upper_jensen/P5HistoricalGatePaidReserveSchedule.lean:58–146` | 先取正有理 e，再取单个 aligned q；实际 old-literal indexed integral 误差 `< eta/2 + canonicalHistoryBankCost`。 |
| `30i/history_reserve/P5HistoricalBelowMuCommonParent.lean` | 从每个原半开盒 `t0 < 39/200 < mu` 推出实际 common/old parent 一致、`archive_parentExcess_zero`。这条第五源的 changed-parent 债已有码，不再把 parent equality 当成缺少前提。 |
| `30j/history_reserve/P5HistoricalActualThirdHistoryTransport.lean` 及 `P5HistoricalHistoryTransportConsumers.lean` | 实际矩形 fullGamma/currentExponent、activation/fallback、Q3 与同 positional Q4 的传递；不以任意 stored cap 替换。 |
| `30k/history_ideal/P5OriginalHistoryGapCorner.lean`、`P5OriginalHistoryCorePayment.lean`、`P5OriginalHistorySourceConsumers.lean` | 原 11 条整数 gap 平面、原 order 语义、半开角点、严格 current-third margin `133/2048000`、每行历史空集与真实 Q3/Q4 consumers；原稿尚缺全实际 typed 行的 order/positive-gap 实例。 |
| `30f/upper_fifth/P5OriginalGenericWireFloorReceiver.lean:118–157` | 任意原 mask 的同父完整 64 子盒 Jensen/floor 证明；保留真实 child-owner reserve。 |
| `30g/upper_fifth/P5FullStoredParentSameOwnerBinding.lean:29–77` | 原 72 块 stored new/old 同位置；`new=max(old,complete64sum)` 的闭 guard 与 `stored_minus_old_defect_eq_wire64`；不把 old 再加一次。 |
| `30h/upper_fifth/P5FullArchiveOwnerIntegralAssembly.lean:34–143` | 实际 owner 的源 index 唯一性、完整源最大值、逐 owner integral 与独立定义 `archiveFifthIntegral` 的精确重组。其旧 floor 下界只对 `mask56Indices`，且扣两笔债。 |
| `30o/adopted87_policy/P5OriginalFourthFifthSourceInputs.lean:56–143` | 原第四 17-byte payload 解码出的 `originalRows4`、实际整数 `originalAdmission4` 及其 geometry 结论，和同原第五 bank 的 `heldData`。不是 complete sixth/eighth policy。 |

上表 `30x/` 表示 `docs/source-only/20261102-resume-30x/`；F/G 的实际目录日期为 `20261028-resume-30f/g`，完整精确路径及 raw hashes 均列入 REGISTRY。原 143 typed blocks/hub 在 hidden frozen 目录，shape 在既有 `TypedShapeCandidate.txt`。本轮只重读元数据/源码并逐文件 hash，没有重新转写数据或物化重复副本。Q06 负责 L 的 binary authenticity、F keys/positive 复用；本任务不重复那些证明。

## 原手稿与原 certifier 的依据

`../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:367–375` 要求 actual ancestors、successive new-minus-current-parent 和不重复收益。`../goldbach-research/fifth-prefix-adaptive-refinement.tex:34–83` 保留原第一/第三决定，使用真实 L4、自己的第五 cube 与 clipped lower residual；其后对任意合法 partial/full 第四树用原 U4 上包络。因此不需要假设数值父级恰好等于某个固定 raw15 最大值。

原 `certify_fifth_prefix_jensen.py:17–37` 先计算第三 gap：对 masks **1,3,7,5,6** 的两仿射面作 correlated lower bound，再与 W 取 max；独立要求 `lo[:,:-1] >= hi[:,1:]` 和 `thirdgap > 0`，之后才检查第五 half/full/selected gates。`export_fifth_prefix_jensen_witness.py` 收集已接收的 exact-term 调用。原第五 mask 和三个 Jensen 统计量不是第三历史许可。

原 `fifth-prefix-subdivision-refinement.tex:17–35,113–134` 固定全部 292633 parents、各自 mask 和 old planes，并对每父完整 64 children 作 whole-parent maximum。`certify_fifth_prefix_subdivision.py:108–121,160–176` 的 `split_bound` 与 `full` 对每个原 row 执行，没有 mask5/6 过滤，最终保存 `max(old, childsum)`。F 的 `mask56Indices` 是较早形式化采用的**第三 owner licence 子族**，不等于原 subdivision 的运行范围，也不等于第五 `raw.mask ∈ {5,6}`。因此将真实剩余父盒补到完整档案，是原论证所需的缺项，非更强的导航目标。

## 新增供应

### 1. 真实 143 块的原第三历史入选请求

`P1HistoricalFifthTypedHistoryAdmission.lean` 定义精确谓词

```
rawKeyOrdered raw ∧ 0 < producerThirdGap400 raw
```

`rawKeyOrdered` 和 `producerThirdGap400` 直接复用 K。143 个封闭有限 body 分别读取原 block000…block142；聚合复用原 `rows_toList_order`、`block_order`、`archiveRow_source_member`。没有另建索引、重排行、转 Finset 去掉重数、改变 mask 或重算保存的统计字段。Decidable 实例显式展开有限整数谓词；不用 Classical decision、axiom、sorry 或 native_decide。

这填的是 **source-level 的真实全行有限实例**。其形式接受仍待执行；原二进制与这些 typed rows 的对应仍依赖已有 L 闭证明候选，而不是 hash 证明数学等式。

### 2. 同 q 的实际历史、动态 Q3/Q4 和 literal error

`P1HistoricalFifthActualHistoryAdmission.lean` 将上述真实源实例传入 K 已有证明，消除每行 `ho/hp` 输入，给：

- 每个真实 decoded owner 的 current-third margin、`jointRegion` 和 `canonicalInvalidHistory=∅`；全 `canonicalHistoryBankCost=0`。
- K 的固定 `sourceCoreBankCost=0`，无理想 core 小量假设。
- 实际素数 third ancestor 的 `originalQ3` margin。Q4 结论直接选 **actual `parentOwner ...`**，用 `rfl` 供旧接口的 owner equality；selected licence 从原 `licensedOwners` 构造推出，没有外加 parent equality 字段。
- `exists_same_q_complete_history_paid` 使用 H 原来选出的同一个 e/q，联合全部真实 raw-box 完整覆盖、原 masks、0/e decoded gates、`licensedOwners=adoptedOwners`、历史空集和 I 的 actual parentExcess=0。实际 old-literal indexed integral 误差变为 `< eta/2`，无未付 history 项。

量词仍先取 e/q，再统一所有 N/历史。参数范围保持 `0<omega≤1/800`、`0<e<3/51200`、`chi=e/20`；无 c/K 或源族修改。Q4 局部定理是原 **zero-buffer** baseline 的动态父级，不声称 buffered Q4 与理想六分支相等。

### 3. 原全档 64-child 输入与扣债 floor 包络

`P1HistoricalFifthRemainingChildFacts.lean` 只补 `ownerLicenseCheck=false` 的真实剩余源位置，每个原 block 有一个闭合有限 body，内容是已有 `SourceChildFacts raw c`。true 分支直接复用 F 的 `proposed_full_mask56_source_child_facts`，未重写其证明。合成结论为每个原 ArchiveIndex 的全部 64 子盒输入事实。它们是整数 d、原 ratio/vertex、原 expanded floor 的有限条件，不是目标实积分下界。

`P1HistoricalFifthFullOriginalFloorEnvelope.lean` 复用 F 的 arbitrary-mask Jensen receiver、G 的真实 owner 可积性、G 的 stored-minus-defect 恒等式和 H 的全档积分重组。真实第四输入固定为 O 的 `originalRows4/originalAdmission4`，所需 geometry 由 `originalAdmission4_geometry` 推出，**没有几何许可输入**。逐父和总和均保留 original owner 与物理 old fourth profile。

最终得到的是且仅是

```
sum_(all original i) storedNewQ(i)
  - sum_(all original i) oldBranchDefectQ(i)
  - sum_(all original i) indexedActualReserve64(i,e,q,chi,omega)
<= archiveFifthIntegral originalRows4 originalAdmission4 e q chi omega.
```

原 292633 位置各计一次，每父恰 64 子盒。不是 mask56 子和，不以总积分为输入，不新增 factor64、Chen quarter 或排序 factorial；旧 Jensen/Taylor 分支没有由 child proof 冒充支付。

## 严格剩余边界

1. 新 286 个有限 bodies、继承 G zero-gate/stored-max/F child facts/base/key guards，以及 L 的独立 original NPY-to-typed 证书和 O 字节 include，全部仍 UNEVALUATED；需完成必要 import staging、elaboration、资源与 kernel 验证。
2. 完整原 stored floor endpoint 仍须支付 `oldBranchDefectQ` 的旧 Jensen/Taylor 证明分支，及真实 `indexedActualReserve64` 的总成本。新 history=empty 和 H old-literal B13 误差，**不自动等于这个 child-specific reserve 小量定理**。
3. O 的具体 original fourth geometry filter 已足够供应这里的包络许可；没有因此宣称 complete adopted fourth/sixth/eighth 策略、完整87、所有原收益保留或 same-rho 物理密度流程完成。新总包络仍针对已有 `archiveFifthIntegral`。
4. 全 All22 endpoint、两笔完整 reserve、最终物理 rho 和 PP/K 仍不在本任务已供范围。主导航“完整原 floor→实际总积分”不宜直接改蓝；可以登记“扣原 old-branch defect 和真实 child reserve 后的全档包络”这一窄源码叶。

缺口分类：本次的遗漏是 **(2) 可补的原始有限源实例及原 source 范围对接**；未运行的 guards、缺省安装和大有限 reduction 是 **(1) 实现/形式验证边界**。未找到坏档案行或原稿数学矛盾，故未升级为 (3) 实质原稿缺口。

## 静态验证与交付

只做源码/原程序阅读、声明及 import 路径清点、143 block 引用文本完整性、JSON 和 raw SHA256 检查；没有计算 gate、gap、floor、积分或任何总数值。生成脚本的两个输出只包含证明源结构，不解析/重转写 archive literals。286 个闭 body 的真假未据此判定。

Q23 独立审阅已认可四源所列窄 scope；最终 hash 见 REGISTRY 和独立 review。完整 direct imports、真实143块 pins、原程序/报告 pins、声明行号、安装模块、实际消除/保留前提均登记于 `REGISTRY.json`。未安装任何模块，未改旧文件。
