# upper_jensen：E 批真实原始父格遗漏几何

状态：SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT。三份 Lean 文本闭合；局部步骤完成。完整原始目标 `task_complete=false`，`compiled=false`，`formal_credit=0`。未执行 Lean、lake、数值 checker、归档逐行判定或 Q80 总量计算；前四批源码保持冻结。

本轮消除了一个真实接口缺口：由原始整数第三层 margin 和独立非领先 pair gate，推出 canonical adopted owner 在许可父格上零遗漏，再把完整归档的真实严格 gate 遗漏精确分解。没有假设 trim 小、全归档 selected、某个 Jensen 积分结论或完整 K。

## 原稿和独立对象

原稿 `chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` 的 upper 段落要求继承实际祖先、同阶段区域分离和 successive new-minus-current-parent；附录 `global-positive-upper-completion-20261010.txt` 第 59–78 行保留非领先 pair 的独立 gate、旧父格 subdivision 与新 cover 的分离，第 184–216 行要求同一物理有限树、真实 inherit 区域和适当墙条带，禁止删除可能具有全父测度的 child 投影。

这里使用 D 批 independently constructed `adoptedOwners`：同一 raw decoder 经两端 selected 和 firstStop 筛选。E 批 upper_mesh 的严格 `licensedOwners` 还筛选真实第五层 `gateCheck 0/e`。两种 owner bank 没有被混同。完整 typed archive 使用其独立 143-block literal `rows` 及 `ArchiveIndex`；292633 是已给 shape 源的形式结论，未在本轮重算。所有全归档求和按原始位置，保留重复行，未以 raw.toFinset 去重替代。

## 证明主线

`P5OriginalBufferOwnerGeometry.lean` 在同一个真实 rational box 上证明 fullGamma 随 loss 增加不增。每个 xz/yz pair 失败时仍有原 baseline，mu dispatch 也保留原 branch，故 levelExponent 同向单调。对两端真实 selected 的同一半开 owner cell，正 buffer fullCell 包含于零 buffer fullCell；初始 cap、current exponent、firstStop 和严格 history 均逐项保留。原始 `thirdOwnerKeyCheck` 的整数端点与已有正 stop surplus 推出 decoded label 的实际 firstStop，结合前驱 `decoded_third_owner_selected`，消除 canonical adoptedOwners 的四项过滤，而非假设过滤结论。

`P5OriginalLicensedTrimResidual.lean` 定义原始 `mask5WholeRawCheck || mask6WholeRawCheck`。这是第三层两种非领先 pair branch；并非 raw.mask 第五层位元的宣称。两项 check 自带真实全父格第三平面 margin 和独立 xz/yz pair margin，复用原始 `whole_raw_mask5/6_owner_cover`。先证明正 buffer adoptedDomain 等于原父格，再经同 owner 的 buffer 单调性得到 baseline cover；没有将正 e 证明错误地套在 e=0、chi<0 上。由此许可父格 omittedParent=∅、成本为零。全 raw bank 的 trim 精确只剩两个原始 check 均 false 的 residualRows；每个 residual 原始 clipped parent 的真实体积仅付一次。

`P5HistoricalIndexedTrimGeometry.lean` 消费 upper_mesh 的独立完整 source index 和严格 owner bank。定义真实额外拒绝域

`gateRejectedDomain = canonical adoptedDomain(0) \ strict indexedDomain(0)`。

证明 strict indexedOmitted 恰为 canonical omittedParent 与该 gate 拒绝域的互斥并，故对真实 BASE 几何索引，strict trimCost 精确等于两个实际体积成本之和。许可第三层几何只消去 canonical 项，绝不自动消去额外第五 gate 项。完整 292633 位置的 canonical trim 精确归约到原始两个 check 均 false 的索引；严格 BASE bank 的 trim 精确等于其 canonical margin 残余加全部真实 gate 拒绝成本。残余父体积的定量界直接使用 fixedParent=originalBox∩ambient。

最后消费同一 source-index B13 schedule，得到先 e 后 q、同一 chi=e/20 和 omega 下

`|licensedBankError| < eta/2 + residualParentCost + gateRejectedBankCost`。

父格残余按原始 source index 计一次，没有按每个 decoded owner 或每个 64-child 重复 raw mass。这里没有把总残余≤eta/2作为结论前提；未解决的几何成本明确保留在右端。

## 冻结源码及安装顺序

| 目标 module，统一前缀 ImbalancedChen | 行数 | 原始字节 SHA256 |
| --- | ---: | --- |
| P5OriginalBufferOwnerGeometry | 156 | bc04acf47d043dfa796a0275fc4182279d9794b606a649fb4bb33794554e56b2 |
| P5OriginalLicensedTrimResidual | 210 | 4a7a78146fca1eb1d99ef9a6d5fba9b6b8bc2d34b6bc026e85c8a20679717fe7 |
| P5HistoricalIndexedTrimGeometry | 191 | 5e76f55c601a1680bd0c6becc12c2b5059670aaf3a283f7039a7822ce81c28e6 |

源码均位于本目录，将原始字节安装至 `ImbalancedChen/<同名>.lean`。先安装 registry 指明的 frozen raw-key/mask5/mask6 前驱及 D adopted/uniform bank、E indexed archive/error 与其完整 typed 数据依赖，然后依上述三行顺序安装。真正现有生产 module 与仅 source-only 草稿在 registry 中区分；没有宣称草稿 import 已可编译。

## 明确剩余

- 没有逐行判定完整 archive 的两个原始 margin check；既不声称 residualRows/indices 为空，也不声称原始 292633 行全部满足 BASE 几何。
- BASE 外的 upper_mesh `residualIndices` 仍明确保留。对这一部分未宣称原 kernel 可由当前 compact B13 直接支付。
- BASE 内的 canonical margin 残余仅有真实父体积成本上界，尚无任意小结论。严格第五 gate 拒绝域也未证明可任意小。
- upper_mesh CommonPolicyInputs 可能改变旧祖先；本轮 B13 比较的是同一旧 source owner/kernel，不是改变祖先后的误差定理。changedParentPrefixes 残余不被消除。
- 独立 typed literal rows 与原始 NPY bytes 的全字段 Lean authenticity 仍是独立义务；SHA 和 metadata 不充当该等式证明。
- 未对 complete causal policy、全归档总量、全部数值 enclosure 或最终 K 作完成声明。前批 named 128 child 结果没有被扩为全 archive。

上述是明确保留的实现义务。本轮没有给出新的原稿反例或原稿缺陷结论。所有验收仅限源码逻辑审阅，未获 Lean 内核验证。
