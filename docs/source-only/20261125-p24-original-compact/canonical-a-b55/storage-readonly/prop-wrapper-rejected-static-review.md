# 通用可约 Prop 包装：在冻结原 shape gate 下不可采用

结论：**否定本次方向，不开发、不编译、不修改 inspector，也不改当前 A03e。**

此结论不是否认一般 Lean 中可以给定理类型增加一个定义上等价的 Prop 包装，而是该表示不满足本次明确要求保持的原完整形状检查接口。

## 精确已读原件

- 当前 A 候选：`P2OriginalCompactArchivedTotalCandidate-node-blocks-05-compact.lean`，SHA256 `03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd`。
- 已实际通过的 P3 full2048 原检查器：`/tmp/p24-full2048-evidence-recovery-20261126/unpacked/owned/InspectBlocks.lean`，SHA256 `c190906df505fbe101f0aca84f46a7ba3252ad75b7ab6bb07ffa2ae3fb950d48`。

## 决定性源码依据

原检查器只读取 declaration 的 `info.type.consumeMData`。它连续六层对每个项直接调用 `isAppOfArity ``And 2`，拆出左右两个原始参数；不是对归约结果进行检查。六层后必须刚好得到 64 个叶子。

每个叶子同样只去除 metadata，然后直接要求 `isAppOfArity ``Eq 3`。等式 carrier 必须是原 Node alias 或 HistoricNode 的常量，左端必须直接是指定 `sourceState` 的三个实参，右端必须直接是 `HistoricNode.mk` 的四个实参。节点 index、completed、grid 和四个 Int 也按严格语法读取。

检查器明确写明不做 `defeq`、`whnf` 或 sourceState 求值。它最终还核对全部 2,048 块、131,072 个节点、块起点对齐、连续范围、私有 theorem、safe/nonpartial/nonaxiom 和无自由/未解变量。

因此，若把闭块类型改为 `GenericFacts start values`，即使其 WHNF 定义上等于原六层 And64，原检查器在第一层看到的 head 仍是 `GenericFacts`，于是 `balanced` 置为 false，后续没有 64 个原叶子，整套 shape check 必定失败。若只包装叶子，同样会在原 Eq 直接语法检查处失败。

## API 与范围

当前 `checkBlock` 由 `balancedFold` 明确构建原 And type，调用同步 `mkAuxLemma [] type draft.proof`，检查 theorem 后才用 `projectBalanced` 产生已核块的节点证书。一般元层投影是否能通过额外归约接受一个可约包装，不会改变上述原 inspector 的直接语法结果。

把 inspector 改成先 whnf，或者新增一套解包分支，会改变被冻结的检查器。把包装在安装 theorem 前完整展开则恢复原 type 表示，不能以该包装达成 fulltype 存储节省。本次要求不允许以这些变化绕过空间问题。

未实现任何新 Prop/helper/生成器，没有重跑 full2048，没有增加/删除辅助定理，没有改变 64 节点块、原数字、source options、owned audit 或 shape gate。现有 storage 缺口继续作为实际工程 blocker 处理。
