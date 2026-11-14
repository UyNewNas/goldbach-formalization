# R9 两个实际失败模块的最小源码修订

状态：`SOURCE_ONLY_UNCOMPILED_PENDING_INDEPENDENT_REVIEW`。本交付只提出两处实际错误所在模块的最小修订，没有本地编译、LSP、Lean/Lake、证明辅助程序或 CI 执行，也没有新的数学验收结论。

## 精确证据与原源

- 实际 run `43430153710`，job `132003902339`，driver head `9e4fa641ef9fad4a8cb073ff7e883a660131eeff`；数学源 pin `484d8ffc8f79e7c213b33ae86a8d960cd4da6de4`。
- 只读用户已提供的 light ZIP，SHA-256 `5fe15f0748168e2871fdd17076e56c8b4d62c688da9b5aec06d561f9502534dc`。错误直接来自 `batch-build.log`；完整原文已在相邻 `s07/R9_COMPILE_FAILURE_EXCERPT.txt`。
- `P2_STAGE_RECEIPT.json` 与 `SOURCE_OBJECT_BINDINGS.json` 双重约束实际选入源。两模块的原源在 receipt 中均属 baseline `eb035a259f2f40853e9899f6d98af25852184fee`，不是把当前工作树或最新版本当成 R9 源。
- OldWeight：17691 bytes，SHA-256 `7eb654897cb3be7322699d98fed7c1ddd70211de65d00acc6896714a6c2c3f37`，blob `0b6ca79da9c3b1f79ddfbac68546515ada9b7d9c`。本地可见文件恰好与此字节完全一致，复制后再次双重核验。
- SecondDecay：15180 bytes，SHA-256 `abd3c8d28a01ecbbe64361a25e11d51a030827ac783463f7189e2a158e673227`，blob `e46424376bf81b48a5c1a3a412823f88a474af72`。从本地已有 bare 对象库 `output/t-batch-20261110/publish.git` 只读 `git cat-file blob` 恢复，并核验精确字节；没有 git 写入或网络拉取。

## 错误一：OldWeight 第 266 行的 dependent match 转接

实际诊断是 `hbranch` 简化后得到 `match k with ...`，但桥接参数期望 `match k, ⋯ with ...`。各分支的不等式逐字相同；阻塞在保留的判别参数及依赖匹配的表达形状，不是数值不等式错误。

根因对照使用 **R9 已实际 Built 的源** `ActualThirdOriginalP4ASixTentSymmetricLeaf.lean`，而不是未经验证的新模式。其选入 blob 为 `2668b1686d662bd4818a5f50ef633dd15b3484af`，SHA-256 `bc6092cfae16065c1bec98a3ee817d67e6bae4d7d5764d3752b02702f0abc94f`，来源 `repair_r9` / 数学 pin `484d8ffc…`。该文件第 195、197、199 行的同型 `original_selected_tent_guard_bridge` 调用，三个参数都采用 `by cases k <;> simpa only [...] using ...`。OldWeight 的对应三个参数只有 `simpa only`。

修订把此 **同一成功原件的三段转接方式逐处复用** 到 OldWeight：在 `hbranch`、`hroot`、`hres` 的局部参数证明内各加入 `cases k <;>`。局部 case 分析仅消去 `.rise/.fall` 判别；不改外层量词，不缩减到某一侧，也不改原 selector 的 if/elif 条件、优先级、根过滤或正残量条件。三个 match 均有同一潜在结构，所以沿用成功供方完整的三个转接，而非只补首个报错位置。

## 错误二：SecondDecay 的可积性名字解析

实际诊断先报第 140 行 `Unknown identifier ordinary_factor_integrable`，随后第 137 行留下整条积分界目标。后者在该处证明脚本中依赖 `hnew`、`hold`，与前述未知名字构成同一失败链；没有证据表明它是第二个独立的数学积分障碍。

R9 所选公开声明确实已存在于 `ImbalancedChen.OriginalThirdP4AOrdinaryEarlyReturnSourceOnly` namespace，文件 `ActualThirdOriginalP4AOrdinaryEarlyReturnLeaf.lean` 第 86–99 行。该源 SHA-256 `94ce0c2504a26b63154886eaba45cccefb4664c432b775ec601a2893ceb1d1df`，blob `10c1183634a4271812dd263c5f129ec9c54cc5d7`。该 theorem 从实际 factor 的可测性、全局有界性以及实际 box probability 证明可积性；它不是待证明的积分目标，也没有新前提。

实际 import 链为 SecondDecay → OriginalFirstDecayLeaf → OrdinaryRawFallbackAllOld → OrdinaryOuterMinimum → OrdinaryEarlyReturnLeaf。R9 已 Built 的 FirstDecay 在自身文件中打开了 `OriginalThirdP4AOrdinaryEarlyReturnSourceOnly`，并在第 147、154 行成功使用同一 lemma。SecondDecay 虽打开 FirstDecay namespace，但未打开 EarlyReturn namespace；`open` 指令不会被传递成另一个 namespace 的导出成员。因此普通短名字在该处不可见。

修订只把第二源内两个短调用改为完整相对限定名 `OriginalThirdP4AOrdinaryEarlyReturnSourceOnly.ordinary_factor_integrable`。这样保持 imports、所有 theorem headers、正性/宽度/可测性证明、概率归一化、`integral_mono_ae` 及 factor 四原样。没有增加新 theorem、假设或 helper。

## 原手稿核对与数学范围

读取的原手稿为 `chen-imbalanced-semiprimes/verification/data/imbalanced-chen-transfer.tex`，SHA-256 `06ecf0c7a8d767115dd0ef595e52844d49486b4b98d5979300faf47f4e09ff78`；与 `proof-library/source/imbalanced-chen-transfer.tex` 现有副本字节相同。

- 原文第 5653–5768 行保留 ordered-domain 六分支包络、两张 affine tent 平面及原 gate；第 6245–6248 行说明内部 cell 使用 weighted Jensen/chord 和有向区间算术。OldWeight 的失败是这些既有分支的 **形式表达/依赖消元**，未发现需要改变手稿数学命题之处。
- 原数值对应式只读核对 `goldbach-research/numerical-third-compact-independent-20261010.py`，SHA-256 `005fcc24c3431753e2530ab90f70e80d2256b3691cd45d14e13eb9191b0caa7c`。第 108–139 行保留所选 affine OLD、原 signed chord 与 clipped weight；第 154–156 行正是 `ao>=3*z1` first decay 及 `ao>=4*z1` 的 `UP(decay(ao-z1,z1)*(T-ca)*z1,z0*ao)` second decay；第 161–163 行保留原 mass 与 final UP。该文件仅作为原有数值配方的静态对照，**没有执行或把它当 R9 源绑定证据**。
- SecondDecay 的可积性及把 pointwise bound 积分成 full-box bound，是 **已有供方已补出的标准推导**。修订只是正确引用既有声明。二阶 decay 的 derivative/MVT 推导另由 R9 已选入 `P4AActualLowerIncrementGapBound` 供给，参考副本及精确 receipt hash 已冻结；这里没有写新的数学证明，也未把数值配方本身当数学证明。
- 两个实际诊断均未揭示原手稿的 **实质数学缺口**。这一判断只涉及这两个局部故障；不等于 full historical charge list、完整 P2、kernel replay、axiom export 或最终 acceptance 已通过。R9 后续八个未启动模块仍未验证，本交付也不对其推断通过。

## 静态核验及后续复用

`R9_TWO_SOURCE_REPAIR.patch` 只有五行 proof-body 词法变更。全部 30 个顶层 declaration headers（17 + 13）与 imports 逐字不变；原定理的前提、结果、量词及所有计算定义均保持不变。未新增 `sorry`、`admit` 或 `axiom`。该核验是纯字节/词法检查，不伪称 Lean AST/elaboration/kernel 检查。

`FREEZE.json` 记录 before/revised SHA-256、Git blob、来源、imports、参考供方及原手稿 hash。`before/` 和 `references/` 仅为不可混淆的证据副本；待选修订只在 `revised/` 两源。

R9 的三个实际 Built 原件必须作为后续复用候选：ClippedGapAssembly、FirstDecayLeaf、SixTentSymmetricLeaf。其精确选入 receipt entries 与真实 build markers 已写入 FREEZE；本地没有重编译它们，也没有重编译另 89 个 protected 模块。

最终边界：**源码修订候选已冻结；编译成功未声称。** 本次遵循用户禁止本地重现/编译的约束，systematic-debugging skill 中的本地复现/测试步骤以实际已有 CI 失败证据和纯静态同型对照替代；没有把用户禁止的步骤间接交给任何 helper。
