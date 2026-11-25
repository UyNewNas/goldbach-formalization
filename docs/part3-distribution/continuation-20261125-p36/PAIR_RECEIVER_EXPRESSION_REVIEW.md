# PairReceiver 表达修复与 qPoint 可见性：独立只读审查

日期：2026-11-25。范围为 `0bae3ddfc80db1b6b0faf2245e2c1abcc5875c11` → `c99f987016148b32b6278bf948e8125bf058522b` → `0de9c5100f4725a10cb202327504c82fa34a129e` → `669de6df7493c10f2892a812bac1fe9d56e2ed5e`。只审查 PairReceiver 的真实差异、可见性记录和第 17–19 份诊断；不编译、不 stage/提交，不重复 endpoint 候选数学审核。

**结论：未发现本次修改引入 source proof escape、新数学前提或改变原选择/冻结规则。qPoint 的 statement/body 在移除 `private` 后原始 bytes 完全相同；`exponent_upper` 则有单独实测支持的证明体修复，不能再把它的当前正文称为历史 visibility-only 版本的逐字副本。所有结果仍是源码审查，尚无本次独立核证过的主/extra 成功 archive。**

## 1. 实际表达修复

| 修改 | 核对结论 |
| --- | --- |
| 打开原 `P2OriginalLowerAffineTieSelector.LabeledBranch` | 该原结构确含 label、affine cap、argument；原 CandidateBank 的 inherited 类型使用同一结构。新 named-open 消除未知名字被 autoImplicit 误处理的错误，没有引入任意的新类型假设。旧名字未成功 elaboration，不能声称已有两个验收类型的同一性。 |
| `exponentCode_membership (m := mesh) hx` | 原 API 的 `m` 是隐式自然数；`hx : x∈Icc a b` 不包含 mesh，无法独立确定它。现在明确选取同一声明、同一 qHi/code 中已有的 mesh；不改变 `exponent_upper` 的 statement 或增加条件，但确实改变其 proof bytes。 |
| c3/c4/c5 的局部 alias 展开 | `h3` 的 simp 增加原 `c3`，h34/h45 在原 prefix rewrite 前展开其两个 let。原 codeAt、三个 cap、rank、word 和两个 prefix lemma 均未改变。 |
| selector 假设先 `dsimp only` | `select` 原定义没有修改。该步骤只展开 `pcode/base/rest` 的局部 let，使原来的 if 在 `hsel` 中显现。 |
| 只处理 split 后存活的分支 | 在 `hsel : select ... = some branch` 下，stableBase 分支给 `none=some branch`，已由 `split_ifs` 消解。余下仍调用原 `firstStable_some`，取得 `branch∈rest ∧ stableAlternative ... branch`，再投影其原 `sourceCheck`；删除多余两个 bullets 没有跳过合法分支。 |

对四个版本去除注释/字符串后扫描，`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`run_tac` 均未出现；差异也没有关闭验证的选项。

## 2. 可见性记录与历史正文边界

[PAIR_RECEIVER_COMPATIBILITY_VISIBILITY.json](PAIR_RECEIVER_COMPATIBILITY_VISIBILITY.json) 的 SHA 为 `700ecb80ced61537ea7c993cad6cca5ff0566c2397d41222e7c320358de9227c`。其中 source-before `8f01047a...`、expression-repair-before-visibility `14836560...`、source-after `c59c6329...` 均已通过实际 Git bytes 和逆向恢复 `private` 独立重现。这个 source-after 绑定的是 **c99 阶段**，不是最终 `669de6d` 文件。

qPoint 声明从旧 `private theorem qPoint_cast` 到下一声明前的整个原始 byte span，在仅删除 `private ` 后，与最终公开版本相同。当前记录的 private/public 声明 SHA 分别为 `4238bdeea5c2fe0437a839be6465c3ae4d804603e6b5bbcc9e8d2c180c0a0cf4` 和 `9e32c41ca3e93cb36b0263b750aa88c43d9ee0a54ea4b7b8600659e941b0a25d`，可按“声明保留一个末尾 CRLF”重现。历史 coarse visibility 记录使用去掉末尾空白的 span，因此其声明 SHA 不同；这不是正文改变或 CRLF 规范化。

历史四 helper 中，`squareGates_mono`、`sum_le`、`slot_words_mono` 的正文继续逐字相同；`exponent_upper` 的正文因显式 `m := mesh` 而不同。ELABORATION_REPAIRS 已准确记录这一点。旧冻结记录及预检应保留为其原基点证据，不能冒称当前 Receiver 仍为 `8f01047a...` 或旧 qPoint-only 投影 `45fd5f2c...`。后续集成应绑定最终实际源码，且 qPoint 已公开，不能盲目重复应用旧 visibility patch。

## 3. 第 17–19 份原始失败日志

| 日志 | SHA-256 | 实际错误类别 |
| --- | --- | --- |
| [seventeenth-pair-source-receiver-failure.log](seventeenth-pair-source-receiver-failure.log) | `9301981a6b16d3c35ffdf75430e62b791583a6e2cc4cabd0dbe6a582f8d024b0` | 5397 bytes / 103 lines；8 个 error、2 个 warning：未知 LabeledBranch、恢复后的 selector 错误、无法推断 m，以及未展开 code alias 的目标/重写失败。 |
| [eighteenth-pair-source-selector-let-failure.log](eighteenth-pair-source-selector-let-failure.log) | `0f04ff3d5a8468329d6fe9bae04d75c8844177e20d853e9b60a23a460b1a839e` | 1037 bytes / 18 lines；1 个 error：if 仍藏在 pcode/base/rest 的 let 后，split_ifs 无法直接分支。 |
| [nineteenth-pair-source-branch-scheduling-failure.log](nineteenth-pair-source-branch-scheduling-failure.log) | `c187a3e238fd4aac15038dbff0dabf111311bab551e43a75628a12fad0e63f0c` | 576 bytes / 3 lines；2 个 error：多余 bullet 中 simp 无进展，随后没有对应目标。 |

日志 bytes 均与提交、工作树及诊断记录 SHA 一致。第 17 份的 `declaration uses sorry` 和 `hsel : sorry ...` 出现在未知名字导致的 elaboration 恢复之后；源码四版本均无 `sorry`，不能将该失败日志误认成作者用 sorry 放行，也不能把后续错误减少当作模块已验收。

## 4. 最终 pin 与验收要求

Receiver SHA 链为 `8f01047a...` → `c59c6329...` → `18a9c438...` → **`46fcace4ea622a6cff8bd799b7e5a6da9ffb20ba0278ccf73865b1ea491ba9db`**。在 `669de6d` 核对 261 sources + 5 companions 共 266 项，selected SHA 全部匹配提交及审查时工作树；manifest SHA 为 `87513fefc916a22e572c9c752db33525d7a6773f089f10527146a5fbd206215d`，source guard 同步。

整个 verification tree 仍为 `879002f0dc10ca87c6c6069e13bdd7b2352cdfd2`，runner SHA 仍为 `895a8bc67d6c28e4db0ce6954344e20679cb581e3b861bafed469852d5ee5d30`。未降低 strict compile、bundled kernel replay、完整 defining-module/type/传递公理及 cache/source/object 绑定检查。本次仅写报告，未来真实主/extra archive 到达后仍须优先独立核证，未预先分配通过信用。
