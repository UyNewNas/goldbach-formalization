# Canonical 原始 tent 子族：具体 bank 与非空真实运行

已交付 `P2OriginalCanonicalPairTentBank.lean`，607 行、55 个文本声明。原完整 adopted-plan 目标仍为 OPEN；本文件未编译，formal/kernel credit 为 0。

现有 `CandidateBank`、`pairPlan` 是参数化 receiver。原稿并不要求唯一序列化的逐前缀 plan，而是在选定误差后作有限、因果、带 buffer 的构造。此次给出该路线的一个具体 tent 子族供应：不输入任意 CandidateBank、成功 selector、accepted history 或最终 plan。所有候选来自原始 rank3/4/5 掩码全集，分别为 7、8、16 个；每个掩码先选出原 `v` 的较低 affine 片，再作自己的 full/selected square 检查，再进入有限最大选择。未把同一 tent 的较高 sibling 作为竞争者。

`bank` 的比较 floor 是初始有理 seed；到了第四、第五级，它不等于实际父值。真正的 `pairPlan` 仍按其已冻结第三、第四 cap 重测 `freshCheck`。因此较小或相等的候选严格继承真实 incoming cap。源码证明单调 cap 链及实际 `run` 的第五 cap 身份；后者本身不表示任意输入 word 被接纳。

非空实例使用 epsilon=1/100、mesh=225，真实网格步长为 1/1000。前三区间为 `[.100,.101)`、`[.080,.081)`、`[.040,.041)`；初始 cap 为 `249/448−1/1000`。选中原始 mask `{0,1}` 的左 tent，冻结 cap 为 `589/1000`。源码从实际 `exponentCode` 的半开唯一归属推得共同 code，继而证明整个正宽度 chamber 从 ordinary root 的第一 square、第二 cube 起运行 accepted，并在第三步冻结此非平凡 cap。没有把成功选择或 accepted 作为输入。

对这个具体 chamber，buffer 正、seed 大于 1/2、全/selected-complement square 及原始 selected-subproduct critical interval 都给出严格几何证明。另有每个选中 endpoint 严格低于同一原始 `VariableEnvelope.v` 源的证明。这是子族包含关系，不能把本子程序改称原稿含 W 的共同最大策略。

需要保留以下界限：

- 一般 `buffer/seed` 构造没有全局正性假设；`sourceCheck` 只是必要几何检查，未变成完整 arithmetic factorization licence。严格合法几何目前只明确供应上述 witness。
- `argument` 按已有 tent-bank constructor 保存 selected-sum midpoint。它不是实际 residual Buchstab/H/h query；本次 cap/retention 证明不使用该查询字段，尚未供应 H/h floor 的真实字典。
- W、完整 adopted L5/L6 bank、同一共同 maximum 的后续挂接、真实 native count/mean、PP/density/compiler 估计及数值 gain 都仍未完成。未声称存在某组实际素数恰落在所示 chamber。
- 所有 `decide +kernel` 和有限 `norm_num/fin_cases` 证明项均仅为未执行源码；未运行编译器、数值 replay 或大型 checker。

原稿没有在此被证伪。缺少的是完整形式化供应及后续连接；本具体子程序也没有替代原稿的整体有限逼近论证。
