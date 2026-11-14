# T02 — 精确旧 API 兼容源码独立审查

结论：**PASS_EXACT_BOUNDED_SOURCE_ONLY_COMPATIBILITY_DELTA**。允许将本次精确冻结的源码 overlay 作为独立 source-only 档案保存；不授予编译、Algebra 对象复用、R3 driver/dispatch、full34 proof、六 adapter 或完整 J 接受。没有新的阻断项。

对象为 `t01/weil34-failure-review/compat-candidate/FREEZE.json`，3883B，SHA256 `6f530a0058e4ffda0f96e8ad7e0d371aa0d8e0ee01e26fa9397383d141146266`。独立重算 15 个冻结条目的 length/SHA256/Git blob，实际集合恰为这 15 文件加 FREEZE，共 16 文件。具体允许字节见本目录 `ALLOWLIST.json`，详细重算结果见 `EXACT_SOURCE_METADATA_REVIEW.json`。

## 只发生了已批准的 36 个引用替换

我从上一轮独立生成的 36 个原 source line/column/token 位置出发，在内存中按原坐标只作规定替换，再将所得每个完整文件与实际候选逐字比较；11 文件全部一致。重新生成的 unified diff 与作者 `EXACT_COMPAT.patch` 原始 bytes 完全相等。没有依赖作者报告来推断差分范围，没有执行或 import 候选代码。

| 原名字 → 固定旧 pin 名字 | 精确数量 |
|---|---:|
| `ite_eq_left` → `if_pos` | 6 |
| `ite_eq_right` → `if_neg` | 26 |
| `dite_eq_left` → `dif_pos` | 0 |
| `dite_eq_right` → `dif_neg` | 3 |
| `FiniteField.Polynomial.expand_card` → `FiniteField.expand_card` | 1 |

数量是 4 处实际 unknown-name 诊断、Auxiliary:221 的 1 处下游隐藏同族位置，以及未启动模块中的 31 处静态同族命中；分类及坐标逐项一致。无 `_iff` 或其他近名替换，没有把 `dite` 当作 `ite` 子串，也没有添加泛 alias。

34 个原文件全量再次匹配已审 dca6 source manifest 及真实 Git blob 字节。23 个无命中文件未复制到 overlay；包含已编译成功的 Algebra，原字节仍为 10882B / SHA `19e52ee1833944e6ade8dbb42d7d8e1a19ebfae8e911bed84b7121e8bb38b3a3`。11 个修改文件各自有独立 old preimage 与新 candidate bytes/hash/blob，不能把新字节标作 dca6 原源。

## 声明、imports 和数学引用

全部改变都位于现有 proof body。134 条作者 declaration metadata 记录独立重算匹配；其中 `dickson_one_eval_add_of_mul` 是 equation-style declaration，作者该条 hash 实际覆盖完整最后声明及 namespace 尾部，范围比 header 更宽，这整段也逐字未变。结合完整文件只含 36 个已知 body 替换的结果，所有声明名、类型、参数、假设、结论、imports、module 模式、namespace、options、归一化相关内容均未变。没有新增 theorem/lemma/axiom、数学前提或数学证明路线。

逐处替换与上一轮签署的 `PINNED_API_COMPATIBILITY_REVIEW.md`（SHA `d83e77ef1106c9104773a2e034989a526cd3c784304ea94b9abbcfb8fe4ec53d`）相同；该报告已核固定 Lean62eed 四旧名的完整参数、显式条件 witness、任意 Sort 宇宙、等式方向及全部实际使用上下文。本轮读完整候选 diff 后确认没有改变 witness、rewrite 方向或 `simp only` 的其余列表。静态适用性成立，未声称 tactic/elaboration 已执行。

旧 e4c917 的 `FiniteField.expand_card` 与新 56a005 的 namespace-prefixed 名称具有相同 Field/Fintype 假设、等式和证明体；Auxiliary 仍作同向的反向 rewrite，只引用旧 pin 中现成的 theorem。没有搬运或重写新版本 proof，没有重新形式化外部 Weil，也未将上游 4.35 成功换算成项目 4.33 成功。固定源码依据为 [Lean62eed Core](https://raw.githubusercontent.com/leanprover/lean4/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Init/Core.lean)、[Mathlib e4c917](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/FieldTheory/Finite/Basic.lean) 和 [Mathlib56a005](https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/FieldTheory/Finite/Basic.lean)；本轮复用上轮固定源阅读，不重复 GET。

## 原档案和后续边界

各文件的原 copyright/Apache-2.0 文字头、作者和出处说明保留。原上游 LICENSE 未动，11358B / SHA `c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c`；原 dca6/上游 `5dd712…` source 档案不被覆盖。overlay 的 `SOURCE_OVERRIDES.json` 明确保留原 source anchor、独立 candidate identity 和尚未发布的状态；后续发布应保存这一 provenance 和原 LICENSE 的关联，不能宣称候选仍是上游原字节。

本冻结集合没有 workflow、driver、profile、package pin、cache/producer/admission/helper 改动。原 487B profile、Lean4.33/e4c917、F1–F7 的证明与保留门禁继续适用。发布源码档案不使这些源自动获得 runner admission；实际 source/manifest/install identity、未来 R3 driver，以及 Algebra 原 producer 的真实物理 payload/reuse 资格另行独立审查。

本轮没有本地 Lean/Lake/LSP/helper/fixture/环境执行，没有 artifact 下载、Git/GH 写入或派发。完整 34 的 private/owner/serialized 库存、两种 full types、direct AX/raw safety、fresh native kernel 和 retention 未完成；全部六 adapter + 真实完整项目依赖闭包及 J 保持 HOLD。28 green / 242 blue / 29 yellow / 0 red 不变，proof/goal 信用增量为 0。
