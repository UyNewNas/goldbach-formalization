# 固定旧 pin 的完整类型与有界 token 适用性

这是静态名称兼容性审查，不是编译结果。全部 34 原文件先按冻结 SHA 核字节，再按完整 token 盘点；共 36 处、11 文件：`ite_eq_left` 6、`ite_eq_right` 26、`dite_eq_left` 0、`dite_eq_right` 3、`FiniteField.Polynomial.expand_card` 1。详尽 line/column/context 见 `BOUNDED_COMPAT_TOKEN_INVENTORY.json`。不匹配 `_iff` 后缀，不把 `dite` 当作 `ite` 子串；Algebra 及其余 22 个无命中文件不得改变。

固定 [Lean62eed Core](https://raw.githubusercontent.com/leanprover/lean4/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Init/Core.lean) 的四个旧名均在 public section。以下以不同变量名完整转述其参数与方向：P 是任意命题，dec 是隐式 `Decidable P`，A 是任意宇宙 u 上的 `Sort u`；P、dec、A 及分支均为隐式参数，条件证明是显式参数，源声明中显式条件证明位于隐式 A/分支参数之前。

| 旧名 | 分支类型 | 显式参数 | 结论方向 | 固定源零基行 |
|---|---|---|---|---|
| `if_pos` | left,right : A | witness : P | ite(P,left,right) = left | 1075–1078 |
| `if_neg` | left,right : A | witness : ¬P | ite(P,left,right) = right | 1080–1083 |
| `dif_pos` | left : P → A；right : ¬P → A | witness : P | dite(P,left,right) = left(witness) | 1091–1094 |
| `dif_neg` | left : P → A；right : ¬P → A | witness : ¬P | dite(P,left,right) = right(witness) | 1095–1098 |

四条都是正向消去条件分支的等式，不增加逻辑假设；显式 witness 正是原 proof 已提供或正要证明的分支条件。`dite_eq_left` 零命中，因此本轮不得为了完整性创建额外 alias 或修改任何位置。以上不是仅按相似名字猜测替代。

已逐处读现有使用上下文：

- Auxiliary 的正分支是系数条件成立，负分支是其否定；原 proof 的两段式 `rw` 后续目标正对应这些条件，L221 的非整除证明亦是负条件。
- ClassGhost、IrreducibleGhost 的正分支在代入零后使用 `rfl`，负分支已有不等于零证明；ClassValue、ExtensionDefinitions、PrimeFoundation 和 CurveTrace 同样显式提供对应非零条件。
- DicksonFiniteAlgebra 的 10 处分别提供非零系数、参数不等式、指数不等式或正自然数非零条件，均为 nondependent ite 的负分支。
- ScalarExtensionSum 的两处未显式给 witness 的 `simp only` 位于零项拆分，条件是零的自反相等；四处负分支已有 subtype property/nonzero proof。SpectralBound 的一处是 Bool 枚举求和后正分支消去。旧 `if_pos` 仍以条件为前提，静态语义和使用方向相同；本轮不声称已实际跑过这些 simp 调用。
- CarlitzRoots 的三处在展开 carlitzAlpha/carlitzBeta 的 dependent-if 后使用 `ht : t ≠ 0`，需要的正是 `dif_neg`，其结果保留该 witness 作为右分支实参，没有抹去 proof 参数或改写定义。

`expand_card` 方面：旧 [Mathlib e4c917 源码](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/FieldTheory/Finite/Basic.lean) 的完整依赖为任意 K、Field K、Fintype K、显式多项式 f；q 是 Fintype.card K。结论为其 q 倍指数展开与 f 的 q 次幂相等，方向是 expand→power。原 Auxiliary 使用反向 rw，故沿旧 lemma 仍是 power→expand，未改变原论证方向。

新 [Mathlib56a005 对照](https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/FieldTheory/Finite/Basic.lean) 的外层 namespace、假设、结论和证明体不变，只在 theorem 名加 `Polynomial.`，并保留旧名 deprecated alias。旧零基行445–451与新447–453逐行对照，证明体相同；新455–456给出 alias。改回旧名即可引用当前 pin 已有证明，不新增 lemma，不复制新版证明。

实际诊断只发生于 Auxiliary 的四个 unknown-name error；Auxiliary L221 是同文件下游隐藏命中，另 31 处在未启动文件中，仅有静态兼容性证据。本审查允许将上述精确映射作为候选差分审查的语义依据，尚未批准具体 overlay 的字节、producer restore、source/manifest 绑定或 dispatch。所有声明 headers/imports/数学前提、原 pins/profile、F1–F7、未来 full34 proof scope 仍须原样保持。
