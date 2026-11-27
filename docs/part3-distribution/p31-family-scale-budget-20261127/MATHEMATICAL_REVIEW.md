# P3.1 数学与源码独立审查

审查基线为 `96d8c62edc5f8e4c196441ab680bcf34b1dcbe8a`。审查对象是 `ImbalancedChen/Part3ActualFamilyScaleBudget.lean`（初稿 SHA256 `ba56fc2d1683e92d4076149784ef46d5e565fc59dc851817f1946e2a8bb1ec0a`）与 `ImbalancedChen/Part3ActualModeUniformTail.lean`（`bc4236973376292b6237b5255f495bfda5f636d573073a3d64b56a2d3d6c1f66`）。以下行号指此初稿。仅审查数学、来源、作用域及可从文本识别的 Lean 书写问题。编译、内核重放和公理审计归另行验证。

## 结论及问题等级

- **Critical**：未发现。
- **Important**：未发现数学或规格阻断项。
- **Minor**：`Part3ActualModeUniformTail.lean:96` 中的 `rw [sub_eq_add_neg, Real.rpow_add hxpos]` 依赖重写搜索顺序。等式左边已含 `x ^ (19 + 2 * eta)`，比右边新产生的整个指数和更早满足该通配模式。建议给第二条 rewrite 显式传入 `(19 + 2 * eta)` 和 `(-(epsilon * ((r - 1 : ℕ) : ℝ)))`，以便展开目标幂，随后 `ring` 只需结合交换数值因子。这是静态定位提示，未观测到该行的 compiler diagnostic。
- **规格符合性**：本轮“实际物理尺度的多项式预算 + 统一单模态尾”符合计划。**数学质量**：通过。**实现质量**：所用供应方、对象、端点和量词与证明意图一致，建议使上述重写稳健。编译验收应引用独立回执。

## 独立核对

| 项目 | 可复核的位置和结果 |
|---|---|
| 原始材料及命名 | 逐一对 F1/F2/S6 三个完整供体文件核对 Git blob 和 SHA256，并将来源 JSON 中全部 9 个原始片段逐字节对照各自原件。F2 的两个助手在预算模块 27–39 行保持原文。F1 的几何结论（142–189）在 49–96 行仅改变私有性和外层命名空间。S6 的 B/C 在 19、21 行保留原定义和 namespace；F 在既有 `Part3ActualNonzeroSourceCore.lean:34`，无重声明。 |
| 稿本定位 | 独立核算 45,951 字节数学附录 SHA256 为 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`，Git blob 为 `7cf3bbb16cd8924565eb439e474e0674f04631da`。行 678–693 的稿内 D 是 b 上平滑长度，对应这里的物理 B，不是自然数标签 D。行 700–703 对非零 m 使用公共阈值及一个充分大的固定阶数。行 673–674 的谱层 Z 与 F1 行 726–728 的物理 h 频率乘数有不同意义。 |
| 几何与分母 | `Part3DistributionTargets.lean:126` 给出 U,V,Qᵢ≥1 和实际单项式不等式。预算模块 49–96 从中及 σ>0 得各长度≤x。118–129 在 g=0 或 D=0 时 F=0，其余分母≥1。131–150 在 glD=0 时 C=0，正分母≥1。152–187 在 D=0 时 H=ceil(0)=0，余下的自然分母和 V 的乘积≥1。δ 仅通过 D/δ 进入 quotient carrier，既有 `Part3ActualLabelBudgetCardinality.lean:81` 对包括零在内的任意 q 成立。预算不需要标签上界，也不跳过任何零标签。 |
| 闭区间及系数 | `Part3ActualLabelBudgetCardinality.lean:94,127` 对完整整数闭区间给出 2F+1，F=0 时仍容许单点。两个有序的 quotient/h 标签给平方，分别用 Q₂+1 与 2H 控制。预算模块 189–234 的估算为 C²≤x⁶、2F+1≤3x、Q₂+1≤2x、2H≤130 Z x⁵，故总界为 3×(2×130)² Z²x¹⁹=202800 x^(19+2η)。X≥1 与 η>0 给 Z=x^η≥1，所有平方和实指数处理均有相应符号条件。 |
| 正尺度适用范围 | 预算模块 100–113 由实际长度和正自然标签推出 B,C>0；尾模块 47–55 对 D,δ,g,l>0 明列条件，保留原 `NeZero (g*l)` 参数，无自由 B/C 假设。实际 fixedSlice 是独立对接，S6 行 302–309 原来由 gcd 成员关系推出 δ>0。终端没有声称已建立这样的成员关系。 |
| 单模态尾和量词 | 尾模块 29–39 取自然数 n>max(1,(19+2η+L)/ε)，r=n+1 满足要求。65–78 使用既有 `Part3ActualModeSmoothMassTail.lean:99` 的全尺度常数 A；K=6·A·10^(r−1)·202800。83–101 的指数合并为 19+2η−ε(r−1)≤−L，在 x≥1 时方向正确。105–129 的 r,K 在 atom 及 b,σ,κ,c₀、D,δ,g,l 和 tag,mode,negative,u,k 所有变化参数前给出。lam、om 是实际定义，所有界由 admissibility 和既有单模态供应方导出。 |
| 零项与六块 | `Part3ActualSmoothMassTruncation.lean:90,153,221,233` 表明 y=0 的整个 completed kernel 在截断式两侧相消；非零 y 上 m=0 保留在 truncatedKernel 内。截去的是公共窗外 m 尾。六个 (B 或 2B, C 或 2C 或 4C) 都用同一 J=ceil((C/B)x^ε)。尾模块 58–64 正是相应实际接受对象。没有从尾估计推断任何零项量级，也没有把固定块的支配不等式当成恒等式。 |
| 适用边界及冻结 | 来源文件 scope 和尾模块 12–14 明示仍需原行重组与外层 Fourier 权重求和。F1 的 e=d.cleanedAlphaAtom 与尺度保持及 admissibility 传递是接原始行时的义务，此轮对任意可容许 e 的结论并不替代该步骤。独立逐项比较前后闭包 85 个共同模块的记录，并用实际文件重算 SHA256，全部一致；本轮闭包共 87 个模块。 |

外层 Fourier 系数求和、外标签/权重、从固定切片导出正性、清洗 atom 的识别，以及向完整 signed medium error 的回接仍由后续原始行论证承担。本次审查没有发现另需引入的分析假设。
