# pp_derivatives 源码交付

新增 `P5OccurrenceWordFourFactorLeibniz.lean`，344 行。独占目录内新增，生产模块、旧草稿及 Git index 均未改。未编译、未执行 Lean/lake 或数值 checker，正式验收信用为 0。

## 实质推进

原 PhaseB7 只有一字母的四因子导数公式，registry 明确缺任意字母串展开。本文件用真实坐标曲线的 Frechet 导数证明 occurrence derivative 的平滑性，再证明有限 list 求和可逐项微分。对四因子分配列表归纳，得到任意有序 occurrence word 的精确 Leibniz 等式，列表长度恰为 `4^r`。同一原始 owner 重复出现时保留每个字母，不用 Finset 去重。

随后用分配总长度守恒和带重数的三角不等式，证明乘积导数的点界为 `4^r * BA * BE * BP * BC`。最后 `family_four_chart_bound` 直接消费已存在 `Family.mixedEuler` 和 grouped occurrence chain：原始 ambient 的一对 `C,B` 同时适用于所有 `k ≤ kStar`、`m ≤ 6*kStar`、`r ≤ 12*kStar`，保留 `log(T+2)^B`。这里没有假定乘积本身的导数界、PP、medium 或最终上下界。

## 仍未闭合

具体 eta、psi、plateau 的统一全阶常数仍是显式三个单因子义务；本文件没有把它们标成已证明 primitive。右闭 atom plateau 与完整原始 chart 的等式、`D_T` 的紧矩形积分、Pi/EuclideanSpace 体积归一化尚需后续代码。故文件文本闭合 `complete_module=true`，原分配的完整实际 chart/D_T 任务仍为 `task_complete=false`，`ready_to_install=false`。

## 精确依赖

直接导入 `ImbalancedChen.P5OccurrenceLeibnizAllocation` 和 Mathlib；六份 source-only 依赖的路径、真实 SHA256 与拟安装路径全部写在 `REGISTRY.json`。这些源码尚不能冒称已编译生产依赖。人工读取了 pinned Mathlib 的 [chain rule 源码](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Analysis/Calculus/Deriv/Comp.lean) 核对 `HasFDerivAt.comp_hasDerivAt_of_eq` 的显式基点参数。

本次未发现原稿数学缺口，当前边界属于形式化实现衔接。
