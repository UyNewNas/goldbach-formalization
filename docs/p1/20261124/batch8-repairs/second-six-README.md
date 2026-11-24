# Batch6 第二组六项候选

**状态：仅源码候选，尚未编译。** 本交付没有启动 Lean、云端任务、独立内核复核或 full-owned 审核，也没有改动共享主仓库。

源码基线是 `2ab8216113394bce00f8d2d9d76de330541f1720`。六项实际失败来自同一原始 normal 日志，SHA-256 为 `ff807abaed2597bebae11e5a80990b69d097c13f6766a3238029cab04b972c61`。`MANIFEST.json` 逐项绑定拆分日志、修补前后源码与参考来源；`PATCH.diff` 给出完整改动。

## 修补及现有证明复用

| 模块 | 实际错误 | 本次候选 |
|---|---|---|
| P2OriginalInitialClosedTree | 库存整数 M/R 与根 namespace 的实函数同名；有限索引条件未归约；结论中的修正项被误泛化成任意实数 | 明确库存常量，复用现有 Fin 归约规则；结论限定到真实紧致区域修正项 |
| P2OriginalLowerSelectedCapConstructor | 分支等式改写目标后，旧 hr 的类型与反身目标不匹配 | 原存在量构造使用 rfl |
| Part3ActualWThreeCapacityRun | prefix 是保留关键字；最后三个 cast/product 证明的宽泛 simp 超过步骤数 | 将同名标识符写成 «prefix»；复用 ActualTwoCapacityGreedy 中的定向 simp only 规则 |
| P2OriginalSaving19SourceMeasure | 向量前两坐标和集合 membership 没有展开，阻止 linarith/精确引用 | change 为原 comparisonCap/newCap 减 total 的标量目标，再调用原推导 |
| P4AOriginalSecondResidualSupplier | Fin.last 1 与数字索引 1 未统一 | 局部证明 Fin.last 1 = 1，再沿用原供应引理 |
| Part3RoughWeightedPrimeMass | id 的非零目标、measure 类型和 Abel 和式下端点推断未闭；field_simp 后已有零个目标 | 显式非零证明、volume 和 m := 0；删除多余 ring |

既有工作检索记录在 `../batch6-group2-existing-search/MANIFEST.json`：52 份现成源码只有这些失败基线，没有找到可直接替换的已验完整版本。Fin 归约沿用已完成 normal 的 `P2OriginalFourteenUniformResidual` 中现有模式；cast/product 沿用 `ActualTwoCapacityGreedy`。Abel API 对照精确 Mathlib 提交 `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`，原文件保存在 `references/`。

## 接口核对

六项的 imports、namespace、声明名字均保留。静态比较覆盖 97 个公开定理、3 个私有定理和 59 个定义/结构/归纳定义。按 Lean 同名转义规则将 «prefix» 还原后，59 个定义体全部保留；11 个证明体改变。没有新增假设、sorry、自定义 axiom 或 native_decide。

唯一实际声明修正是 `originalCompactThirdCorrection_eq_original_seed_integrals`：旧日志明确显示 `originalCompactThirdCorrection : ℝ` 被 autoImplicit 引入。候选将它绑定到 `OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection`，即 `Part4ActualThirdFiniteDensityReserve.lean` 已有的实际积分定义；原 `originalCompactThirdCorrection_eq_sum_closedLeaves` 正是关于这个常量的定理。此处不是“声明字节未变”，而是恢复原稿所指对象。

## 手稿与待验事项

手稿 pin 为 `a988cba584d803ae2856a0de50efb582f4f3dd6a`。紧致第三积分与完整划分见 numerical-appendix 的 upper density 段；W 三槽原序过程见 coefficient-appendix 第 176–186 行；第八阶密度与 cutoff 见 argument 的 `eq:current-eighth-saving` 和 sieve-appendix 的 `sv:eighth-range`/`sv:eighth-density`；共同 lower cap 合同见 numerical-appendix 第 473–511 行；原第二阶变化见 sieve-appendix 第 183–196 行。精确定位及源哈希列于 manifest。

RoughWeightedPrimeMass 的独立 Chebyshev–Abel 界没有在手稿中以同名公式单列；它是已有 P1 依赖中的技术供应引理。本次保留该定理与 Chebyshev 输入，只修其 API/类型表达，没有扩展数学范围。

这些实际错误目前支持语法、名字绑定、类型推断和证明表达问题的分类。候选是否完成仍由下一次真实 normal 及其后内核验收决定。特别是 WThree 的旧语法错误曾阻挡后续证明展开，下一次编译可能暴露新的局部问题；此包没有提前改写未出现的错误。
