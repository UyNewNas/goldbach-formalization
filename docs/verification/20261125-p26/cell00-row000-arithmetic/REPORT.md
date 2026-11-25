# Cell00 row0：原始十项算术条件与旧 Q96 floor

## 已闭合的实际结果

本包的 12 个新 owner 均通过本地 normal 编译和独立 leanchecker，共 24 次成功调用。
最终无假设定理是 `ImbalancedChen.P2OriginalSaving19Cell00Row000.bounded_row_data_checks`：

```lean
RowNumericsPure.RowDataChecksFor
  (Geometry00BoundedAccess.boundedRowVertex (0 : Fin 56))
  (Geometry00BoundedAccess.boundedRow (0 : Fin 56))
```

命名空间缩写仅用于此报告。源码中的陈述完整绑定已通过原 parser 与真实 typed decoder
的 `concreteGeometry00`。原九个 vertex IDs 顺序为 `[27,25,11,9,7,5,3,1,0]`。
`boundedRow_eq`、`boundedRowVertex_eq` 与原有无 fallback 定理接通真实 row/vertices，
没有用外部数值计算替代原数据等式。

完整十项是：Matrix.det 非零；全部 9 点的 PhysicalQ；正 gap 总和；原体积等于
绝对行列式除以 8!；原 meanGap；全部 10 个 weighted means；全部 90 个 maxima
domination；全部 10 个 maxima attainment；精确 Jensen 有理数；原旧 Q96 整数。
行列式规范始终为 Matrix.det，证明使用已存在 fastDet 的原算法与原正确性证明。

原 moment row0 的旧 Q96 字段也已证等于 geometry row0 的 Jensen floor，并等于
同一精确 `oldFloorQ96 (massOf row) (meansOf row)`。该整数为 6708449485921。
这提供原 FloorChecks 第 3、4 项的实际有限等式；不把它误称为完整 FloorChecks。

## 源码复用与集成选择

Pure Q96 的 13 个定义、fastDet 全部算法/证明块、RowNumerics 的坐标函数和完整十合取
均来自已有源码，只作显式命名空间迁移与必要轻 import。13 个定义的原文切片和
force/determinant 块逐字比较在 REPRESENTATION_MANIFEST 与独立 review 中固定。
索引仍保留泛型 `{ι : Type*} [Fintype ι]`，未强行限制成 Fin10；fastDet 的所有
原 private helpers 仍为 private。

首版同 FQN 提取本身通过了 3 owner normal/kernel，但会使已有 heavy/Core 对象发生
公共名称冲突。它只作为诊断证据放在 diagnostic-v1，不是本轮生产候选。当前 v2
使用新命名空间，原 Q96、Winner9 heavy、MomentFloorConsumer 和 Core 源/对象均未改。
`bridge-candidate` 的 13 个 rfl 与十合取 Iff.rfl 是待单独验收的原命名空间接头，
当前明确 SOURCE_ONLY；本包没有为了这些桥重建旧分析供应商。

原稿依据是 `a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 2026-11-06 英文稿：
numerical-appendix `num:simplex-moment`（177–196 行）给出单纯形重心矩公式，
argument `eq:current-eighth-saving`（278–291 行）给出带因子 4、无 Chen quarter
或 ordering factorial 的 saving 密度。现有前缀递推和高斯消元是有限代数表示；
本包没有增加稿外分析估计。

## 复用与验证范围

最终闭包 353 个项目 owner，其中 341 个已接受 owner 原样复用、
12 个新 owner。仓内备用库存还包含既有 3 个 Prefix 对象供下一项工作，最终 row0
闭包不依赖它们。全源/对象/回执指纹在 FULL_SOURCE_CLOSURE.json，canonical 源闭包：
`596d600cdcc2091bd8fa9acd7422178c2b256b6a876decb834f8f426b68b0dda`。

运行时固定 Lean 4.33.0-rc1（62eed1db4d67327ec8120be05f1a1b0847d74561）与 Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1。每调用固定 4 GiB / 180 秒 / 1 线程，
原件、供应者 source/object、目标 source/object 在回执中逐字核对。
累计成功 normal 32.289s，独立 kernel 33.573s；峰值 normal
2782650368 B，kernel 2405249024 B。所有已打印 24 项依赖集合
仅含 propext、Classical.choice、Quot.sound；成功回执无警告或占位。

| Owner | normal 秒 | kernel 秒 | normal 峰值 B | kernel 峰值 B |
|---|---:|---:|---:|---:|
| P2OriginalLogMomentQ96ArithmeticPure | 1.701 | 1.959 | 1813651456 | 1555238912 |
| P2OriginalSaving19Cell00Row000Arithmetic | 2.980 | 2.617 | 2694066176 | 2323509248 |
| P2OriginalSaving19Cell00Row000Determinant | 2.799 | 2.998 | 2736848896 | 2376339456 |
| P2OriginalSaving19Cell00Row000Gap | 2.761 | 2.666 | 2705092608 | 2327687168 |
| P2OriginalSaving19Cell00Row000Input | 3.070 | 2.696 | 2736427008 | 2338709504 |
| P2OriginalSaving19Cell00Row000Jensen | 2.733 | 2.917 | 2696687616 | 2323578880 |
| P2OriginalSaving19Cell00Row000Maxima | 3.188 | 3.903 | 2741878784 | 2365419520 |
| P2OriginalSaving19Cell00Row000Means | 2.510 | 2.922 | 2751832064 | 2375921664 |
| P2OriginalSaving19Cell00Row000OldFloor | 2.929 | 2.707 | 2707021824 | 2333917184 |
| P2OriginalSaving19Cell00Row000Physical | 2.774 | 3.506 | 2782650368 | 2405249024 |
| P2OriginalSaving19RowNumericsPure | 2.438 | 2.780 | 2655571968 | 2274766848 |
| P2Winner9FastDetPure | 2.408 | 1.901 | 2161700864 | 1854394368 |

唯一失败是 Input 第一版 `rw` 对 Fin0 coerced 索引表达式未匹配；它不是资源超限或
数学反例。失败 source/log 原样保留，改用已有等式的 trans/congrFun 后同预算通过。
其余所有新算术 owner 首遍 normal/kernel 通过，没有重复运行已通过的 owner。

## 尚未宣称的结论

本包没有证明其它 55 行、10 个 Q80 floor、新 Q96 的 `max old new`、完整 28918
行总和、原 Archive aliases、几何 pulling/ownership 或实际 reciprocal integral 下界。
原 FloorChecks 第 1、2、5 项仍须用真实 gap/deviation 与已有 Prefix/HigherMoments
桥接完成；不能把一个 Nat 编码表直接当作原 rationalMoment。当前没有发现本 row0
算术条件的实质数学缺口；先前阻塞是导入/归约表示与源码接口问题，未证义务仍明确保留。
本地 normal/kernel 结果也不冒称 P1 strict 接受。
