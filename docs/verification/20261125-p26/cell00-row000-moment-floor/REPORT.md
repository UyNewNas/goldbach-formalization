# Cell00 row0：完整 Q80 / 新 Q96 的纯 prefix 数值证书

## 已完成的结果

12个新模块全部通过本地正常 Lean 编译及独立 leanchecker：1个实际数据整数编码、10个因子证书、1个最终五合取汇总。共122条显式打印theorem，axiom union仅为 `propext`、`Classical.choice`、`Quot.sound`。已有356个supplier源码及对象原样复用，没有重编；完整项目闭包368个模块。

原始row0的顶点顺序严格为 `[27,25,11,9,7,5,3,1,0]`。已经闭合证明9个gap以及10×9个deviation与原已解码顶点、原保存top的精确整数公分母编码。每个因子的degree1–6共60个实际prefix moment值、10个第一矩 `1 − means/top`、10个原保存Q80字段的精确值，以及每项Q80的下界≤与严格上界<均有Lean证明。

原十个Q80整数之和为 `3793373373731202336663`，T仍为这个整数除以2^80。旧Q96为 `6708449485921`，新Q96精确计算为 `6729532351297`，保存新值绑定到原来的 `max(old,new)`；没有删除max或用new≥old作为额外前提。

## 本轮边界

通过的是原prefix evaluator在实际原数据编码上的有限数值证书。`bridge-candidate/P2OriginalSaving19Cell00Row000OriginalFloorBridge.lean` 单独保存了连接原 `rationalMoment`、原Q96 namespace与同五合取的完整候选证明。它依赖原 `HigherMomentsPrefix` 与已有 `Q96ArithmeticBridge`，这两个对象当前不在本地数值环境，**该桥尚未编译或接受**。不能把这些纯数值等式计为原全局 `FloorChecks`、单纯形积分下界或P2.6端点已经完成。

本轮只覆盖cell00 row0。其余55行、其他12个cell、全部Archive成功guard和ownership都没有由本包证明。没有改变旧Q96、HigherMoments、Core、Consumer或其他既有FQN；没有修改主仓/P1，没有提交远端任务。也没有声明P1严格all-owned审计已经完成。

## 稿件与接口

依据release-20261106英文numerical-appendix的 `num:simplex-moment`（177–196行），来自 `chen-imbalanced-semiprimes` commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`；完整文件SHA见FINAL_RESULT.json。稿件明确的是单纯形单项式积分公式。本包不声称稿中显式给出新的prefix或Newton定理，而是复用既有有限表示接口：

- `P2Winner9HomogeneousRecurrence.prefixCoefficients` 及原正确性；源码 `4234d0cc…`、对象 `125f9299…`。
- `P2OriginalSaving19PrefixInterface.prefixCoefficient_cast_eq`；源码 `7372895e…`、对象 `0e086c10…`。
- `P2OriginalSaving19PrefixMoments.normalizedMoment`；源码 `f9ae192d…`、对象 `82a3d6a1…`。
- 待接语义桥直接调用 `HigherMomentsPrefix.normalizedMoment_eq_encoded`，没有另写高矩或递推证明。

prefixMoment只对本任务所需degree1–6声明真实moment语义；原Q80 gapEvaluator恰只用这些次数。高于6的函数值没有被当作高阶矩。所有数组来自已过的actual row/vertex绑定与Moment00Shape；`row_ids_and_floor_sizes_bounded 0`保留原10个floor槽，Fin10索引不会选默认值。整数编码中的零是实际gap等式的结论，没有省略顶点或项。

## 保留原五项 FloorChecks

| 原义务 | 本包状态 |
|---|---|
| 10个第一矩等于1−means/top | all_first_moments，prefix表示下已过 |
| 10个保存Q80等于精确factorFloorQ80 | all_saved_Q80，另有all_Q80_bounds明确≤/< |
| moment old Q96等于geometry Jensen floor | 复用已过 moment_old_matches_geometry |
| moment old Q96等于旧evaluator floor | 复用已过 moment_old_eq_evaluator |
| 保存new Q96等于max旧/新evaluator | saved_new_Q96_max，prefix表示下已过 |

最终 `prefix_floor_checks` 不带任何guard成功假设。原rationalMoment版本的 `original_floor_formula` 保存在未编译桥中，不能继承这张表的已过状态。

## 验证与失败保留

所有新owner预算保持4GiB、180秒、单线程。成功normal累计 33.758s，kernel累计 33.434s；最大采样RSS 2,763,128,832B（约 2.573GiB）。完整命令、源/object/依赖前后hash、原geometry00与moment00输入前后hash、日志和回执均保留。

唯一失败是汇总 `assemble-v1`：轻量imports缺少 `Finset.sum_div`，另有一个闭合整数到有理数转换尚未化简。失败无olean；编译器错误恢复输出不被接受。最小修复仅增加已有缓存 `Mathlib.Algebra.BigOperators.Field` import和一行norm_num；未下载/重建Mathlib，未重编任何通过的11个owner或supplier。`assemble-v2`正常和kernel都通过。因子证书有无害的unused-simp提示，已过源码保持冻结，不为去警告重复编译。

## 文件与发布范围

`PUBLICATION_SOURCES.json` 是12个新编译owner的精确白名单；`PUBLICATION_FILES.json`另列source-only桥路径。SOURCE_MANIFEST绑定每个新source/object/normal/kernel；FULL_SOURCE_CLOSURE给出368项目源码、import、对象与复用来源；VALIDATION完整保留成功和失败。父代理可以按精确白名单整合源码，不需要重建356个supplier。

独立只读审查来自 `/root/p26_manuscript_audit`，见review目录；它核查了实际编码、factor00样本、10因子汇总与原式桥，不把只读审查当作数值编译，也不声称自己复算全部十组数字。生成器中的Python Fraction仅产生候选字面量；全部数值结论来自上述Lean证明，host metadata没有进入任何定理前提。
