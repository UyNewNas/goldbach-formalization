# F certificate_triple：实际完整秩 W1 源到原 PP 接口

本批完成局部源码连接，完整派发目标仍未完成。`task_complete=false`、`goal_complete=false`、`batch_target_complete=false`、`batch_target_source_complete=false`；仅 `local_step_complete=true`。两份 Lean 均未编译、未运行 checker，形式化信用为 0。

`P2W1ConcreteRankPrimeProductReceiver.lean` 使用 E 独立构造的真实 `arithmeticLabels=(q1,q2,q3,n)`，按完整词 `old ++ [q1,q2,q3] ++ primeFactorsList(n)` 的长度取 `rankSource`。它把全部旧词、三处有序标签与每个尾部素数槽编码进现有 `Part3.labelledPrimeTuples`。总函数里的 min 截断仅使定义处处有值；`tuple_val` 从真实乘积 `<N` 和正旧乘积证明源上不发生截断，也不读默认槽。

`primeWord_injective` 先消去相同 old 前缀，再逐一恢复 q1/q2/q3，最后以尾部 primeFactorsList 的精确乘积恢复 n。因此 `tuple_injective_on_source` 是由真实源证明的元组编码单射；没有声称乘积映射单射，等乘积的不同标签仍分别计数。`n=1` 与尾部重素数保留。

`family_test` 给真实源到元组族的精确有限测试求和，`rank_primeMass_eq_tuple` 和 `source_primeMass_eq_rank_tuple_sum` 给原 additive-prime 计数的完整秩分解。`actual_W1_count_le_rank_tuple_sum` 从 E 的真实冻结 receiver 三槽计数出发，只用非负 sigma 去掉 receiver 后交给这批具体元组族；没有把一个任意正源宣布为已许可。D/E 的实际 singleton history/mask 定理仍可直接用于这些原 old、Q、E、i/j。

`rank_distribution_eq_actualPP` 将这个真实源的 signed 分布余项严格接到原 `Part3.primeProductSignedError`。权重是具体元组像上的常量 sigma、像外为零，和待测模数没有参数依赖；`actualPPWeight_bound` 给其点态 [0,sigma] 界。互素均值保持原 `(m,q)=1`/phi(q)，same rho 没有更换。这只是精确 source dictionary，既不假设、也不证明内部 PP 解析估计。

`family_product_cap` 与 `family_fixed_power` 保留全乘积 `<N` 和原 old/window 的固定幂下界。固定幂结论的 old 因子及原 cutoff floor 前提仍明确列出。本批尚未把这些前提在全部十一 Upsilon 根上消去，也没有把单一乘积门称作完整 whole-group capacity/monomial licence。

`rank_smallPrimeMass_le` 复用现有素数元组有限重数定理，真正支付完整 rank 源中的小素数搭档：上界为 `sigma*rank^rank*z`。`source_smallPrimeMass_le` 将所有 rank 相加。总秩 R 必须界住真实源；E 已从固定 eta 的几何 floor 给出统一秩构造，但全部根上的共同 floor 仍 OPEN。这是显式有限付款，不是已经获得 currentK 或完整渐近误差结论。

`P2W1ActualSinglePairAlpha.lean` 直接读生产 `singleChildren`/`pairChildren` 的实际成员，按整数 old 乘积定义原 `alpha=(log N-log B)/log(Q/B)`。成员所给同一 Q 与正剩余 level 推出分母为正，并给出原 `1+(alpha-1)/(1-u)` 或 `1+(alpha-1)/(1-u-v)`。从旧 alpha>=2 推出新 alpha 不减，没有将其重置为 2。这没有构造原 pair 的冻结 history，也没有证明所有根的 alpha 基态。

完整 F 目标仍需：全部 single/pair/retain/argument 路径及十一原始 Upsilon 根的统一真实绑定；pair incoming cap/mask 与全 full/selected/ceiling 门；全根固定幂 floor；整组容量分配和三单项式门、共同有限混合几何/平滑许可；unsifted mass/J 与原 W1 成本；same-rho majorization、density、互素修正和内部 PP 解析估计。P1/P2/internalK/PP 均仍在内部，不以 hPP/hK/Generic Sound 作新 primitive。

lower_tail 的原 `quotientSwitched` 含 Gamma7-21 更高 arity 颜色词，本批严格三槽族没有与其全量等同；全 21 项正成本仍 OPEN。coefficient_physical 明确其 lambda6 的十一 PhysicalCell 不是十一 Upsilon 根，且没有 F 的根/容量/单项式许可可供消费。本批不提供 H248 增强 count。

E 最终三源、REGISTRY/REPORT 与独立 SOURCE_REVIEW_PASS 记录已逐一重核 raw SHA，保持冻结。REGISTRY 包含全部新源码 SHA、直接源/导入 SHA、安装映射、实际前提和剩余义务。源码审阅通过不表示编译或内核通过。未运行任何 Lean/lake、有限决策项、数值程序、checker、额度查询或新代理；未修改其他目录、生产或 Git。没有提出新的原稿数学缺陷。
