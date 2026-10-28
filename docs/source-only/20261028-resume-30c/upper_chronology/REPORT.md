本批交付 `P4AOriginalCell0ActualSixthParentGuard.lean`，500行、15条公开定理。未编译，formal_credit=0。局部本批目标已写成闭合源码，原 broad upper_chronology 目标仍 false/OPEN。

实质消除了前批 `selected_actual_slot16` 的外给 `CurrentParentGuard`。关键不是把实际sixth父值设成raw R：cell0的严格第34行给 A(t0)<R，而全部11个sixth PhysicalCell都要求 old first-three mask6 的tent(t1+t2)≤A(t0)。cell0 descending winner又使这个tent恰为R，两者矛盾。因此这里没有任一sixth更新适用，`sixthSourceCap` 精确继承其实际第五父cap。

上界从真实冻结值逐层推出：真实支持第三标签的Gamma≤originalThird=R，减buffer不增大；第四、第五的每个实际subset tent均由同一cell0旧63平面控制，所以其有限max也≤R。空mask单独处理，没有暗加mask非空前提，没有使用 unsupported Theta分支当成Gamma。

下界来自真实算术递归：复用已存在 `Part3.ActualRetainedAncestorTests.retained_leaf_ancestor_tests`，从真实rank8 frontier转成真实retained leaf，取rank7真实Boolean admission，读同一个冻结rank6祖先cap。其完整UpperAdmissibleSet在最小第7素数处的奇数测试给出 prod(ancestor7)·p7²<N^actualSixth。用精确log坐标字典得到H7<actualSixth。整个过程中不索取此不等式或祖先admission作为前提。

为防止把支持问题藏到一个更小的carrier，另证原先96行inner bank在原参数选择 meshStep≤chi、omega≤1/100 下已自动满足第三joint-cell与rough许可：order行控制整个闭盒的两条第三顺序门，stop上端原已保留，width就是共同step，third cutoff行给整盒t3>1/100。因此额外 `parentBoxes` 筛选在这些条件下不删除前批bank中的任何label。

最终 `original_bank_CurrentParentGuard` 和 `original_bank_slot16` 仅要求真实有限bank/frontier成员、e≥0、共同meshStep≤chi、omega≤1/100、N>1，实际rows4/licensed4/J5/rows5在全链保持同一对象。firstStop、96行、实际ancestor admission和CurrentParentGuard均不再是调用前提。

范围仍限当前实际all-eleven候选树上的cell0有限bank。尚未把它证明为全原始58/87策略，也未给其余13ascending域、后槽、统一加权误差、密度telescope、same-rho、数值saving或K。源码依赖本身仍有未编译安装边界，须编译专员接续。未发现原稿新的数学缺口；未运行Lean/lake、checker、额度检查或子代理。
