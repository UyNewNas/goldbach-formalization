# certificate_rows 第五批交验

新增四份完整局部源码。实际k=2…6 measured moments、full Q6实际测度项、E[P]=1和原始负log二次余项均有实质源码推进；本批全目标仍 batch_target_source_complete=false，原始task_complete=false。T10的Jensen-gap尾余项期望比较和最终积分enclosure尚未闭合。全部未编译，正式信用0。

`P2Winner9SelectedAllMixedMoments.lean` 首先从真实Δ8单项式law证明任意独立有理稀疏多项式的真实积分等于系数加权factorial和。随后每行k=0…6的实物理整数数据分别构造gap·Y^k·b²多项式，和原始signed convolution是两个独立对象；具体相等性为闭合、未执行的有限算术证明项。由此两行全部70项的canonical/physical measured formulas、binomial归一化及完整Q6接到真实积分，保留U^k、L²、gd和Jacobian。

`P2Winner9SelectedPhysicalMeans.lean` 用独立二次多项式积分构造实际gap mass、原始stored factor means及E[P]=1，给出真实物理期望与canonical expectation相等，完整Q6对应实际同support上的70个weighted integrals。没有把E[P]=1或means当原始前提。

`P2Winner9SelectedAnalyticRemainders.lean` 对真实负log余项显式求导，导数为(t-P)(V²-Pt)/(PtV²)，利用两个正端点均不超过V分别处理t在P左右的单调性，从而推导原始二次下界。随后证明十因子的线性项点态抵消并指数化，得到真正pointwise reciprocal-product quadratic bound。该文件另以有限多项式恒等式证明degree10 binomial点态余项非负，但明确没有把这较弱结论当作T10 Jensen-gap期望结论。

`P2Winner9SelectedPhysicalQ6Floor.lean` 逐字读取原始Q6两行Q80/Q96字段，给精确directed cross-product证明项，把原floor接同一typed T10和真实measured Q6表达式，并从实际Y>=0、gap>=0、square>=0推导Q6非负。所有新的closed decision均未执行，没有数值成功声明。

剩余最关键一步是T10尾余项的凸性/Jensen期望比较，以及J_T与实际mass/mean乘积对应后进行完整积分enclosure。仅有pointwise finite-binomial minorant不能推出1+T10，代码与登记均保留这个边界。完整policy licence、all22/all17572和c/K仍OPEN。此前D及更早源码/registry/report均冻结未改；未运行Lean/lake/producer/checker/数值重放，也未查额度或派新代理。精确依赖、安装映射和raw SHA见REGISTRY.json。
