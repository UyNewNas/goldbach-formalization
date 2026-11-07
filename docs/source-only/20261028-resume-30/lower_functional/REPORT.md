# lower_functional 源码交付

新增 `P2N48SelectedFunctionalRemainder.lean`（310 行），未编译，正式验收信用为 0。模块文本闭合；原分配的全部 lower functional 目标仍未完成。

本次补上的是原稿 `eq:current-root-functional` 第 897–905 行及第 1354–1362 行要求的实际有限行与整体负项连接。前驱 PhaseB 只有“每一行 cost ≤ 整体 coefficient”，这些逐行不等式不能相加来得到整体 cost 的上界。本文件先用原始 n48 的半开仿射坐标区间证明：两个真实 `selectedParent` 相交时，`(term,ix,iy,iz,iw)` 必须相同；term 的识别使用真实 D10 与 D11 域不交，不替换有序 simplex。`ordinal/method/floorQ` 均不属于几何 key，所以不同 source ordinal 本身不能保证不重叠。

在明确的有限 key 注入条件下，Lebesgue 积分有限可加性给出 selected row cost 精确总和。再将实际 U10 全低带与 U11 原始 E0+E1 掩码补集组成的真实 joint domain 分成 selected union 和其未覆盖补集，得到

`actualSelectedCoefficient = sum(selected row costs) + uncoveredCost`。

因此原来的 Q80/current-K 逐行 recost 可合法给出

`actualSelectedCoefficient ≤ sum(saved parent bounds) - sum(row gains) + uncoveredCost`。

文件还把已存在的实际 adopted-mask native joint harmonic 供应者直接接到这一精确分解的负号极限，没有新增 hMean、hLower 或 whole-functional 假设。原始 nonlinear sixteen-policy kernel、同一 mask 与 low U10 不掩码规则均保留；没有创建新 arithmetic owner 或改变因果策略。

未完成事项很具体：实际 `actualRetainedRows` 的 key 注入尚未执行/证明；`hMass` 和旧 switched/Q80 row checks 沿用真实逐行义务；`uncoveredCost` 仍须由其他方法、priority children 与其余有序/tied parent 的完整证书上界控制。`actualRetainedRows` 只选 method-zero 且排除 priority，本文件没有把它误称完整负域覆盖。原稿明确要求这一补集，因此这里是实现衔接缺口，不是新发现的原稿数学缺口。

直接 import 是 source-only `ImbalancedChen.P2N48ActualSelectedRhoCoefficient`；编译专员需先按 REGISTRY 中的 exact source/hash 对应安装 PhaseB、Phase4、Phase3 和原始 typed archive，再处理本模块。没有运行 Lean、lake、数值 checker 或额度检查，没有改生产文件、旧草稿、Git 或看板。
