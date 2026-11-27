# P1.4：原实际子盒 Q-Jensen 连接已验收

`child_Q_average_ge_saved_e` 由原整数 d=vertexD 证书给出的实际子盒 gap 积分下界，得到 Q(e) 不超过该子盒上 Q(childX) 的平均值。这里 e=d/(1024·1600·childRight₄)，原子盒、原冻结 parent picks、原 childX 和全部几何范围条件保持不变。

实际子盒测度等于已定义的 childVolume，其严格正性由原各坐标跨度得到，因此测度既非零也非无穷。原 firstF/Q 的已验收凸性与单调性直接复用；Mathlib 的积分 Jensen 用于同一个子盒及同一个函数。原 gap 积分先与 max(0,gap) 比较，再除以同一正上端点，并按实际体积归一化。没有把积分下界或所求平均值界加入假设。

原 **2<b≤4、childRight₄>0、整个闭子盒上的 childX∈[0,b−2]、d=vertexD 以及 e∈[0,b−2]** 仍全部是明确条件。本轮没有为每个实际存档 child 自动提供这些 A/B 几何证书。

## 修复与验收

复用刚验收的 `Q_convexOn_no_calculus_input` 和 `Q_monotoneOn_no_calculus_input`，不重复证明同一个 Q 的凸性和单调性。原两个重导出定理的 hconc/hmono 参数仍保留；直接使用已证的更强结论。其余修复只补齐原 exact64 child 命名空间、显式原 Point、ENNReal 记号，以及末端除法恒等式和多余 tactic。原数学定义、数值常量、区间端点及所有 theorem 条件/结论不变。

`formal-00002`：normal **9.172184 秒**、精确新模块 kernel **9.640651 秒**、完整 owned 类型/表达式/宇宙/公理审计 **8.001301 秒**，全部退出 0。共 **19 个 owned 声明，0 个私有声明**，全部生成声明也进入审计，仅有 `Classical.choice`、`Quot.sound`、`propext`。

原 PointwiseQ 和 FirstFConcavity 的源、回执、对象等输入前后指纹一致，旧模块 normal/kernel 次数为零。冻结 Member guard/core、工具链、依赖及资源参数不变，只向隔离输出写入新模块。采用 guarded direct Lean，不声称 Lake named-target 或全导入闭包重放。泛用回执内继承的 `whole_P1_5_complete:false` 不改变本轮模块明确属于 P1.4 的事实；完整 P1.4 同样未闭合。

`formal-00000` 的实际 namespace/notation/Q 表达失败以及 `formal-00001` 的末端两处表达失败均保留。缺少独立复核时打包门按预期拒绝归档。源码历史 source-only 注释保持原文，验收以明确回执和快照为准。

**完整 P1.4 仍开放。** 后续须接实际子盒积分界、完整原存档父表/Key 及全域 stored max/floor、endpoint/reserve 连接；没有重算全表排序。P1.5 的实际历史整盒原子、碰撞与统一 signed medium 也仍开放，原 ProperPower 登记 18/21 未改。

[验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p14-child-q-jensen-evidence.zip)

独立只读复核无阻断。归档：512106 bytes，55 个成员，SHA-256：`275ded3bfa0605b96192d766d61d92fc7fdfd5830805c343737331d752d4bfc7`；CRC 与每个索引成员已复核。
