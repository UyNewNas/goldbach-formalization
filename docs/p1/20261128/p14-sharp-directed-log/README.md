# P1.4：原有向对数锐界已验收

原 lower3 与 upper4 已验收：对 0≤x<1，三项正级数给出对数下界，四项加上原精确 1/9 几何尾给出上界，包含 x=0。私有导数证书证明“原有限有理上界减真实对数”的导数恰为 (4/9)·x¹⁰/(1−x²)²，由非负导数得到上界，没有替换成更粗的无权尾。

`directed_Q_lower` 保留 2<b、0≤e≤b−2，取原 a=b−e、z=e/(2(b−1)−e)、y=(a−2)/a。原分子 a·lower3(z)−e·upper4(y) 的两个系数方向不变，除以正 a·b 后得到原 Q 的下界。原生产器的展开整数分子/分母公式也保持原样。这是数值 floor 的对数供应项，未声称具体存档 floor 正确。

冻结 1106 numerical-appendix 的 num:log-enclosure 正是正项展开及按 2n+1 控制分母的几何尾。这里 n=4 对应原 1/9 尾，不使用浮点对数。

## 修复与验收

原 source4a 的实际 normal 失败日志和 source4ebc 前像均保留，二者源码哈希核实一致，因此没有重复跑未修改的失败源。仅三处证明表达修复：congr_deriv 代替 convert 的额外等式；先交叉相乘外层非零分母再清除 z 内分母；Q 恒等式先按原符号 a 消分母，再用 a=b−e。全部定义、定理前提与结论、系数、域及 CRLF 保留。

修改稿 `formal-00000` 首次通过：normal **8.785046 秒**、精确新模块 kernel **12.193834 秒**、完整 owned 类型/表达式/宇宙/公理审计 **9.092884 秒**，均退出 0。共 **35 个 owned 声明，含 1 个私有声明**；生成声明也纳入审计，仅有 `Classical.choice`、`Quot.sound`、`propext`。

原 PointwiseQ 九项源/回执/产物/日志输入前后指纹一致，旧模块 normal/kernel 次数为零。冻结 Member guard/core、Lean/Mathlib、依赖和资源参数未改；采用隔离 guarded direct Lean，不声称 Lake named-target 或全导入闭包重放。泛用回执继承 whole_P1_5_complete:false，完整 P1.4 同样未闭合。

**完整 P1.4 与 P1.5 仍开放。** 后续 Q80、生产器载荷语义、原整数 d/A/B 与 floor、Key 及完整父表 max/floor 仍须分别验证和连接；不得以这里的符号对数界替代全存档数值证书。原 ProperPower 登记 18/21 未改。

[验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p14-sharp-directed-log-evidence.zip)

独立只读复核无阻断。归档：581395 bytes，35 个成员，SHA-256：`7b30f632c3c669ce33925c67192a6439e2ce964ec3d08884e95183bae16142b4`；CRC 与每个索引成员已复核。
