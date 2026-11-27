# P1.4：原实际整子盒 Jensen 积分界已验收

`integral_frozenUpperPositiveKernel_ge_child_Jensen` 将上一轮的子盒平均值桥接到同一实际整子盒上的原冻结正部核积分下界。原 parent picks、grid1600 子盒、实际移动 own-cube 门控 profile 和原 32 顶点 gap 始终相同，没有把 U_P 换成常数。

原条件保留：五个子盒左端点严格为正、2<b≤4、整闭子盒上的实际新 residual≤b、0≤d 和同一个 d=vertexD 证书。从这些条件推导 childX、局部正部 gap/t₅ 和保存值 e 的合法范围，再建立实际移动 profile 的连续性、核的可积性和子盒固定端点前因子比较，最后结合原 Jensen 平均值界与逐点核界。所求积分界、Q 输入范围和 profile 可积性均由证明得出。

整数尺度也精确保留：e=d/(1024·h₅)，整子盒体积乘前因子等于 4·1600·∏width/(h₅·∏hᵢ)。这些算术恒等式不自行认证全部存档 d 值或几何 guard。

## 修复与验收

相对 fbf182411 原码，只调整四处证明表达：mul_div_assoc 代替 convert 的除法目标；使用锁定版本的正因子消去 API；显式展开 profile 函数应用；先用已验收 child_span，再展开 childRight，避免丢失跨度恒等式。全部定义、定理前提与结论、数值常量、区间及 CRLF 保留。

`formal-00001`：normal **8.633598 秒**、精确新模块 kernel **8.783466 秒**、完整 owned 类型/表达式/宇宙/公理审计 **7.822736 秒**，均退出 0。共 **35 个 owned 声明，0 个私有声明**；全部生成声明纳入审计，仅依赖 `Classical.choice`、`Quot.sound`、`propext`。

原 PointwiseQ、FirstFConcavity 和 ChildQJensen 的 15 项源、回执、对象等复用输入前后哈希一致，旧模块 normal/kernel 次数为零。冻结 Member guard/core、工具链、依赖和资源参数不变；采用隔离输出的 guarded direct Lean，不声称 Lake named-target 或全导入闭包重放。泛用回执继承的 whole_P1_5_complete:false 不改变本模块属于 P1.4 的事实；完整 P1.4 同样未闭合。

首次失败源码、完整日志与执行驱动均保留。缺少独立复核时打包门按预期拒绝归档；独立只读复核无阻断，未编译或写入源码。历史 source-only 注释保留，以已冻结验收回执为正式状态。

**完整 P1.4 仍开放。** 尚须对原存档各子盒落实几何条件和 d 证书，完成 Key、完整 stored-parent max/floor 及 endpoint/reserve 连接；没有重跑全表排序。P1.5 的实际历史整盒识别、碰撞与统一 signed medium 仍开放，原登记 18/21 未改。

[验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p14-actual-child-jensen-integral-evidence.zip)

归档：516080 bytes，44 个成员，SHA-256：`def00f238b496d45b770d7a9eac7a1f8c45fc81658a79b61ad6d6ad516711b65`；CRC 与每个索引成员已复核。
