# 全部 36 个黄色节点任务单

36 个黄色节点逐项设任务。其中 13 个实际叶任务负责完整数学或工程义务，23 个父任务负责依赖汇总与总装验收。父子任务复用同一证明。

当前环境最多同时运行 3 个子代理。等待运行名额与已实际派发分开登记；遇到精确上游依赖时保留负责人，释放运行名额给其他叶。局部源码或引理完成不构成整叶完成。

每个节点的完整剩余义务及直接黄色依赖保存在 [ALL_YELLOW_TASKS.json](ALL_YELLOW_TASKS.json)。下表是该合同的调度摘要。

| 负责人任务 | 节点 | 类型 | 完整职责 | 显式模型／推理 | 调度状态 |
|---|---|---|---|---|---|
| y13_main_assembly | `goldbach` | 父级汇总 | Goldbach 1+1.74817 | gpt-6.2-astra / high | 等待运行名额 |
| y01_gain_reserves | `P1` | 父级汇总 | 原始因果first-exit树与历史选择器 | gpt-6.2-astra / max | 执行中 |
| y01_gain_reserves | `P1.4` | 父级汇总 | 第五层真实数据认证、完整几何许可与动态owner绑定 | gpt-6.2-astra / max | 执行中 |
| y01_gain_reserves | `P1.4.child-7` | 父级汇总 | 原始第三层owner和动态Q3/Q4 parent绑定 | gpt-6.2-astra / max | 执行中 |
| y01_gain_reserves | `P1.4.child-7.child-4` | 父级汇总 | 完整87域的实际动态parent、共同历史与原策略成员供应 | gpt-6.2-astra / max | 执行中 |
| y01_gain_reserves | `P1.4.child-7.child-4.child-13` | 父级汇总 | 原档案signed gain与数值saving搬运、实际核/素数均值误差及独立reserve付款 | gpt-6.2-astra / max | 执行中 |
| y01_gain_reserves | `P1.4.child-7.child-4.child-13.remaining` | 实际叶 | 原增益搬运与剩余误差、预留支付 | gpt-6.2-astra / max | 执行中 |
| y02_full87_verification | `P1.4.child-7.child-4.child-14` | 实际叶 | 同源闭包编译、kernel replay、传递公理检查与独立复核 | gpt-6.2-sol / high | 已定位阻塞，保留任务 |
| y03_w1w2_gamma | `P2` | 父级汇总 | 数值证书与真实解析积分绑定 | gpt-6.2-astra / max | 等待精确上游依赖 |
| y03_w1w2_gamma | `P2.9` | 父级汇总 | 17,572行实际数据链：计算层已闭合，解析许可仍待供给 | gpt-6.2-astra / max | 等待精确上游依赖 |
| y03_w1w2_gamma | `P2.9.child-5` | 父级汇总 | 实际 bank 端点解析许可／积分语义供应 | gpt-6.2-astra / max | 等待精确上游依赖 |
| y03_w1w2_gamma | `P2.9.child-5.child-9` | 父级汇总 | 完整causal marks与W1/W2 carrier识别、Gamma5实际付款、Gamma9–15成本及旧计数许可 | gpt-6.2-astra / max | 等待精确上游依赖 |
| y03_w1w2_gamma | `P2.9.child-5.child-9.remaining` | 实际叶 | 完整 W1/W2 因果载体与 Gamma 许可 | gpt-6.2-astra / max | 等待精确上游依赖 |
| y06_same_rho_pp | `P3` | 父级汇总 | 强移动剩余类分布与谱估计 | gpt-6.2-astra / max | 执行中 |
| y04_spectral_732 | `P3.5` | 父级汇总 | 原始全物理范围的统一7/32小核估计与总装 | gpt-6.2-astra / max | 已定位阻塞，保留任务 |
| y04_spectral_732 | `P3.5.child-7` | 实际叶 | 真实normalized trace/Fourier乘积、完整连续谱/ABL/gap及含全部费用的统一7/32能量 | gpt-6.2-astra / max | 已定位阻塞，保留任务 |
| y06_same_rho_pp | `P3.6` | 父级汇总 | 把估计实例化到同一rho和实际PP源族 | gpt-6.2-astra / max | 执行中 |
| y05_causal_q_mass | `P3.6.child-28` | 实际叶 | 原causal策略的共同Q覆盖、过滤补集付款、定量调和质量见证及所需稀疏正质量族供应 | gpt-6.2-astra / max | 执行中 |
| y06_same_rho_pp | `P3.6.child-30` | 实际叶 | 超出已证级别范围的高秩／增强及其他系数类、完整同rho PP总装 | gpt-6.2-astra / max | 执行中 |
| y07_uniform_upper | `P4B` | 父级汇总 | 任意实b的坏半素数上界hUpper | gpt-6.2-astra / max | 等待精确上游依赖 |
| y07_uniform_upper | `P4B.4` | 父级汇总 | 供应hdensity和hUniformPP，消除上界前提 | gpt-6.2-astra / max | 等待精确上游依赖 |
| y07_uniform_upper | `P4B.4.remaining` | 实际叶 | 完整 hUniformPP 供应与同 rho 上界总装 | gpt-6.2-astra / max | 等待精确上游依赖 |
| y12_lower_assembly | `P5` | 父级汇总 | 十一项Chen均值与hLower | gpt-6.2-astra / max | 等待运行名额 |
| y12_lower_assembly | `P5.6` | 父级汇总 | 供应八组原始causal估计并闭合hLower | gpt-6.2-astra / max | 等待运行名额 |
| y08_member_policy | `P5.6.child-2` | 父级汇总 | h34：U3+U4组合上界的接口与适配 | gpt-6.2-astra / max | 等待运行名额 |
| y08_member_policy | `P5.6.child-2.child-8` | 父级汇总 | 全Member proper/equality层质量、全native域误差、完整外层Theta与immutable430/441共同realization | gpt-6.2-astra / max | 等待运行名额 |
| y08_member_policy | `P5.6.child-2.child-8.child-12` | 父级汇总 | 把完整原始U3/U4 selected-count历史、代数映射、正权重、owner及完整／selected继承过滤条件绑定到Member子族，落实完整实例许可 | gpt-6.2-astra / max | 等待运行名额 |
| y08_member_policy | `P5.6.child-2.child-8.child-12.remaining` | 实际叶 | 完整 Member 实例与原策略许可 | gpt-6.2-astra / max | 等待运行名额 |
| y09_w1w2_exceptions | `P5.6.child-2.child-8.child-13` | 父级汇总 | 原W1/W2窗口与严格fresh子载体之间的端点、repeat及selected异常衔接与统一付款 | gpt-6.2-astra / max | 等待运行名额 |
| y09_w1w2_exceptions | `P5.6.child-2.child-8.child-13.remaining` | 实际叶 | W1/W2 异常衔接与剩余分析付款 | gpt-6.2-astra / max | 等待运行名额 |
| y10_bank_semantics | `P5.6.child-2.child-8.child-14` | 实际叶 | 全部bank逐项舍入权重、point读取及candidate→profile/基项比较，解析seed/count与同rho PP许可 | gpt-6.2-sol / high | 等待运行名额 |
| y11_history_430_11 | `P5.6.child-2.child-8.child-15` | 父级汇总 | 全native-history的proper/equality/inherit质量控制、外层积分—Theta—计数对应与430+11层共同嵌套因果细化 | gpt-6.2-astra / max | 等待运行名额 |
| y11_history_430_11 | `P5.6.child-2.child-8.child-15.remaining` | 实际叶 | 全历史质量控制与 430+11 共同实例 | gpt-6.2-astra / max | 等待运行名额 |
| y12_lower_assembly | `P5.6.child-9` | 实际叶 | 把八组真实供应闭合到同一原始实例 | gpt-6.2-astra / max | 等待运行名额 |
| y13_main_assembly | `P6` | 父级汇总 | 定理1.1、推论1.2与最终集成 | gpt-6.2-astra / high | 等待运行名额 |
| y13_main_assembly | `P6.3` | 实际叶 | 消除hLower/hUpper并导出无条件主定理 | gpt-6.2-astra / high | 等待运行名额 |
