# upper_jensen 第二批交付

新增两个模块，共422行、24项声明（含私有端点算术引理），只写本任务目录。第一批文件冻结未改；未调用 Lean/lake、数值 checker 或内核审计，正式信用为0。

`P5OldFifthActualChildJensenIntegral.lean` 完成实际 grid1600 半开 child 的整体 Jensen 积分衔接。保留同一个 raw 行、parent-fixed 十五平面 picks、原始严格 own-cube gate 和实际 `frozenGap`。输入仅为可由字面几何供应的正坐标、closed-child 残量比上界、`2<b≤4`、`d≥0` 及 `d=vertexD`。从 `g=M−max(U_P,S+2t5)` 推出 `g_+≤(b−2)t5`，再由 `t5≤T` 得到 `X=g_+/T` 和局部比 `g_+/t5` 的所有 Q 取值范围。结合已写的32个实际顶点 gap 积分，还推导 `e=d/(1024*1600*T)` 的合法范围。因此新结论没有把 `hXrange`、`he`、目标积分、凹性或均值下界当新假设。

积分使用原有 normalized uniform-child Jensen，并消费第一批已证明的 firstF 凹性、单调性。另对真正 moving strict-gate profile 使用已有全局连续零扩张，证明 `frozenUpperPositiveKernel` 在闭 child 连续、在实际半开 child 可积。每个倒数坐标由 child 上端点控制，得到

`∫_C frozenUpperPositiveKernel ≥ childVolume * childPrefactor * Q_b(e)`。

常数振幅和 e 都给出精确 grid1600 整数尺度等式：`V*childPrefactor=4*1600*prod(width)/(h5*prod(h_i))`，`e=d/(1024*h5)`。这是原稿 whole-child bound (J) 的分析部分。

`P5NamedFifthChildJensenInstances.lean` 直接消费另一代理冻结的 `P5NamedFifthPayloadSemantics`（SHA `1dacad69…143244c`），形成两个无额外前提的实际 child 归一化 Q 平均值及正部核积分实例。parent0 的 `(b,e)=(4,233/808)`、child d=29824；parent1 的 `(b,e)=(399/100,393/1616)`、child d=25152。所有 source picks、正坐标、closed-child 比率和顶点 d 前提均由字面源证明供应。原 grid400 parent 的 d=5984/5232 没有被套用到 grid1600 child。

依赖文件路径、SHA、消费声明与安装模块名均登记在 `REGISTRY.json`。两个实例属于 whole-child、unbuffered、positive frozen-parent surrogate；仍未把它们等同被真实 selected-owner 剪裁后的贡献。owner clipping-loss、所有行/child覆盖、atanh有理对数floor、Q80整数floor、汇总 reserves 与当前K仍开放。没有发现新的原稿数学缺口；这是已知内部实现衔接的推进。广义原任务 `task_complete=false`，本轮窄步骤 `local_step_complete=true`。
