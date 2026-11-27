# P1.5：四个原数值 Medium 门模块已验收

执行此前 78 模块验收包中的后续计划，完成四个既有模块的 Member 环境验证：完整乘积尺度支撑、原十五个普通策略的数值 Medium 门、接入共同 beta 的实际 presieved 系数门，以及同一实端点整盒分组的数值门。最后一项保留原 `(boxPolicy ...).val < 15` 范围，没有声称覆盖额外 W 分支。

`exists_actual_ordinary_whole_box_medium_threshold` 先固定 n、eta、共同 beta 参数、图常数与 kappa/trim，再给出一个阈值。全部 N、x、HB U、所查询的实际 selected box、完整实端点向量、粗糙词长度 r、向量 v 和 roughWidth 都在阈值之后量化。它复用同一整盒端点分组，将完整 beta 端点接入第三组，得到原四项严格 `NumericGates`；没有将待证门条件换成假设。原 rough cube gates、端点 padding、全部正 trim 条件和 N^(7/32) residue 保留。

`P5ZU1011SameRhoCompleteScaleSupport` 保留原 physical cap 153/256 和局部 ceiling 1199/2000<3/5，处理原 kappa0 许可区间；空 selected bank 按原分支处理，没有对其 1/8 默认值虚设小上界。此处只是物理支撑条件，不是系数分布结论。

## 修复与验证

所有更改均在证明体内：显式使用原 Rat 单调嵌入及 cast 归一化；对 log_pow 后产生的自然数强制转换添加 Nat.cast_ofNat；在原局部 delt、abc 和 betaEndpointFactors 的实际表达上展开。所有原定义、声明前提与结论、量词顺序、数值常量和严格大小条件不变。四个原提交源码完整保存在 provenance 中，原混合行尾保留。

四个模块全部通过原串行 Member guard 的 direct Lean、精确新模块 kernel 和完整 owned 类型/Lean.Expr/宇宙/公理审计。合计 **49 个 owned 声明，其中 13 个私有声明**；生成声明同样进入审计。各模块分别为 12/1、22/4、5/3、10/5（owned/private）。仅有 `Classical.choice`、`Quot.sound`、`propext`。

原 78 个已验收模块全部复用，238 项源/对象/回执等输入在验证前后哈希一致，旧模块 normal/kernel 次数为零。原 78 模块还只读重新核验过全部冻结记录与审计解析，没有重编译。冻结 driver、Member guard/core、Lean/Mathlib 与 -t0 -j2 -M12288 资源参数不变；本轮输出在独立 overlay，原缓存未改写。不声称 Lake named-target 或全导入闭包重放。

所有失败与成功尝试均保留。最后一个模块的 attempt-00001 因编辑脚本语法错误而意外重复了一次同源失败 normal；没有计为新增进展，已验收模块均被跳过。其后先完成独立编辑，再启动 attempt-00002 并通过。其余失败分别记录了实际 cast/表达诊断，没有覆盖旧尝试或放宽数学前提。打包前重新解析原完整审计并校验全部输入/产物/日志；缺少独立复核时打包门按预期拒绝归档。

**完整 P1.5 仍开放。** 数值门不是统一 signed distribution 界，也未识别实际历史系数为整盒原子。实际策略路径到有限整盒、原阶乘/标记重数归一化、N 之前固定的总标量范数以及物理/自由碰撞与完整有符号中段界仍待连接。按原 rough Möbius 选 beta 的次序、完整 q=ab 的 pan/.599 过滤和原 ProperPower 登记 18/21 未改。

[验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p15-medium-numeric-gates-evidence.zip)

独立只读复核无阻断。归档：1938023 bytes，134 个成员，SHA-256：`c3b8e87dcc152ff731aa5b67dc7fd988e558d1376e0a181f62a4ebede96d0aac`。CRC 与每个索引成员均已复核。
