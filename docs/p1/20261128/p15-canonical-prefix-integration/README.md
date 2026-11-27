# P1.5：复用原规范词支撑与首次前缀转换

已有 `P4AUpperTaggedMixedWallPayment.raw_support_iff_canonical_validSelection` 正好识别原 fixed rough support 与同一个规范降序素因子词的完整有效选择。本轮直接验收并复用这个既有实现，没有在 P1.5 下重写规范词证明。原 `P4AUpperTaggedFirstPrefixDisagreement` 同时提供真实顺序 decisionAt、实际前缀表达和原 O crossing 的首次分歧转换；该 O crossing 的分类不等于实际历史差系数的全部仿射覆盖。

原工作树依赖图需 18 个未有 Member 对象的模块。进一步查到 P3.6 提交 `8495b3b274a046060faf2ce9020b2588665634c0` 中已验收的 `P2CanonicalWallFullResidualPayment`，它移除不必要聚合 import，并保留完整残量质量和规范前缀/尾项结论。因此只需三个新的 Member 编译模块：上述 P2 模块和两个原 P4A 模块。复用 donor 的完整已提交源码及原 normal/object 指纹记录，不移植 donor 二进制，不计新增 donor 数学证明。

两个 P4A 文件只修复原标识符 universe 的同名转义、List 记号作用域、函数应用/定义展开、显式指定原 rough carrier。原声明的数学含义、量词、数值常量、support、wall 条件和 beta 定义不变。P2 原工作树前像、donor 精确源码、原验收记录及三个模块的选定源码均保存在 provenance/快照中。

## 验收

三模块各自通过原串行 Member direct Lean、精确新模块 kernel 和完整 owned 类型/Lean.Expr/宇宙/公理审计。合计 **63 个 owned 声明，其中 9 个私有声明**：P2 为 21/2，Mixed 为 11/0，Prefix 为 31/7。P2 的 21 个是原 donor 数学证明在新环境的重新验收；不是新增数学成果。全部私有和生成声明均进入审计，只有 `Classical.choice`、`Quot.sound`、`propext`。

旧 78 模块的 238 项源/对象/回执等输入前后哈希一致，旧模块 normal/kernel 次数为零。原 driver、Member guard/core、Lean/Mathlib 和 -t0 -j2 -M12288 参数不变。新输出位于独立 overlay，不改写原缓存；不声称 Lake named-target 或全导入闭包重新重放。

全部失败/成功尝试保留。Mixed 的 attempt-00001 因编辑前置检查失败误触发，重复了 attempt-00000 的同源失败，未计进展。之后将编辑和编译分开执行。Mixed 的验收依据为 attempt-00003，Prefix 为 attempt-00001；P2 首次通过。缺少独立复核时打包门按预期拒绝归档。独立只读复核无阻断，未编译或写入文件。

**完整 P1.5 仍开放。** 这三个模块提供已有支撑/前缀 API 和完整 residual wall 支付工具，未证明实际历史所有分歧均被所需有限仿射族覆盖，也未证明关于 N 一致的原子数和总标量范数、物理/自由碰撞或全域 signed medium。没有把 O compiler 的平滑系数或 beta 接入替换到历史原系数。更大的实际 OrderedThird 仿射代码依赖图未在本包中编译或计入验收。原登记保持 18/21。

[验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p15-canonical-prefix-integration-evidence.zip)

归档：590166 bytes，104 个成员，SHA-256：`26d12d29b6b2ba8646c20cd7da877fe188721ff9359763e0bf666f1b58b7e7e3`；CRC 与每个索引成员已复核。
