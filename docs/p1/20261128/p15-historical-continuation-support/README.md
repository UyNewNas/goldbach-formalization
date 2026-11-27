# P1.5：实际尾词与原始粗糙支撑差的双向连接

`fibre_iff_actual_continuation` 将既有 rough owner 的 fibre 精确改写为实际公共退出路径和同一个有效尾词，不再要求预先提供 `changedRough` 或粗糙 mask 等式。原状态、奇偶性、old/fresh 的原测试分歧、尾词乘积、字面 remaining 中的次序及准入有效性仍完整保留。

`exit_continuation_word` 直接沿原 `p1SignedExitStates` 递归重建完整选词。公共路径先前选中的每一步通过双方原策略；退出位置通过准入方而未通过拒绝方；原尾词接续准入方。因此恢复的整个选词对准入方有效、对拒绝方无效。对于拒绝方可能给出的另一个同积保留词，直接复用 batch90 已验收的 `P2LowerCanonicalRetainedTrace.actual_chosen_eq_canonical` 将两词识别为同一个规范词，得到矛盾，未重写唯一分解证明。

`realized_continuation_iff_support_difference` 补齐原 `RealizedRoughContinuation` 与原始保留支撑差的逆向。`realizes_of_actual_continuation` 据此导出原 fresh-minus-old mask 和 changed 支撑成员关系。这里没有另造策略、粗糙系数或 beta；实际历史系数、按原 Möbius 选 beta 的次序及完整 q=ab 的原 pan/.599 过滤均未改变。

## 验证

`formal-00001`：normal 7.431478 秒、精确新模块 kernel 8.387653 秒、完整 owned 类型/宇宙/公理审计 7.330893 秒，全部退出 0。共 **8 个 owned 声明，0 个私有声明**，生成声明也纳入完整清单。仅有 `Classical.choice`、`Quot.sound`、`propext`。

复用四个已验收历史模块，以及 batch90 的原 P2 源文件、对象和其他产物。共 19 项复用输入前后指纹一致，旧模块 normal/kernel 命令数为 0。冻结 Member guard、审计 core、工具链、依赖和 `-t0 -j2 -M12288` 资源参数不变。验收方式是隔离输出的 direct Lean，不声称 Lake named-target 或全部导入闭包重新重放。

`formal-00000` 的原源码与执行驱动均保留；失败仅因 `Bool.and_eq_true.mp` 和 `Finset.not_mem_union.mp` 在锁定版本中不可这样调用。下一次仅修正这两处 API 表达，没有改变数学前提或结论。打包前还从原 owned 日志重跑只读解析与全部哈希检查；缺少独立复核时打包门按预期拒绝归档。

独立复核结论：无阻断。复核只读，不运行 Lean 或 kernel，也未改写源文件。

## 保持开放

**完整 P1.5 仍未闭合。** 当前是原始支持的精确连接，尚未把实际策略门区域识别为有限整盒原子，也未证明 owner 数量或绝对标量总范数在 N 之前一致固定。原阶乘/标记重数归一化、物理/自由碰撞项和全域统一 signed medium 结论仍须连接；常数与阈值仍须先于全部实际 chart/row/mode/family 索引。原 ProperPower 登记保持 **18/21**，三项 HOLD 不变。

[验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p15-historical-continuation-support-evidence.zip)

归档：385741 bytes，46 个成员。SHA-256：`1d54ae63a6f49a83a4e7836a6374f545f432657833ec7629d40d89fd0a69b254`。CRC 与每个索引成员已复核。
