# P1.5：原历史系数的完整规范词测试

原 `commonRoughSupport` 上，`rough_mask_eq_canonical_trace_difference` 将实际 fresh-minus-old rough mask 精确改写为：对同一个 `b.primeFactorsList.reverse`，从空前缀、正初态执行原 fresh 完整 `FirstExitValidSelection` 的指示函数，减去原 old 完整有效性的指示函数。它复用已有 P4A 原始支撑字典，没有重新证明规范素因子字，也没有只检查最后一个门。

`remaining_test_eq_canonical_trace_pair_sum` 把这个精确等式用于原任意复值测试函数 G 的历史 pair-sum。只改写保留 mask；原 `attachedMobius` 不变，仍先按原 μ(b) 选 beta，再乘 mask。pan 下界与严格 .599 上界继续作用于完整 q=a*b，原 actualSmallRosserSupport、union rough support 和 trueDDeltaRho 全部保留。`fibre_canonical_trace_sign` 再将完整规范词的两个指示函数差连接到同一个原 owner 的固定外部符号，不重选 beta。

导入 P4A 模块只为复用原 raw-support 字典。没有将 O compiler 的平滑系数、其 small-prime 接入、wall 估计或分类许可迁移给历史原系数。

## 验收

`formal-00000` 首次通过：normal **6.679597 秒**、精确新模块 kernel **10.530530 秒**、完整 owned 类型/表达式/宇宙/公理审计 **7.578297 秒**，均退出 0。共 **3 个 owned 声明，0 个私有声明**，全部生成声明也纳入审计，仅有 `Classical.choice`、`Quot.sound`、`propext`。

两个既有历史模块和三个刚验收的规范前缀依赖，其 15 项源/回执/对象等输入在验证前后哈希一致，旧模块 normal/kernel 次数为零。冻结 Member guard/core、工具链、依赖和资源参数不变。采用隔离输出的 guarded direct Lean，不声称 Lake named-target 或全导入闭包重新重放。缺少独立复核时打包门按预期拒绝归档；独立只读复核无阻断，未编译或写入源码。

**完整 P1.5 仍开放。** 这是原系数到同一完整规范词的精确连接；完整仿射门覆盖、有限整盒原子及其 N 之前固定的总标量范数、物理/自由碰撞和全域统一 signed medium 界仍须继续连接。原 ProperPower 登记保持 18/21，未新增替代策略或不受原稿许可的分布结论。

[验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p15-historical-canonical-trace-evidence.zip)

归档：179265 bytes，34 个成员，SHA-256：`b3895ceb13cac626c6fbcff0eae3eb718e3cb7c0de119a21c9ea2a47ca7260ca`；CRC 与每个索引成员已复核。
