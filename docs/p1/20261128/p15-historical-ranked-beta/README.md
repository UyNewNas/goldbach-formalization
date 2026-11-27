# P1.5 原历史系数：固定粗糙阶数与原 beta 选择

新的有限连接已通过原 Member guard 下的正常编译、精确新模块内核重放，以及全部 owned 声明的完整类型、公理审计。共有 **16 个 owned 声明，含 1 个私有声明**，传递公理仅为 `Classical.choice`、`Quot.sound`、`propext`。

对原 `commonRoughSupport` 中同一个粗糙因子 b，其 Möbius 值正是规范完整素因子字长度的符号 `(-1)^roughRank b`。原小 Rosser 成员只由这个符号决定；之后才乘上 fresh-minus-old 的 owner 掩码。

若原完整模数 a*b 属于 `remainingModuli`，复用已接受的 P4A 粗糙素因子乘积下界，得到 `roughRank b ≤ floor((599/1000)/rho)`。固定 rho 后，此界在 N 之前确定。原 pan 下界和严格的完整模数 `.599` 上界均未改变。

先从每个原 owner fibre 中剔除没有任何原小因子能通过完整过滤的零行，再按上述有限秩分区。最终 `remaining_test_eq_ranked_owner_sum` 对任意复数算术测试 G 保持原 `trueDDeltaRho` 精确求和：owner 掩码与秩 Möbius 是两个固定外部标量；内部 beta 的选择只看原秩 Möbius，绝不先乘掩码再选。没有换成 joint/presieved 系数，没有取绝对值和，也没有改动小素数附着。

`ranked_word_realization` 保留同一个 b 的规范字、同一个实际前缀和 tail，并给出 `r = prefix.length + tail.length`。tail 仍在原状态的 `remaining` 内，原 old/fresh 实际准入有效性不变。

这对应冻结 1106 系数附录的固定粗糙阶数、带符号原子与唯一小/粗糙分解。通用乘积下界直接复用 P4A；规范字和 rough owner 直接复用本分支此前已验收模块，没有重写这些证明。

## 验证与保留尝试

- `formal-00000`：最终 fibre 求和中隐式 cap 无法推断。精确源和驱动保留。
- `formal-00001`：只剩实数幂转为复数幂的转换。精确源和驱动保留。
- `formal-00002`：补显式 cap 与 `Complex.ofReal_pow` 后，normal 8.246490 秒、kernel 8.739907 秒、owned audit 7.395725 秒，全部退出 0。两处失败均为形式化表达问题，数学前提和结论未修改。

复用 residual、rough owner、canonical owner 三个已验收模块的源、对象与回执，并将 P4A 对象绑定到上一批 78 模块验收保留的原 Member 边界指纹。输入前后哈希一致，旧模块 normal/kernel 次数为 0。原冻结 helper、guard/core、依赖和编译资源参数不变。这是隔离输出的 direct Lean 验收，未声称 Lake named-target 或全导入闭包重放。

## 仍然开放的范围

**完整 P1.5 尚未闭合。** 本轮只有秩标签的数目在 N 之前固定；没有证明字面 owner 状态数或外部标量总范数对 N 一致有界。实际 owner/rank fibre 仍不是已获矩形张量许可的原子。仍须连接原策略的整盒端点与原阶乘归一化、显式支付物理/自由碰撞，最终取得常数及阈值先于所有实际 chart/row/mode/family 索引的全域统一有符号中段界。原 ProperPower 登记保持 18/21。

[完整验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p15-historical-ranked-beta-evidence.zip)

归档：508,886 bytes，53 个成员，CRC 与每个索引成员哈希均已复核。SHA-256：`97098880fbf3745e751731d9a378673072a48f0d31e1e47bd03c8946b14a3859`。
