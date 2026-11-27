# P1.5 实际历史 owner 的唯一性

同一个粗糙因子 b 的实际首次分歧见证现在已证明唯一：不只选中前缀相同，原状态的字面 `remaining`、`positive` 和 `mass` 也全部相同。在原 `changedRough` 载体上，`realizes_iff_owner` 与 `fibre_iff_realizes` 把既有 owner/fibre 的选择条件精确改写为原 `Realizes` 条件，没有增加任意选取造成的额外切割。

`RejectsAtLast` 只是把**同一个原 retained 策略**逐个作用到被选中字上的 Prop 证书：第一次拒绝恰为最后一个字母。它不是替代策略，不改变任何筛选条件。`exit_prefix_word` 从实际 `p1SignedExitStates` 的递归得到这个证书。两个这样的拒绝字若有前缀关系，就必须相等；此处不需载体无重复的假设。

两个实现同一 b 的实际见证都已接到 b 的同一个规范降序素因子字。因此它们的前缀可比，进而相等。原粗糙素数载体没有重复；复用原 `carrier_decomposition` 以及 Mathlib 的列表分割唯一性后，剩余载体也相同。最后直接复用原 `sign_mass` 不变量，得到完整状态相等。没有重写上述既有不变量或规范素因子字证明。

这一步为冻结 1106 系数附录中的实际带符号原子连接去除见证选择歧义。原 old/fresh 准入有效性、粗糙 mask、beta 选择和完整模数过滤均未修改。`Realizes` 条件仍完整保留，不能只凭规范前缀就删除其余条件。

## 验收

`formal-00000` 首次验证即通过：normal 7.131754 秒、精确新模块 kernel 9.363532 秒、完整 owned 类型/宇宙/公理审计 8.746767 秒，均退出 0。共 **21 个 owned 声明，含 3 个私有声明**；私有和生成声明都进入审计。仅有 `Classical.choice`、`Quot.sound`、`propext`。

复用已验收 residual、rough owner 和 canonical owner 的源、对象与回执，输入前后指纹一致，旧模块 normal/kernel 次数为 0。原冻结 helper、Member guard/core、工具链、依赖和资源参数不变。这是隔离输出的 direct Lean 验收，未声称 Lake named-target 或全导入闭包重放。本轮无失败或覆盖的尝试。

## 尚未闭合的范围

**完整 P1.5 仍然开放。** 唯一性去除了任意 witness-choice 条件，但 `Realizes` 所描述的实际策略门区域仍须接入整盒端点细分和边界条带余量，原阶乘归一化及物理/自由碰撞仍须精确连接。尚未证明 owner 状态数或标量总范数对 N 一致有界，尚未得到常数和阈值先于全部实际 chart/row/mode/family 索引的全域统一有符号中段界。原 ProperPower 登记保持 18/21。

[完整验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p15-historical-owner-uniqueness-evidence.zip)

归档：237,862 bytes，33 个成员；CRC 与每个索引成员哈希均已复核。SHA-256：`02ade6953cca40e90661e11ab1fe81cc45432cd7358b52fbb61600948468b04f`。
