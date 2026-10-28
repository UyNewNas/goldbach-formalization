# upper_fifth 第二批交付

新增 `P5NamedFifthPayloadSemantics.lean`。原第一批文件冻结未改；本批未编译、未执行 Lean `decide`、未跑大型数值 checker，formal_credit=0。

真实连接已推进到两条 named parent 的 actual grid1600 zeroChild：

- `sourcePicks` 精确用父盒 midpoint 的 A/C/global-cap 三列按先后 argmin 选择，证明与 producer 整数三列乘同一正数 `64*n` 的算术对应。picks 在所有 child 固定，未改为 child midpoint。
- 定义完全有理的十五旧平面最大值和新 min(A,C) 减 own-cube ceiling；证明其有理表达式 cast 到真实 `frozenGap`，进而 cast 到同一 `vertexD`。
- 原始 grid400 d=5984/5232 与 `parentDQ` 分别绑定。实际 widths=(2,2,2,2,1)、grid1600 的 zeroChild 使用新 d=29824/25152，各自给出 `hd : (d:ℝ)=vertexD`。这两个尺度没有混用。
- A/B=3200/800=4 与 3192/800=399/100，由父盒所有坐标的实际 lower endpoint 直接证明 residual 上界。这对每个真实 closed child 成立；同时给出所有实际 childLeft 正性。
- 用实际 `integral_frozenGap_ge_saved_integer_d` 得到两条 zeroChild 的真实 gap 积分下界。upper_jensen 的一般核积分代码可直接消费 hleft、hnew、hd，继续得到 Q/Jensen 核积分实例。

辅助小规模 Fraction 算术只用于作者选取正确常数：两行各 32 个父顶点和 32 个 zeroChild 顶点。Lean 中的四个有限有理 `decide` 定理尚待用户编译；这不是已执行内核验收，也不构成全表数值 receipt。

剩余原目标：其余 63 child 的逐项 d、full historical family、exact_floor 对数/Q80、selected-owner clipping reserve、buffered joint tree、历史完整 J5 与 K 都开放。`complete_module=true`/`local_step_complete=true` 仅为本文件局部身份与两个 actual child 输入闭合；`task_complete=false`。本轮未发现原稿数学缺口。

精确源码哈希、held import 安装映射与接口名见 REGISTRY.json。没有触碰生产源码、旧草稿、Git 或看板。
