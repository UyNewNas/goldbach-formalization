# upper_mesh 源码交付

新增 `P1OriginalFifthJointMeshSchedule.lean`，7 个声明（2 个定义、5 个定理）。文件文本闭合，未编译，正式证明信用为 0。完整原分配目标仍未完成。

本次真正推进的是移动 mesh 的量词顺序。原先固定 mesh 时 `step ≤ chi ≤ e/10` 强制正的 e 下限，无法据此获得任意小 eta。本文件对事先固定的有限原始行集合，将每行 B13 标量误差 `modulus_i(e)/400^5 + M_i*(428/75)*e/400^4` 求和，证明该和在 e=0 连续且等于 0。由此先选正有理 e 严格小于 3/51200 且误差和严格小于 eta，然后调用实际 `exists_small_step_complete_cover` 选择 q，取 `chi=e/20`。同一个 q 同时满足 `step≤chi<e/10`、预先指定的 `step≤omega/2` 和每一个 grid400 原始行的完整半开 Ico 覆盖。没有乘以随 q 增长的 decoded-owner 个数。

代码最后给出有限三角不等式桥：实际每行积分误差一旦证明小于各自 B13 envelope，其带符号总和便被同一 bank envelope 控制。该桥没有提供尚未证明的每行积分估计。

没有把整体 hUpper/K、selected integral 或 section measure 作为前提。本文件使用的解析前提仅为每行 compact-kernel difference modulus 在 0 处连续并为 0。实际 literal kernel 的 uniform compact continuity 到这些 moduli 的构造、owner crossing 的真实一维 section 上界、原始 selected/firstStop 全部判定或 omitted-child trim、全 87 域共用祖先的绑定仍待完成。因此不能据此宣布任意 eta 的实际 upper reserve 或全 22 归档行已闭合。

窄审阅未发现原稿新缺陷；这里是实现与参数选择衔接缺口。没有修改旧草稿、生产源码、Git 或看板。安装位置和精确依赖 SHA 见 REGISTRY.json。
