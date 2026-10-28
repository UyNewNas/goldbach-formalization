# upper_jensen 第三批交付

新增两份 Lean，共504行、33项声明，写入本任务30c目录；前两批全部冻结未改。源码、依赖原始路径、SHA、安装模块名和残余前提均在 `REGISTRY.json`。未运行 Lean、lake、内核审计或数值 checker，正式信用为0。

本轮把 whole-child 下界接到**实际 selected-owner 的并集**，并保留两笔可观测误差。`retainedChild` 是真实 half-open child 与原始 `selectedFifthCells` 对应 `fullCell` 并集的交；每个 `fullCell` 保留原先 first/third 历史、粗糙激活及实际半开网格。遗漏集定义为原 child 减去该并集，不假设它仅有零测边界。

具体 reserve 是

`rowMassBound(raw) * volume.real(omittedChild) + rowModulus(raw,e) * volume.real(retainedChild)`。

第一项控制被真实 owner 剪裁掉的 frozen-positive 核；第二项用同一原始 signed `literalRawKernel` 正部的统一范数差控制从0缓冲到e缓冲。new mask、可变 MI、可变 rawFourth−2e、两个独立严格 own-cube gate 保留不变。这里没有对有限带符号 Möbius 系数主张单调性。

`whole_child_sub_reserve_le_retained_positive` 通过确切 sdiff 积分恒等式和已构造的真实 mass/modulus 得到剪裁/缓冲下界。随后，先在同一个 child 内按实际 owner 的唯一半开归属分割，再按全部64个 child 分割同一个 raw owner。交换这两层有限和后，`all64_certified_sub_reserves_le_actual_owner_sum` 把所有 child 的 Jensen 值减去显式 reserve 接到已有的原始可变第四/第五策略 `rawOwnerIntegral`。右边没有被复制64次；每个 child-owner 交集只计一次。实际策略的 key、geometry、gate、粗糙参数和同一族 records 前提全部保留。

`certifiedChildJensen` 对负的 signed d 采用0分支。消费邻居冻结的 `P5NamedFifthAllChildren` 后，第二模块对两个字面 parent 的全部128个 child 自动供应 hd、正坐标、同一 parent picks 和 closed-child ratio；不假设 d 全正。获得每个 parent 的完整64项 certifiedTotal 减 reserveTotal 不超过其实际 owner 积分和的源码定理。

尚未解决的是让**实际遗漏体积**趋零并使该 reserve 落入原稿给定预算。任意 selected policy 的遗漏体积可能大，本交付不宣称已经小于u。也未证明全历史 parent bank、所有 adopted J5、atanh/Q80 整数floor、same-rho解析估计或最终K。没有新原稿数学缺口；这是原稿已要求的剪裁与同源缓冲误差衔接。`local_step_complete=true`、本轮源码目标已写出，原广义任务保持 `task_complete=false`。
