# coefficient_bv 第四批：实际 W 整盒原始源重组

已输出 `P1ActualHighWWholeBoxNativeRegroup.lean`，未编译，正式信用0。`local_step_complete=true`；目标仍未闭合，`batch_target_source_complete=false`、`task_complete=false`。

新增源码沿第三批真正构造的 actual high frontier 扩展到 W-winning row4。先证明 finish 与 complete 实际递归程序在所有数值情况都保留原始槽位出现次数：first overflow 的那个原槽被放入middle后继续处理原后缀；close的capacity<1分支保留整个原向量重跑。由此证明同一 row4Slots 程序的close/gap两分支都是固定原label整词的排列。分组只由原key、几何参数和A决定，不读取算术测试，也不把tuplewise greedy的决策纤维当矩形。

重组对象是同一真实 `rho e h epsilon m N (small*n)` 源。先从actual physical support证明，只要此值非零，完整small*n及n都平方自由；因此可以合法插入两次Mobius并应用既有原始sorted-word重数恒等式。这样得到原排序源到ordered全盒的精确c/Mword转移，没有漏掉相等label的排列数或重复素数。再使用row4程序自己的三个固定槽位表，复用既有三组tuple系数正规化恒等式：原c/Mword及三个group factorial各恢复一次；每个normalized gamma都有全整数一有界结论，覆盖重复label与cross-group碰撞。

随后直接将第三批的HighFrontier代入既有 actual_row4_atom_small_attachment。保留同一个small、同一个row4整盒程序、同一个完整q，并得到实际分组见证及e/128 Monomials和local qscale transport。由此将实际high对象、数值W分支与同固定槽位的signed源求和放在同一接口中。

关键边界：最终精确三组求和中仍显式保留 `rho(small*(a*b*d))` 的原始因果gate。没有证据证明该gate在每个原整盒上恒定或已经按三组分离，所以本文件没有将这条带耦合源的恒等式冒称完成rho三卷积/medium licence。真正消除这一gate的source-form整盒soundness、其它winning分支、全high覆盖、SW与medium/Brun解析估计仍OPEN。原稿没有因此被判定错误。

前批全部冻结未动；直接source-only依赖的raw SHA与安装路径、生产前驱raw SHA、原稿SHA均登记在REGISTRY。未运行Lean/lake/checker、Git或额度检查。
