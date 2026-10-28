# transfer_lambda 第二批交付

新增 `Part3AllKFamilyProperPowerSaving.lean`：315 行、11 个声明。第一批源码保持冻结。`complete_module=true`、`local_step_complete=true`；整条原任务仍为 `task_complete=false`，未编译、未经过内核验证，正式信用为 0。

本批把第一批的 all-k proper-power correction 真正接到了原稿几何尺度。主要结果 `uniform_family_power_saving` 的常数 `C,B` 从同一个 `Family.mixedEuler 0` 得到，选在 T、rank、chart、test kernel 之前；没有把物理幅度或所需误差重新作为最终接口前提。

证明的关键连接：

1. 对每个非空的实际 `badChartWords`，选择其中一个非零 chart word。该 word 的同一 `bankWeight` 非零，故 Family 的全整数支撑给出每个坐标至少 `lower*T^aStar`，完整乘积至多 `upper*T`。结合前任的真实 psi 支撑，得到整张 padded Cartesian box 的体积上界 `∏(U_i+1) ≤ 5^k*upper*T`，以及所选坏坐标 `U_bad ≥ lower*T^aStar`。
2. 从 literal `chartBank` 解出实际 dyadic label j。用 `Nat.le_log2` 证明 `log2(2^(j+1))=j+1`，继而消除原来抽象的 logarithm envelope，得到 `log2(U_bad)+1 ≤ cutoffIndex(cap)+2`。
3. 若实际 bad-word 集为空，先归零；只有非空集合才扩大到 box 并使用上一步尺度。这样没有把一个 inactive chart 的形式盒子当成已获物理支撑的对象。
4. 调用已有 `oneBadSlotBox_absolute_mass_scale`，再对原始 occurrence `bad : Fin k` 求和，得到

   `2*k*M*H*5^k*upper*T*(cutoffIndex(cap)+2) / sqrt(lower*T^aStar)`。

   函数 `powerSavingBudget` 将它明确改写为

   `(2*k*M*H*5^k*upper*(cutoffIndex(cap)+2)/sqrt(lower)) * T^(1-aStar/2)`。

   `aStar>0` 是既有 Family 字段，因此这里确有幂节省，而不只是一个未绑定的 Cartesian cardinal 上界。
5. `family_atlas_power_saving` 经第一批的精确 `family_atlas_sub_primes_exact` 接回完整 HB atlas 减原 prime chart；同一 kernel 和实际 rough projector 保留，prime 侧只在 `z<lower*T^aStar` 下删除 rough projector。

尚未完成 native `W_N` 的 Family 构造、实际 same-rho modulus/divisor kernel 支付、product=T 对角分离、全 chart 求和与 cap 的目标尺度绑定，以及碰撞和完整 PP 插入。这些没有被本文件改为新的经典 primitive；`H` 仍明确是当前单个测试 kernel 的点态预算，实际 signed 模数核必须另行证明。

本批只检查源码逻辑、登记 SHA 和禁止 token，未运行 Lean、lake 或数值 checker。没有发现新的原稿数学缺口。依赖路径、精确 SHA、预期安装 import 和具体已消除义务均记录在 `REGISTRY.json`。
