# transfer_power 第二批

交付 `P5ProperPowerActualReciprocalTail.lean`：395 行，7 个 theorem。源码文本闭合，`local_step_complete=true`；原任务完整目标仍 `task_complete=false`，未编译、未内核验证、零正式信用。第一批文件未修改。

本轮实质补齐 actual chart 的加权非碰撞倒数尾项。对真实 properPowers(U)，选取其已有 prime-base/exponent cover 中的一个代表；代表映射按乘方结果可证单射，故不需要假设 prime-power exponent 唯一，也不会因重复表示漏算。n=p^e≥A 且 e≥2 给出 sqrt(A)*p≤n，因而 1/n≤1/(sqrt(A)*p)。先求底数 harmonic，再求 exponent 的有限 log2(U) 范围，得到

`Σ proper powers n≥A, 1/n ≤ (log2(U)+1)·logBudget(sqrt U)/sqrt(A)`。

这是带固定对数损失的真正 A^(-1/2) 倒数尾界。将原始有序 word 单射进每个原 dyadic 坐标的有限载体后，finite Fubini 保留全部有序重数。marked bad slot 恰付上述尾界一次，其余 slots 付各自 harmonic；没有排序、factorial 或 product-image 去重。

实际 Family 的全整数 support 给出每个坐标≥Family.lower*T^aStar 和 complete product≤Family.upper*T；第一批 transfer_lambda 的 normalized Lambda word≤1 及 mixedEuler(0) 给出共同 C·log(T+2)^B 幅度。第一批 transfer_power 的同一 rho signed row 预算给出非碰撞 divisor cost，mean 仍是 `Σ_Q |rho|/phi`。把有限实际 complete-product 范围内的 divisor cardinality 取 supremum 后得到明确的 actual chart bound，保留该 supremum 与同系数 meanBudget，没有把它们假设成最终目标大小。

另补实际 normalized Lambda/chart 的 exact-product=t 碰撞预算，直接消费第一批 tau(t)^k integer-word 重数，而不是全素数才适用的 rank^rank。它始终与最终 ordered bad remainder 的 prime-square r=q 分开。

尚待：实际 physical selected W_N/CapPlan 的 Family instance、同一 physical rho 的 divisor subpower/reciprocal-totient aggregate、active-modulus polynomial cap、全 chart/rank/marked-slot 求和及 common margins。最终 J_b、prime remainder r=1 和 fixed-b 全偶数阈值仍未由此闭合。未发现新的原稿数学缺口。

导入与手稿 SHA、安装映射及剩余义务见 REGISTRY.json。未运行 Lean/lake、编译或大型 checker。
