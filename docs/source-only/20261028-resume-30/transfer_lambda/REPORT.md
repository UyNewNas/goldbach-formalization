# transfer_lambda 源码交付

新增 `Part3AllKFamilyLambdaCorrectionBound.lean`，423 行、22 个声明。文件文本闭合；未编译，正式验收信用为 0。原分配的整条 prime-product 转移尚未完成。

前任 all-K Lambda chart 叶子的关键限制是：裸 `Licence` 只承诺光滑延拓和 prime 上相等，并不承诺复合数输入的支撑或幅度。现有 `P5AdmissibleAllRankIntegerGeometricFamily.Family` 已有正确的实变量支撑和全 rank 混合 Euler 导数估计。本文件直接消费这个较强的原稿几何类，不再向裸 Licence 塞一个未经证明的全整数包络。

证明主线如下。

1. 将 Family 的同一 ambient profile 经 `listExtension` 写成 `bankWeight`。对每个长度为 k 的整数 word，证明物理坐标下界和完整乘积上界；这个结论确实包括 proper-prime-power 替换后的 word。
2. 对 `Family.mixedEuler` 取阶数 0，得到一个先于 T、k、chart bank 和 kernel 选定的 `C,B`，使所有 rank 的整数幅度都不超过 `C log(T+2)^B`。这一步消除了前任“只有 prime fibres 有界”的漏洞。
3. 从已有精确 `Lambda/log(p^e)=1/e` 字典推出每个 slot 及完整 word 的系数范数至多 1。以非负有限覆盖引理把全 k proper correction 覆盖到 `Fin k` 个实际 bad-occurrence chart box；一个 word 有多个坏 occurrence 只造成合法的上计数。
4. 接入前任实际整数 Cartesian box 的 sqrt/log cardinal bound，给出全 k 的显式有限误差包络；没有删掉 eta、psi、原 W 或独立测试 kernel。
5. 从全整数物理支撑和 `z<lower*T^aStar` 证明 prime 侧的每个 rough projector 等于 1。随后把完整 HB atlas 减原 prime chart，精确写成同一 kernel 的 proper-power correction，并给出相同有限包络。

`family_atlas_to_primes_bound` 是主要消费接口。`family_uniform_all_k_correction` 记录统一常数的正确量词顺序。任意 `K : Nat -> Complex` 可同时实例化计数、exact coprime mean、二者差或同一个有限 signed modulus combination；若实例化最后一种组合，其范数支付仍须另证。

这里仍不能声称原稿 PP 结束：实际 `W_N` 的 Family 实例、全 chart 求和与物理规模的幂节省、完整 signed modulus/divisor 支付（尤其 product=T 对角与非零差的区分）、排序/碰撞和后续 actual lower/upper 仍未接齐。文件没有新增 `hPP` 或最终误差作为假设；现有 `Family` 是其明确的几何输入类。未发现新的原稿数学缺口。

所有直接 import 和本文件显式调用的 source-only 前驱均在 `REGISTRY.json` 记录路径、SHA256、namespace 和预期安装名。两个直接 import 都是 held candidate，需要编译专员按登记路径先安装其前驱；本任务没有改生产模块或共享文件，没有运行 Lean、lake 或数值 checker。
