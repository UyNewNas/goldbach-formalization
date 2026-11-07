# coefficient_rough — 第五批 E 冻结源码报告

本批交付 3 份闭合 Lean 源文件，共 773 行、51 个 theorem 声明（含局部辅助及 simp 引理）。只做源码推理、原文/API 阅读和 raw-byte SHA 登记；未编译、未运行 Lean/lake、数值 replay 或 checker，formal_credit=0。原任务 task_complete=false，batch_target_source_complete=false；下面列明的窄步 local_step_complete=true。此前 A–D 全部保持冻结。

## 原稿与实际对象

重新核对 manuscript-body.tex 第 451–463 行的有限政策、proper affine wall、保留 inherit/equality 区域与带符号 small/rough attachment，以及第 1299–1307 行先固定精度/因果政策再令 N 增长的顺序。采用原十一 Cell、原 PhysicalCell、原 coreSequence 和同一 target-deleted originalTuples，不换域、不把弱 raw31 licence 边界删去。十一域本来已有 t6>53/4608；这批没有声称处理该原域之外的全非紧第三尾。

## 实质推进

1. `P2OriginalSixthProperAffineWalls` 将原来的 19 个 baseFace（最后一个 priority min 展开为两个原行）、6 个 full-square 和 6 个 selected-complement square 编成 32 个有理仿射行。证明每行或者有非零线性系数，或者是非零常数，包含 literal eta 常数面。原 omitted 点必有某个实际 sourceRow 满足 0<row(t)<1/(n+1)。原弱 W/raw31/first3 licence 仍留在 closedLicense 内；不要求它们是可删除的零测壁。

2. `P2OriginalSixthOmittedArithmeticMass` 对真实素数元组逐行使用现有 `P1ActualMovingAffineSlab.affineSlabMass_le_envelope`。该接口已按非零素坐标有限解剖，保留 target deletion、全部其余坐标和闭壁 prime atom，给出

   `2*delta/(a*abs(v_j)) + b*K/(a^2*log N) + 1/(N^a-1)`

   乘以其余五个坐标的真实 box mass。这里 a=53/4608、b=19/96。单独先使固定 delta=1/(n+1) 的主项小，再用 N 阈值控制两个误差项与其余 box mass；常数行在 delta 小于其非零常数时严格为空。对十一域和所有原行有限取最大值，获得

   `forall eps>0, exists n0 N0, forall n>=n0, forall N>=N0, forall c, omittedMass c n N < eps`。

   因此是实际 reciprocal-prime 算术质量，且是固定截断先选、N 后增长；没有以连续 omittedGain 收敛替代算术估计，也没有令 n=N 后冒称固定有限政策。带符号版本对每个显式 uniformly bounded tuple test 同样统一。

3. `P2OriginalSixthCommonScheduleAndFullQ` 把十一 core 的有限并集作一个 commonCore，构造同一 CompactThirdChoice（同一 e/chi/mesh/roughFloor），并让连续 saving loss 与独立算术余项采用同一固定 n。真实 compact tuple 先由已冻结 D 源构造旧 policy5 retained leaf，再消费 physical 作者独立冻结的 `original_root_moduli_subset_final`，进入真实 common-refined policy8 的 fixedRoughSupport。没有将新旧 actualParent5 设为相等。

4. 在该真实 support 上，`compact_fullq_coefficient_eq_pair` 直接复用原 unique small/rough attachment，得到同一 full q=e*P 的真实 rho 值等于原 `smallRoughPairCoefficient`，保留原 beta 符号。原 source 严格次序还给出 prime tuple injectivity，故 tupleWeight=1/phi(P)。`exists_omittedFullqTest_uniform_rectangle` 将实际物理 rho 的已证明全 q 一界应用到 `sum_{p omitted} rho(e*P)/phi(P)`，其阈值统一于全部 d、e、cap、w、z、L。

5. `abs_small_sum_omittedFullqTest_le` 明确保留随后 small-divisor 求和的真实 `sum |beta(e)|` 因子。逐 e 的一致估计没有被误报为整个 small/residual 模数总和的归一化密度估计。

## 精确前提与依赖

没有新增 primitive 假设、目标密度假设、hPP/hK/hSW 或结论作前提。仿射薄层估计复用已存在的原 prime-interval/Euler 接口和真实有限 box mass 极限；具体来源和 raw SHA 均在 REGISTRY.json。通用 signedOmitted 的 `|F|<=B` 是明确的逐 tuple 测试包络，不是已经付清的 AP 误差；对实际 rho 的 specialization 由 `actualSmallRoughRho_abs_le_one` 自行放电。

retained support 的输入仍是 hN、原 inert enumeration cap、omega<=共同正 roughFloor、实际原 rows4/licensed4/J5/rows5 与 compact source membership。first-four/support/sublist/history buffer 已由前批构造；新 policy8 的原支包含来自独立 physical 冻结源，未要求新第五 cap 仍 <= 原 oldCap。

coefficient_signed 的 ALL16 canonical residual wall 接口已经阅读，但其 carrier 与原十一 prefixfaces 不是同一对象。本批没有虚构二者的 tuple/row map，也未导入该接口来冒充本域总质量估计；本批所需物理全 q 一界直接复用生产 `ActualSmallRoughAttachment`。

安装顺序：前批 B/C/D 的注册模块及其已登记 held imports；physical 的 Constructor → Ancestry → Preservation（及其登记的 corrected Phase7 / eighth-mask held imports）；本批 ProperAffineWalls → OmittedArithmeticMass → CommonScheduleAndFullQ。新文件的 `ImbalancedChen.*` import 都是预定安装名，不表示已安装、已解析或已内核验收。

## 保留的缺口

- 本批只统一控制原十一域 reciprocal-prime/reciprocal-totient 的 omitted source 测试，以及逐 small factor 的真实 rho 测试。对全部 small factors 和 residual moduli 求和后的归一化密度支付、count-minus-coprime-mean/AP 误差支付仍须提供真实总因子估计，不能用逐 q 一界替代。
- 旧 compact source 的 retained product 确已进入 refined policy8 support；但每个原源点是否仍以 `H5 < actualParent5 <= oldCap` 触发新的 selected lambda6 行，及该 common parent 下的 adopted gain 许可，尚未证明。support 包含不等于所有局部 saving 的保持。
- archived simplex/vertex 归属、Jacobian、原 stored numerical total/gain 及 full rough SW/PP/current K 绑定仍未完成；原完整目标保持 false。
- 生产 import 与所有 source-only 传递依赖仍待用户指定编译负责人安装、解析和内核验证。

当前发现的是上述实现范围缺口，没有新的已证实原稿数学错误。报告不声称核验或 numerical checker 通过。

## 本批源码 raw SHA-256

| 文件 | raw SHA-256 |
| --- | --- |
| P2OriginalSixthProperAffineWalls.lean | 8a991d81c178093f7955bdda5f6b714fabd673badd9661021e860b286e6c864d |
| P2OriginalSixthOmittedArithmeticMass.lean | a79b6b8479a101095f010f348f9832ff800f9e61120ac148456f9f4114592853 |
| P2OriginalSixthCommonScheduleAndFullQ.lean | 83fee7d363735a4492efe789f17b66f6117acc470a5a83c1d9b83dc05909371f |

REGISTRY.json 另登记本报告 raw SHA；REGISTRY 自身最终 SHA 通过交付消息给 root/reviewer，避免在文件内制造自引用 hash。
