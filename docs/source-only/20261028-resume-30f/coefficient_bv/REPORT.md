# F：同一实际 all16 内项的原逐标签三卷积

F 原派发目标保持完整：把更紧的原逐标签阶乘 gamma 正规化接到同一实际 all16 common-fine atom 重构，并验证实际 selected group assignment 的原 whole-box 数值 capacity / branch / SW 许可。**本批没有完成这个完整目标**。`local_step_complete=true`；`batch_target_complete=false`；`batch_target_source_complete=false`；原 `goal_complete=false`、`task_complete=false`。

仅 source-only。未运行 Lean、lake、编译器、checker 或数值 replay；`compiled=false`、`formal_credit=0`。仅写 F/coefficient_bv，E 源码、登记、报告和独立 review 保持冻结。

## 最终源码

| 文件 | Raw SHA256 |
|---|---|
| P5ActualInnerPerLabelGamma.lean | 7a1b177ae76f06f588bc78f45ecf61a4bd99e46dc1a642820c27ed09c1b67f21 |
| P5ActualRetainedInnerPerLabelConvolution.lean | b33556e0b65890ad9b29f4556994d9eeb84771db03248af78082ff9eac457c3e |
| P5ActualAll16PerLabelTensor.lean | 034d0c15d4feae8c6e25bba356ca1fc877d29730d149b67aef097a4738e2a9b4 |
| P5ActualInnerWholeEndpointCapacity.lean | 74e33684c4569395bcc38f1e5f3a271c12c648f7c5960ce45fc478234b949f35 |
| P5ActualPerLabelAuxiliaryRemoval.lean | 2e58212076796dcef5dbf9903bd9da34e9ca9983ab17a6bab405905c71206588 |

合计 24 个定理，未编译。每个源安装到 `ImbalancedChen/同文件名`；namespace 为 `ImbalancedChen.P5Z` 下的同名去 P5 前缀。REGISTRY 记录逐源真实 import / raw SHA / 安装目标。先由用户的独立安装处放入冻结 E 和 signed F 供应源，再安装逐标签基础源、retained bridge 和 all16 tensor；数值端点与辅助互素移除是分别导出的接口。这里没有修改 production。

## 原稿与独立源

重读原稿 `manuscript-body.tex` 280–314、334–338 行（SHA `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`）：原固定 policy、所有 full / selected-complement square、原 `M_j=prod_label(count_j label)!`，完整模数、β 唯一附着以及真实 SW / medium / 合法低秩 BV / Brun 分工。没有把带四个实际 marked primes 的完整模数改称 rank-one BV。

E 的两个源、REGISTRY、REPORT 的 SHA 分别仍为 `86d4b57686ee69226b8f8c9c277b1f66310509f35455826a1008b702c57b7541`、`72d901714e954dd054e2eb7037a2a948f6982227b92f0434f6e613ce8a02128b`、`ec3ea1f49395cd7ba467b563938dee7ba20751162a4366adb806fbd8e00034cc`、`494b53a827c9e1ee18da8fe2e8c029a187954514e26d38bd33755fe49efc9065`。独立 E review `reviews/coefficient.json` SHA `dc024356dbe47bcc6228ab2e90efcc12625b422ef96e78d7450c0a08a59389ef`，`coefficient.md` SHA `9a715b6da5cd7ca0dfa90044bd84c6453b2d7a5592a49891968bf3f41368a2bf`；均重核，未改。

真正消费 signed owner 的 F 独立冻结源：

- `P5All16InnerCartesianDictionary.lean`，SHA `4b41cb243762220486d17814161335df723956e0843cd91268e8e8ad41c44983`：actual canonical inner fibre 与完整 Cartesian boxes 的双向词典，实际 inner 标签注入、原 M_res=1，以及独立 retained 系数源到全盒的精确等式。
- `P5All16InnerCartesianAssembly.lean`，SHA `ab3415dd57e0af7e24b39cc064074e979d9706bd32d431b469776791b08248e0`：从真实 all16 innerAtomLinear 导出同一全盒源，局部 rough-rank 假设由实际 physical compiler 消去。

依赖方向是 signed F 只依赖已冻结 E，本 F 单向消费 signed 的独立源重构；没有使用 signed 的最终 mass 结论，也没有循环假设目标 tensor 等式。physical owner 明确尚无 F whole-source-form endpoint 供应；本交付未捏造该接口。

## 已完成的原逐标签连接

`multiplicity word` 字面定义为 `prod_i∈word.toFinset (word.count i)!`，`gamma` 为原完整 Cartesian product fibre 除以该数。没有用组总 slot 数 factorial 代替它。

`three_group_sum_per_label` 保留原 M1、M2、M3，每项的外标量严格为原 `(-1)^r M1 M2 M3/M_all`。实际 innerCells 的 lower corner 本身满足严格 order，故 signed 独立几何定理给出 j injective。原 computedGroups occurrence partition 随即给每组 word.Nodup，所有原逐标签 M 均确实为 1。这是对这批**实际严格内盒**的真实结论，不是把一般 M 重定义成 1。

实际 gamma 的全整数一界来自 production `P5ActualNormalizedPrimeLabelCoefficient.raw_coefficient_le_label_factorial` 的原逐标签完整纤维定理，对这些注入 word 使用 singleton blocks；off-support、prime powers 仍在定义域中。β 采用原 rawBetaWeight，依整个 residual rank 固定后仅附着第三组，通过原 small/rough 唯一分解保持逐整数一界，未乘 small-support cardinality。

`actual_retained_inner_per_label_convolution` 先消费真正 retained-source / complete-box 字典，再代入原逐标签卷积，没有把候选定义成独立原系数。`actual_all16_per_label_tensor_plus_wall` 进一步得到：

`sum_q jointPresievedSigma(q) F(q) = original-per-label residual tensors + sum_q actualWallRho(q) F(q)`。

这里所有16原 rows，包括 W 和零行，都保留在相同原 marked carrier；局部 hrank 不再作为该 all16 定理的前提。原 marked 前缀为 `fullPrefix t`，完整测试始终是 `F(fullPrefix t*(a*b*q3))`，没有 rho 或门留在 coupled product test。等式对任意 F 成立，因此真实计数、同模数精确 coprime mean 和它们之差可使用同一个源等式。

原 `sum_t∈ordinaryTuples n N E` 与任意 E 仍显式外置。本等式未声称任意 E 已可分离或 marked scalar 的总绝对质量与 N 无关。没有把 NEW all16 ordinary common-beta 源按名字认作旧 compact W4 或 common-refined original11/policy8。

## 真正的整盒端点窄步

`actual_inner_endpoint_inputs` 从实际 innerCells 本身导出 rough upper corner 的非负性、Antitone 和全部原 parity cubic gates。支付的宽度字面为 `(r+3)*meshStep`；原 lower corner 的严格 cube margin 加上真实至多 r 项的 endpoint shift 给出结论，不假设 Dwell 或目标 capacity。

`actual_inner_ordinary_endpoint_monomials` 将同一 rough 内盒的 upper corner 接到 production `actual_ordinary_whole_atom_monomials`。其前提仍是原 ordinary15 eligible rational near-cap Box certificate、真实 marked padded endpoints、原 kappa/A 范围和显式 rank/mesh width <=delta。它保留 native run level `nu-2delta`，涵盖真实 capacity 分支及 full-vector repair 分支的原三 monomials。

**此处的 REAL numerical assignment 包含四个 marked slots，而前述 signed 残余 tensor 使用 residual-only computedGroups。二者未被本交付识别。** 因此不能把数值结论直接贴到当前 all16 残余张量后宣称原 normalized factorization class 已获许可。该分支也尚未支付实际 small β 的 endpoint 增量；W 的数值 action 仍需自己的原分支证明。

## SW 连接的确切边界

`actual_mesh_gamma_auxiliary_removal` 对真实原逐标签 **未附 β** 的 rough gamma，证明辅助互素条件的移除误差不超过 `4*tau(k)*H/w`。H 是该实际固定 word 的 endpoint product；正支持、rough 因子与逐整数一界均由真实 prime box 导出。调用已有 `Part3.auxiliarySWError_sub_one_norm_le`，保持同一 progression q、独立 k 和精确 primitive coprime mean，没有以普通平均替换。

该结论没有 `k=1` SW 估计。附着 small β 的第三组也没有被错误称作 rough。完整原 SW 的 prime / convolution / profile / dyadic supplier 及同 assignment 的接口仍待证明，没有用 hSW 或 hPP 包装它们。

## 下一必要连接与完整目标状态

- 同一 actual all16 源必须构造 marked-prefix common-colour prime alphabet，并把原外 marked multiplicities / E / scalar 消费为统一可分离全源。残余 γ 的 abs scalar=1 不等于完整 marked L1 预算。
- 将该真正完整 prime-label 源的 occurrence assignment 与数值许可的四 marked 加 rough REAL action 精确识别，或对当前实际 residual assignment 独立证明所需三 monomials。不能借用另一分组的容量。
- 支付第三组真实 small-beta endpoint cost，完成 W 及全部 genuine winning branches 的同源数值许可，并接入原 SW。再由内部 medium / Brun / PP 等真实 caller 得到 signed discrepancy 估计；有限恒等式不能代替这些内部估计。
- 原独立 arithmetic wall 的总 attached-modulus payment 仍未由本源给出。

以上是具体源 / 几何 / 分析连接缺口；本交付没有宣称原稿反例，也没有把 P1/P2、internal K 或 PP 的最终结论提升成外部 primitive。整个派发目标仍 OPEN。
