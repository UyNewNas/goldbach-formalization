# coefficient_signed 第六批 F：真实 innerPairs 到完整 Cartesian 源与 small-beta 吸收

本批两份 Lean 共 436 行，15 条公开定理及 1 条私有组合引理。`task_complete=false`、`local_step_complete=true`、`batch_target_complete=false`、`batch_target_source_complete=false`；未编译，正式信用为 0。E 的两份 Lean、REGISTRY、REPORT 已逐一重核 raw SHA，与冻结值一致，未改动。F 的完整任务仍是原 TASKS 所列的 marked colours 加 small-beta 吸收及独立于 N 的 restoring tensor-scalar L1 预算，没有缩小或改名。

`P5All16InnerCartesianDictionary` 先处理独立实际源。每个 certified inner mesh cell 的**完整**原 fine prime Cartesian 盒中，每个 tuple 都由原 reverse raw-gate/retained 字典证明是真 retained divisor 的 canonical descending prime list。随后用素因子分解唯一性证明 tuple 不是仅与 canonical list 互为排列，而是字面相等；完整盒的 product fibre 因而注入，rank 正好等于 product 的 primeFactors.card。反向则把每个实际 retained canonical inner 点送回它自己的完整盒，没有用“支持相等”作前提。

inner cell 包含 lower mesh corner，并且整个 cell 满足 strict order。因此其 label map 注入，原 residual label count-factorial `M_res` 在此类严格 inner cell 上为 1；这一步先证明，再插入 `1/M_res`，不是删掉原归一化。不同半开 cell 的完整 list boxes 不交，不同 rank 也由 list length 不交。实际 retained source 到完整 union 的 `Finset.sum_bij` 与该不交性给出完整 finite Cartesian source 恒等式，保持独立 `presievedCoefficient`、原 e、真实 level 与完整 prefix test。

`P5All16InnerCartesianAssembly.actual_all16_inner_eq_cartesian` 把这条源字典接到 E 独立构造的真实 `innerAtomLinear`。实际 all16 caller 的固定 rough rank 从 B 已有 physical support 结果导出，包括 W 和显示的零行；没有把局部 rank guard 外置给最终 caller。真实 `ordinaryTuples`、selectedPolicy、ownerBox、Z、physical residual exponent、small cutoff 和 rowCoefficient 均保持原对象。

下一条恒等式消费精确冻结的 E peer `actual_ordinary_inner_source_three_convolution`。它的左边已经是独立实际 ordinary presieved coefficient；整个 e 和被真正吸收到第三组 `attachedGamma`，由唯一 small/rough 分解给全整数一界，不出现 `card(small support)` 损失。最终 `actual_all16_beta_tensor_plus_wall` 对任意 signed F 给出真实 NEW `jointPresievedSigma` functional = residual beta-attached tensors + 独立实际 `wallRho` functional；完整 q 始终为 `fullPrefix(t)*(a*b*q3)`。同一恒等式可分别用于实际 count 和 exact coprime mean，未把 marked t 或 residual d 当成独立 prime-test u。

本批 assembly 保留 E peer 的 **slot-count factorial gamma** 接口和全部恢复 factorial，没有冒称它就是稿中原 per-label 的完整 marked 预算。F coefficient_bv 已单向消费本批冻结 dictionary/assembly，独立给原 per-label residual tensor；本批没有反向导入其 F 文件或其预算，依赖无环。

完整 F 目标尚有明确边界：外层 `∑t∈ordinaryTuples n N E` 仍显式存在，marked prefix 没有吸收到三组 gamma。任意算术 E 不自动 factorable；本批没有把 E 隐藏进 product test 后宣称全源已分离。仍需在**原真实几何 E/owner-policy 源**上构造 marked/common-fine Cartesian 字典，保留真实 gates 或给出实际新 wall remainder，再用 residual-only `M_res` 与原 raw marked multiplicity 恢复完整标量，证明独立于 N 的全部 absolute L1 预算。每个固定前缀的 residual source 恒等式、单 q 一界和 E 的 N 依赖 full-modulus mass 均未替代这一步。

whole-box endpoint grouping 在这些恒等式中只提供精确 finite regrouping；其真正 all16/W analytic capacity、SW monomial licence、完整 wall arithmetic payment、repeated-rough collision savings 与 internal same-rho PP 仍保留。P1、P2、internal K、PP 均未外置成 primitive，plain prime-product 的 μ(product) 也未换成 μ(q*product)。未发现新的原稿数学缺口；本批剩余是实际 marked 源绑定、共同 alphabet 和总预算的实现义务。

冻结源码：

- Dictionary：`4b41cb243762220486d17814161335df723956e0843cd91268e8e8ad41c44983`。
- Assembly：`ab3415dd57e0af7e24b39cc064074e979d9706bd32d431b469776791b08248e0`。

依赖文件路径、各 raw SHA、原稿 anchors、精确声明、真实 premises 和安装顺序均列于 REGISTRY。仅做作者静态审阅、token 检索与 raw SHA 固定；未运行 Lean、lake、compiler、checker、数值 replay 或额度检查，未修改生产树、其他作者文件或之前批次。
