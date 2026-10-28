# lower_tail F：实际 physical rho、AP 误差和 child 几何

完整派发目标仍是：实际 same-Q 21 项 child coefficients 的 coprime means、signed analytic errors、full/selected-square/alpha/cutoff source binding，并接入真实 Phi/sifted-count enhancement cost；保留 exact child/fallback counts，消费真实 switched positive-K licence。此整项目标**未完成**：`batch_target_complete=false`、`batch_target_source_complete=false`、`task_complete=false`。本批只将下述实际 source 字典和有限计数连接标为 `local_step_complete=true`。没有缩写或重命名派发目标来取得完成标志。

本批没有编译、Lean/lake、checker/replay、额度检查或新子代理。`compiled=false`，`formal_credit=0`。只写 F/lower_tail；E 和更早批次保持不变。

E intake 已重新核对三份 Lean、REGISTRY、REPORT 的最终 raw SHA，全部匹配。E 独立审阅为 `reviews/lower.json` SHA `953ec64afd042de003afdd52c5e4ee653b62fbf8f9b3e05b6ce746e596112848` 和 `lower.md` SHA `a5dccbab88d92c054ec5605653d95e522329589c5a6f27c8aa80975da283dd21`；该审阅仅认可窄 source 步，不增加 formal credit。原稿 790–877 行的正 marked family、同 Q、实际 alpha 和原反馈义务均重新核对；没有新的原稿缺陷/反例声明。

`P2EnhancedNegativeChildSignedModulus.lean` 将三条原负窗的 d/j/p/k occurrence 先保存为实际有限 marks。真实 `actualSmallRosserMinus` 非零才进入 active row，但 sigma=0 行和三个 j 的重复 occurrence 不假称唯一。完整 physical modulus 为 d*p*k，`physicalCoefficient` 是所有同 product occurrence 的**有符号 fibre 和**。没有假设 product 注入或 `|rho|<=1`。由真实系数已经证明的 bounded-one 性质，只导出保留全部 sigma-weighted occurrence multiplicity 的有限 norm bound。

对任意物理测试 F，原三窗 coefficient sum 严格等于 `sum_q rho(q) F(q)`。因此原真实 AP count、有限 exact-coprime population mean、li/phi 模型均值及各自 signed AP error 全部使用同一个 rho。active coefficients 自身给 `0<q<Q`，old prefix 若真的与 N 互素则推出 q 与 N 互素；没有将这些独立 arithmetic gates 换成最终误差结论。

新增误差字典实质连接到已有生产计数：rawPrimeAPCount 等于 `chenPrimeAPCount N N q`；有限 coprime population 等于已有 `finiteCoprimeMass (chenPrimePrefix N) 1 q`。primitive q 上 finite error 精确为已有 `finitePrimitiveDiscrepancy`，model error 精确为已有 `chenQuotientPrimeAPError`；nonprimitive q 上完整实际 AP count 保留作 fallback。只有提供 old-prefix 真互素条件时，才消除这一 fallback。

通过已有 `chenPrimePrefix_coprime_mass`，有限 population 均值到 li-model 的**同 rho**差额明确为

`rho(q) * [ (pi(N)-li(N))/phi(q) - chenPrimeDivisorCount(N,q)/phi(q) ]`

并保留 primitive-class guard。真实 modulus-prime correction 没有被删掉。`abs_model_error_le_physical_packet` 只在 signed physical regrouping 后取绝对值；它给出要支付的实际 analytic packet，**没有**证明该 packet 或均值 shift 统一为 `o(Theta)`。

`P2EnhancedNegativeChildLogGeometry.lean` 从真实 p∈primeWindow 出发，而不是仅证明一个抽象 alpha 恒等式。实际 `u=log(p)/log(Q/d)` 满足 **50/227<=u<1/negativeParameter(j)**，下端为闭。原 arithmetic source 不得默默变成开反馈区间。其 actual child level 为 Q/(d*p)，actual query 严格等于 `(227/50)*(1-u)>2`。actual child alpha 是实际 `log(N/(d*p))/log(Q/(d*p))`，等于 `1+(alpha_parent-1)/(1-u)` 并在 Q<=N 时不减。没有把 alpha 重置为 2。

`alpha_parent>=2` 仅从独立物理条件 `Q^2<=N*d` 导出。这不被宣称对 finite mother 中任意 d 成立；实际源 bank 仍需证明该 gate 或支付 fallback。full/selected square 则沿 E 冻结的真实 old tagged prefix 接口继承，不从 candidate/adopted 名称推断。

`P2EnhancedTwentyOnePhysicalReceiver.lean` 把上述真实 physical rho count 插回原 21 项 Phi 比较。它还从实际 marks 提取原 d/j/p/k，与 E support bridge 连接，保留 whole prime word 的 full/selected-complement squares、selected labels、完整 product=physicalModulus 和原 cap。

receiver 按真实 `Q^2<=N*d` 将原 D 精确分为 alphaAdmitted 与 alphaFallback，Phi 完全相加重构。admitted 部分可以使用实际 child alpha>=2；其余部分的 **5*Phi(alphaFallback,11/5)** 原计数完整留在最后不等式。这里的 arithmetic partition 不是声称已经等于原 adopted/compiler fallback；两者的 causal/history/mask 绑定仍 OPEN。epsilon 仍乘 admitted marked family 自己的原 `Theta_Q`，没有未经证明换成另一个 normalizer。

三份最终源码：

* SignedModulus：`c05be3c4cdae1ac8b32afd0fed10d1a68bab9b143504a35b83e7eec0cad200ec`。
* LogGeometry：`3daafcded285b261ea84991c8591a5b690623b630383a4db1127259c200ddeb5`。
* PhysicalReceiver：`1266b3d57139dc27682989c50722f0485082294be3e4276e696b84e503dd97a5`。

安装顺序及 raw guards 见 REGISTRY。先按 E 的真实 source-only 安装链提供 E 三源和独立 lower_square 支持，再安装 F SignedModulus、LogGeometry，最后 PhysicalReceiver。没有安装或修改生产文件，也不声称这些依赖已经 elaborate。

未完成的内部工作：真实 family 上 signed AP packet 和 finite-to-li prime-divisor shift 的统一解析付款；由普通 residual mean 到实际 enhanced child feedback 的定量下界；闭下端/共同有限逼近的总误差；actual family 全 physical/adopted history/mask gates 的来源；两正 pair 和完整 Gamma7–21（含 higher arity/unit surfaces）的 positive-K licence/cost；与 immutable-old action count induction 及最终 H248/Phi cost 的结合；原 compiled-row/ideal-query、fixed mesh enlargement、U10/U11 mask 与原 fallback 的整体衔接。certificate_triple 已明确 F 仍无全 switched positive-K 解析 supplier，只有独立 W1 三槽 source/字典的进一步进展；本批没有消费它作为 K 或全 switched cost。

因此本批不是完整 signed analytic error 定理或 H248 增强 cost 定理。P1/P2、PP 和 internal K 均仍属内部证明工作，没有被移到外部 primitive 或作为所需结论的前提。
