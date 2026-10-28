# lower_tail G：真实 modulus-prime 均值修正付款

完整 G 派发目标仍为：支付真实 21-child signed AP analytic errors、positive-pair 和 quotient-switched costs 及全部原 alpha/full/selected gates，组合原同 Q 的 Phi enhancement receiver 和 fallback counts。此整项目标尚未完成；`batch_target_complete=false`、`batch_target_source_complete=false`、`task_complete=false`、`goal_complete=false`。本批 `local_step_complete=true` 仅指下述实际系数重复数与 modulus-prime 均值修正的 source 证明。

本批无编译、Lean/lake、checker/replay、额度检查或新子代理。`compiled=false`、`formal_credit=0`。只写 G/lower_tail，F 与更早源码和报告均未修改。root 若明确下令 <=10 停止，则不再推进 proof；本批没有自行检查额度。

F intake 重核三份源码、REGISTRY、REPORT 最终 raw SHA 全匹配。F 最终独立审阅为 `reviews/lower.json` SHA `356dcd66e4e40b7bfe60a8d9a6043a2a1340e52706bff31b158670afbc0f1b3c` 与 `lower.md` SHA `a901e0a8e81574cb5f4fb75530323ead37a1f13e93f06391cb7da03bc42c0015`。审阅仅为五个窄 source 步，完整 F 目标仍 OPEN。

重新核对原稿 770–788 行的真实 prime-divisor 均值修正及 790–877 行的同 Q 正 marked-family 增强计数。本批没有提出原稿数学缺陷或反例；F 的 arithmetic alpha fallback 也没有被宣称等同于完整 adopted/compiler fallback。

`P2EnhancedNegativeChildMultiplicity.lean` 首次给 F 实际 physicalCoefficient 一个由 source 自身推出的有效全局 norm。原 marks 保留 d/j/p/k，p 是三条实际原窗的选中素数，k 是真实 lower Rosser 系数的 active residual。固定旧 d 时，p>=a，而 s 的每个素因子严格小于 a。因此从 `d*p*k=d*r*s` 可推出 p|r，继而 p=r、k=s。此证明不删除 p|d，也不要求 d 或完整 modulus squarefree。

在同 full q 的 fibre 上，映射到原 `(d,j)` 是单射。对实际非负 sigma，全部三窗 marked multiplicity 至多 `3*sum_d sigma(d)`。结合已有 actualSmallRosserMinus 的 bounded-one 性质，得到真正的

`|physicalCoefficient(q)| <= 3*sum_d sigma(d)`。

这是由真实 source 推出的 norm，不是假设 `hrho` 或把 physical coefficient 改为 1；同 j 的 product 唯一性没有抹掉不同 j 的原始重复 occurrence。

`P2EnhancedNegativeChildModulusPrimePayment.lean` 支付 F 已明确保留的实际 modulus-prime term

`modulusPrimeShift = sum_{q, coprime(q,N)} rho(q)*chenPrimeDivisorCount(N,q)/phi(q)`。

先复用现有 `chenPrimeDivisorCount_le_log_center` 与 `sum_reciprocal_totient_le_log`，对任意实际正模数集合 S⊆[1,N] 导出

`sum_{q in S} chenPrimeDivisorCount(N,q)/phi(q) <= (8/log 2)*(log N)^2`

（log N>=1）。这里无需 squarefree gate，故原 p|d 行完整存在。F 的 actual active physical support 已给 `0<q<Q<=N`。将上面的实际 rho norm 代入，得到

`|modulusPrimeShift| <= (24/log 2)*(sum sigma)*(log N)^2`。

关键的归一化改进来自**真实原 cutoff**，不是新的解析假设：由 `N^eta<=a=(Q/d)^(50/227)<=Q/d` 与 Q<=N 推出 `d<=N/N^eta`。因此

`sum sigma <= (N/N^eta)*sum sigma(d)/d`。

已存在、由 log-power 极限证明的 `ninth_power_log_error_budget` 吸收 `(24/log 2)*N*(log N)^2/N^eta`。再用原 `Theta_lower` 的实际奇异乘积常数和 sigma reciprocal mass，得到

`actual_modulus_prime_shift_theta_payment : forall eta>0, epsilon>0, exists T>=4, ... |modulusPrimeShift|<=epsilon*Theta_Q`。

阈值先于 N、Q、D、sigma 及全部 child occurrence 选择。此付款不要求 Even N、不假设 PNT/AP 分布结论、不假设 K/H248/count 增强界，也不偷偷更换原 Theta_Q。

接着把该付款精确插回 F 的同 rho 计数/均值字典。`finite_mean_shift_split` 保留独立的真实 `(pi(N)-li(N))*primitivePhysicalDensity`，其余正是负的 modulusPrimeShift；`actual_centered_finite_mean_shift_payment` 将这部分均值误差统一支付。

`piCenteredPhysicalError` 使用同一个完整 rho 和真实 inclusive AP count，primitive classes 扣真实 total pi(N)/phi(q)，nonprimitive classes 保留完整 raw count。已有 finite-coprime signed error 精确等于此真实 pi-centered packet 加 modulusPrimeShift。因此 `actual_finite_error_to_pi_packet_payment` 给两者之差 <=epsilon*Theta_Q。这是实际解析均值修正付款，**不是**宣称剩余 pi-centered AP packet 已经小。

冻结源：

* `P2EnhancedNegativeChildMultiplicity.lean` — `82fd4ffcb232adf278d1531775927facd08218e54507266fcedb9e8daf1903c2`。
* `P2EnhancedNegativeChildModulusPrimePayment.lean` — `3728f744d248d7cc8e760bd9fd8e6f3ce9d91e0d74cee6fd3690abaae703fcfd`。

依赖/安装：按 F REGISTRY 的真实 source-only E/F 链提供 `P2EnhancedNegativeChildSignedModulus`，再安装 G Multiplicity，最后 ModulusPrimePayment。ChenInitialCorrectionBudget、TotientReciprocalBudget、ThetaReciprocalMass、CollisionThetaPayment 为已有实际路径；底层 NinthErrorPaymentAsymptotic、BoxMassUniform 按 WSL 真实 research/wu2008 源读并登记 raw SHA。没有安装、编译或声称已 elaborate。

完整 G 目标仍缺：剩余实际 pi-centered signed AP packet 的原内部 PP/分布付款及 PNT 模型项统一付款；ordinary/enhanced residual child mean 与实际反馈积分/共同有限逼近；positive-pair 成本；全部 Gamma7–21 quotient-switched source 的真实 positive-K licence/cost；原 family 的全部 old full/selected/alpha/ceiling/cutoff/adopted history gates 与正确 fallback 的实际来源；immutable-old action/state 和最终 H248 Phi enhancement cost。certificate_triple 本批正推进全 arity 原字典的真实 additive-prime source，并明确其 d*N mask 豁免素因子仍需分类/付款；尚非 K 许可，本批没有将它当作 K。certificate_enhanced 的 F state theorem 依赖本 lane 的 F，故本批没有反向导入制造循环。

H248 始终是实际 Phi/sifted-count 增强问题；没有强造 ordinary-rho 密度=H248。P1/P2、internal K、PP 和最终 count gain 仍是内部工作，没有被移作外部 primitive 或作为待证结论的前提。
