# 第四批 medium_variance：实际加权(14)与有限Gram插入

交付五份源码，共857行；前三批文件冻结不改。所有文件未编译、正式信用为0。

`Part3ActualCrudeWeightedVariance` 从同一实际alphaCarrier和r-filter出发，先精确去掉非负principal mass，再用progression quotient-block occupancy证明 `variance<=2*N²/ell`（N=floor(2U)，ell<=N）。没有额外tau损失。固定除数阶的native harmonic moment随后支付weighted Cauchy第二因子。

`Part3ActualHighConductorLogMargin` 构造R=ceil(log(x)^b)，证明R正及上下界；原始严格Q<=N*x^(-delta)余量支付窗口固定对数，Mathlib log-versus-power给统一阈值。`Part3ActualLowConductorLogChoice` 先固定b及除数矩阶，再选择SW exponent。

`Part3ActualWeightedFilteredBDH` 将这些真实返回合并，给出原始hSW直接推出的任意固定w加权方差(14)：C,x0先于varying atom,Q,r选择，保留tau(r)^(2C0)，无whole-variance/BDH输出前提。原子尺度门明确为Q<=N、Q<=x、Q<=N*x^(-delta)。原稿实际Q（例如floor(8Y)）的调用端仍需证明这些数值门；源码没有伪造该caller。

`Part3ActualPrincipalGramVarianceBound` 对现有paperPrincipalVariance保持原始totient核和同一centered row，以有限Gram average和Cauchy证明

`paperPrincipalVariance <= card(R)*sum_r |eta_r|²*filteredVariance/(phi(ell*r))²`。

共同周期实际构造为ell*product(R)，只是Gram normalization，不进入解析误差尺度。eta可保留真实signed lambdaTrim；不要求eta非负，也不假设最终P上界。

完整(15)仍需将当前strictReceiverCutoff z、实际lambdaTrim除数界、rough support/cardinality、q,d重复度、reciprocal-totient层级和ordinary r-divisor mean接入。已向medium_s1同步该接口；对方实际Lambda与owned atlas正在衔接。完整medium、非零频率四chart/ABL和最终主定理均OPEN。未发现新的原稿数学缺口。

此次标记local_step_complete=true（真实粗方差、加权(14)数值门版本、有限principal Gram插入）；batch_target_source_complete=false与task_complete=false，因为原任务包含完整physical caller和(15)。registry固定每个源码和source-only前置的raw SHA，不提供编译/内核结论。
