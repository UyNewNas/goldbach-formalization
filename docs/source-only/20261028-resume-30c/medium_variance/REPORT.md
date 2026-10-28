# 第三批 medium_variance：实际 fixed-k 高 conductor 大筛

已交付 `Part3ActualHighConductorFixedQuotient.lean`，439 行。前两批和生产源码未改；未编译、正式信用为 0。

源码直接调用当前 production 已使用的具名原始大筛 `ChenLiuCoprimeProducer.polynomial_second_moment_energy`。系数使用同一实际 `alphaCarrier` 和预先固定的 `r*k` 门；对 alpha 取共轭匹配 native polynomial 的 psi 惯例，因此原来的 star(psi) 系数范数精确保留。admissibility 给支持和一界，真实 masked L2 energy 至多 N=floor(2U)，从而得到固定 k 的 dyadic primitive cell 界 `K*(D+N/D)*N`。

随后用 native conductor decomposition 精确改写 full-level highCharacters。phi(f*k)>=phi(f)phi(k) 在 f,k 不互素时仍成立；真正 product cutoff ell=f*k<=Q 通过有限三角重索引保留为 f<=Q/k。没有把 full variance 或一个 hHighConductor 输出作为前提。

每个固定 k 的高 conductor 区间由正 doubling cells 覆盖，窗口数显式至多 Nat.log2(Q)+1。所有窗口使用同一原始 masked sequence。最终 quotient 总和用已有 reciprocal-totient 固定矩支付，得到

`highEnergy <= K*N*(Q+N/R)*(Nat.log2 Q+1)*(1+log Q)^2`，

其中 K=2*chen1973Lemma6Eq19SharpConstant，Q>=1，R>0，r 任意。精确中间式使用 Q/k；最后单调放大保留额外固定对数因子，尚需在下一步用原稿严格 `Q<=N*x^(-delta)` 余量支付。没有 Q^epsilon 损失。`low_add_high_eq_actual_variance` 已将真实 low/high 两半接回原始 reduced-class 方差。

还需吸收固定对数、按原稿选择 logarithmic cutoff R、合并低 conductor SW，证明实际粗方差及固定除数权的 Cauchy interpolation，随后将完整(14)插入 positive principal Gram 得到(15)。非零频率四 chart/ABL 返回仍是独立未完事项。因此第三批 finite high 子步骤已写，原始 task_complete=false。未发现新的原稿数学缺口。
