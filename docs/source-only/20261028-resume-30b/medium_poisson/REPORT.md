# 第二批 medium_poisson

新增 Part3OriginalGevreySharedRowDictionary.lean；task_complete=false，local_step_complete=true，complete_module=true；未编译，正式信用 0。第一批及生产文件全部未改。

本次不再给抽象比例尺的尾界包装，而是实例化原始 shared-first-factor 平方行。Row 就是生产 sharedFirstFactorRows 的两个尾因子和原始 alpha 标签；liftRow 把同一个 p 和这两个标签送入原始 transposedAtom.complexRowLabels。completeModulus 是同一对 p*(q2*q3) 的 lcm，tailGcd 是两份真实尾积的 gcd。Nat.gcd_mul_lcm 给出 D*L=p*tail1*tail2；实际 dyadic membership 推出 physicalH 所需的 32Q1Q3²Q2² bound，调用者不用另给“合法E2模数”证明。

actualSharedW 使用生产 q1SliceAtom 的真实 complexDispersionW，m carrier 为实际 paperPsiNaturalCarrier，m weight 为构造出的 paperPsi(m/V)，q weight 为既有 actualPsiQWeight。直接复用生产任意 S,w 的 q1SliceDispersionW_eq_sharedCRT，得到 exact zero + retained + signed error。由第一批误差定理得到实际各行的 uniform all-power tail。

保留相位来自生产 transposed_actualCRT_fourier_eq_canonicalPhases：同一 CRT residue 的完整 root/slow/reciprocal 三因子，适用于所有整数 h，零模单独置零。没有假设 E2 输出或相位恒等式，也没有把旧 dyadic bump 等同 Gevrey。另由生产有限 complex_dispersion_identity 得到同 q/m 权重下的完整 W−2V+U 恒等式，两个 primitive-coprime 中心项原样保留。

仍未完成的原任务：clean E2 商变量 d,delta,q,w1,w2,n1,n2 的全重索引、完整三相位到原稿(21)的进一步 clean-chart 特化、扩大的平滑 q 支撑的外层 carrier、全 E2 实际系数预算。这里只消费原始 primitiveFirstFactorCarrier；不能宣称已覆盖整个 enlarged q majorant，更不能宣称 medium 完成。

静态核对了单文件注释配对、无 sorry/admit/axiom/unsafe 及引用路径 SHA；没有运行 Lean/lake/大型 checker。依赖的固定 SHA、候选安装路径和全部新引理列于 REGISTRY.json。此窄步骤未发现原稿数学缺口。
