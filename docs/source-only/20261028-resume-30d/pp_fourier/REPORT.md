# 第四批 pp_fourier：完整模数之后的实际 Fourier 尾款

交付四份新 Lean 源码；未编译、零正式信用，前三批冻结 hash 保持不变。`local_step_complete=true`，完整 global atlas/scalar/mode assembly 仍未完成，因此 `batch_target_source_complete=false`、原目标 `task_complete=false`。

第一份先让 q=1 的精确 count/mean 相消，再对同一 rho 的完整 q 行取范数。b≠T 的整个模数和先化为真实正距离的 divisor sum，b=T 则保留为实际 HB fibre(T)×Σ||rho||；exact coprime mean 单独付 Σ||rho||/φ，不带 D 因子。所有标签和重复 complete product 均通过实际 fibre sum 保留，无 product injectivity 或排序假设。

第二份从原 native τ-power、无平移均值和已写的真实 shifted E1，推得 global complete scale X≥T、b≤6X 的实际 mixed moment；未将原稿内部 E3 当新 primitive。这一 global X 只用于尾款，保留 arithmetic-mode 原局部 scale。并将既有 squarefree halfProductDensity 的16次卷积证明推广到实际任意固定 J，得到 τ(q)^J/φ 的真实对数预算。

第三份对实际 Fin m→Nat ordered HB tuple 证明 fibre card≤τ(b)^m。β 是原 native signed real-cutoff rough Moebius/rough-one/log slot 的真实乘积，逐项推得 ||β||≤(1+log(7X))^m。结合 mixed moment 和 totient，完整模数总质量的多项式预算是由这些证明导出，不是输入的新结论。之后消费第三批 actual chart/Fourier tail，明确选取 H=(1+log(7X))^(accuracy+derivativeOrder+paymentExponent+3)，其指数先于 T。

精确乘积 b=T 另用实际物理 D≤T^θ、θ<1，以及已证明 native τ 小幂定理，固定 ε=(1−θ)/2；因此 Dτ(T)^m≤C T，不能仅由 D≤6X 推断。源码据此给出真正的 logarithmic saving。

第四份保留真实 retained separated arithmetic-mode 端口：证明其 actual finite Fourier integral，积分只付 mixedD/2^m；不付 H^m，也不冒称证明 medium/BV/one-long/two-long 模式估计。同一 rho、complete product 和 exact coprime mean 全程保留。另有 signed finite piece restoration 的三角与对数指数付款定理，有限 dyadic/rank/marked-slot scalar norm 只收费一次。

尚未闭合：实际全 HB atlas 的 retained geometry（特别 X≤C*T）、全 dyadic/rank/marked-slot inventory 与真实 scalar norm 构造、共享 cutoff/阈值，以及各原始 arithmetic-mode 估计的应用。不能据此声称 final PP、hUpper/hLower 或主定理已完成。未发现新的原稿数学缺口。

只做源码推导、原稿与已有形式化的定向读取；没有 Lean/lake、大 checker、额度、Git、安装或生产文件修改。精确 raw SHA、依赖和前提列于 REGISTRY.json。
