# 原经典夹持根的光滑正权、混合导数和正上筛

15 份源码给出 Γ9–21 全部 20 个原字的同一个几何外逼近，连到固定 Q、真实 ρ 的有限正上筛。主要入口为 original_common_outer、common_chart_budget、original_positive_family 和 physical_positive_upper。每项先固定原 n、τ、κ 和外逼近精度，再令 N 趋大。全部源码为静态交付。

## 原始标记和真实外权

原词的完整坐标按 p、指定的 q、规范尾素数 r 排列。p 保留在原模数与 Q=N^ν 的几何中，ν=clampLevel(n,τ)。每个颜色决定沿用原三个嵌套阈值的严格比较。q 严格增加，r 非降，各 r 不小于倒数第二个指定 q。程序同时保留原 q 的上下幂窗。两个出现于不同 Γ 行的 112 或 122 仍按原字列表逐次计数。exact_sharp 逐项对应旧 sharp，original_rank_iff 证明整列向量足以恢复原标记与尾整数。真实秩最高为 200。使用 Fin(2N+1) 作为坐标环境时，加性素数测试始终是 M<N 且 N−M 为素数。

令 S_w(x)=smoothTransition(1+x/w)。W 等于逐坐标的低端因子之积乘 B+(1−B)AW_word。低端因子是 S_(1/2)(p_i/N^(1/90)−1)。每个原位均≥N^(1/90)，外权的非零支撑最终均≥N^(1/96)。A=S_h(1−y)，B=S_(c/2)(c/2−y)，y=M/N。W_word 是全部原仿射门的 S_δ 乘积。每个原窗内物理 W=1，处处 0≤W≤1。薄径向补片按整字加入一次。它在 y≤c/2 取 1，在 y≥c 取 0。

当外权为正而尖窗不成立，整数或者处于 0<y≤c，或者处于临界径向壳，或者有一个具体原门失效而其面距离≤δ。失效门映到上包已付的真素数对条带。两个位置不同，值允许相等。尾秩重新求和时，低于原前缀长度的旧向量集合为空，所有其它原秩逐一还原。普通权的超额至多是同一次 totalAmbient。正测试先逐点比较。此前已核的径向粗数、非径向非单位粗余商和真目标排除费用在此处合并为 εΘ_clamp。该步使用固定宽度后的逐 N 正包含，未把两个上极限相减。

## 实际归一化导数与所有二进块

原正权按 P5RoughLogGridSmoothTensorPartition 的真实伸缩标签切分。取 L=ceil(log(2N)/log 2)，原网格端点化为 0,1,…,L+1。实际非零的一维标签 j 满足 j−1<log₂ p<j+1。对整个真实素数环境，所有张量之和严格等于 1。restore_sum 同时对普通质量和加性素数测试还原整字。restore_signed 在真实同余指示与 (M,d)=1 的互素中心之差上使用同一批标签和同一 ρ，先求和再取绝对值。所有原字及秩合计的块数至多 20·201·(3+log N/log 2)^200。这一因子只计分布误差的块数，普通边界费用仍计一次。

第 j 盒在完整正坐标上取 p_i=exp(j_i log 2+u_i)。chart_identity 给出定义了整个正实图的权重恒等式，chart_at_prime 在每个真实素数元组上还原该式。非零图的每个 u_i 在 (−log 2,log 2)，因此其支撑包含于固定闭立方体。仿射门在 u 中的斜率为固定行除 log N，行含 p 和各 q、r 的原位置。低端因子是 log p_i 的光滑标量函数，在两端为常数。两个径向因子也是 log M 的光滑标量函数，在两端为常数。紧过渡段给出任意阶导数上界。对真实门逐次使用 Fréchet 链式法则和乘积的 Leibniz 公式，得每一混合阶数 d 的统一常数。common_chart_budget 在 N、真实盒、盒内点、原 20 词和所有尾秩之外选择 B_d。坐标方向允许重复。这里的导数是实际乘法坐标的归一化欧拉导数，常数并未作为输入。

原 HB/Fourier 下游若使用 P5AdmissibleAllRankIntegerGeometricFamily.Family 这一特定结构，还要将真实物理坐标的全空间光滑零延拓与其 eulerWord 的记号连到本包 chart_identity、compact_chart、common_chart_budget，或直接使用原稿的归一化正实 dyadic 图。该结构的旧泛型声明本身不是本包的原几何或 PP 供应。本文没有把纯指数墙套到 M=N 上。

## 稿内 U* 价与有限正上筛

original_positive_family 给出一组先于 N 的 h、δ、c 及 η,γ>0，令 J=cost·intervalMass(833/2500,1/3,ν)/4。真实几何普通质量原有 J 的上极限，外权普通质量的上极限至多 J+η。对于这同一固定外族，任意额外 e>0 都有最终上界 J+η+e。真加性素数计数由该 W 支配。旧 paper_upper_price_fits 给正余量 β，取 η=β/(2K₀)、γ=β/2。于是 (K₀(J+η)+γ)H_N 最终不超过原 switchCost·Θ_clamp+εΘ_clamp。全局正计数常数 K₀=8452171/1250000。原种子价使用 K_seed=681/100。两个常数的位置与原归一化相同。

physical_positive_upper 直接使用 T24 revision-02 的 fullPrimeTupleMass_le，再对全部原正出现及尾秩求和。保留指定 Bank 和原参数 round,n,e,q,a,ω,N,τ,L，以及 hL、hwL、hwz、hz。真源素数组上限 P=2N，目标仍是 N。模数集是 moduli N (N^ω)，ρ 是原 finite-fallback 的整体系数。终端右侧为实际普通 W 质量乘 physicalDensitySum，加整字互素修正、一个带符号的整族 Part3.primeProductSignedError，以及原小素数费。M>N 的顺滑支撑参与同余、互素中心和完整误差。该部分的真实加性素数测试为零。T24 的整数绝对差桥在逐项求和后的除数上界中保持正向。没有逐模数删除负 ρ，也没有重新把 M≤N 写进 W。

仍须把实际的物理密度与同 ρ、同参数调用相接，支付真实修正和小素数费，并证明当前完整 W 上的有符号 exact-coprime 分布估计，才能把原 U* 价用于 tested 计数。其它经典种子项、增强根、全部前代反馈与 430+11 H430 冻结细胞不在此处结清。row12 和 7/2 根权重的前提及数值沿用原稿。 

