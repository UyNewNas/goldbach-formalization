# 经典 U3 原坏 Γ5 总付款与五倍种子

**源级范围。** 在原稿 second-seed-stable-prefix-extension 的经典分支，拒绝条件是 pa²b≥Q，等号属于坏角。选定三份后继源把此前逐原标签的有符号余项求和，并把所得上界接回同 Q 的原种子。可确认经典 U3 坏 Γ5 的这项换算及其预算。price 中 K=681/100，是原 switched 换算所用的常数。本轮未运行 Lean、LSP、guard、数值重放或 CI，kernel 验收留待远端原工程。

**完整模数和重数。** Pool.actual_bad_whole_pool 中 D=pab，普通上权非零才保留 r。原 root_coefficient_full_Q 给 Dr≤Q 和所需互素，原经典几何给 Q≤N^(1/2−τ)。对固定 D，r↦Dr 单射。实际有限误差及其 true-li、删素数均值改变量由 trueError(N,Dr)+(3/log 2)log N 上控。另一个逐标签的中心费用 #primeFactors(N) 放在同池的 k=D，因为 1<Q/D。两份合计至多二倍原非负池。每个 k 的标签由一个有序三元组 (p,a,b) 确定，其中各素数都整除 k 且 ≥N^(1/200)。k≤N 及原素因子基数引理给每坐标至多 200 个选择。对整个根子集一次换序后有 2·200³ 的绝对常数，不依赖原 mesh、p 或子集大小。

**共同分母及参数次序。** Payment.actual_Gamma5_at_common_mass 先固定 0<τ≤1/12 与 ε>0，存在对所有晚偶数 N 生效的共同门槛。随后对每个满足 1/(n+1)≤11/384 的 n 和每个 B⊆classicalBand(N)，逐 p 求和的
`max(原 Γ5 母计数, 真测试纤维) − (681/100)/4·thetaConversion·原未测纤维`
至多 ε·clampMass(N,n,τ)。原 true-li 素数 BV 只作用于一次完整 k 池，其 Oτ(N/log³N) 及 O(√N log N) 与原正宽区间质量共用同一个下界 (I/2)H_N≤Θ_clamp，I=8log(834/833)。这里是带符号总量的单侧上界，对任意 B 使用整个 clamp 的质量。在 B=clamp 时，分母和实际求和区间相同。逐标签取 max 再求和确实上控两种总计数的 max，中心和均值转换已经进入这一预算。

**接回原种子。** Credit.original_clamp_credit_after_Gamma5 在同一 N、n、τ 与原 clamp 上，设 C_p 是 originalReceiver 的真实基数。Q/p 的几何上界给 (Q/p)^(5/11)≤N^a，且原 p 满足 roughness。frozenCount_eq_original_count 在这个真实根及 pN 掩码下匹配 C_p，切口单调性把 C_p 放入原五倍种子的整数载体。local_sameQ_finite、actual_local_source_identity、mother_positive_split 在相同 Q 与实际状态给出 5C_p≤otherSeedTerms+originalBadPairCount。otherSeedTerms 明列 4:1 两锚、三个负 singles、四条 good-pair 贡献、十三个长项、W2Charge、碰撞和坏素数费用。用上述 max 上界取母项一支替换原正坏角，支付 εΘ_clamp/2。先前真实普通估计给 Σ|C_p+(E_p+S_p)−θ_p|≤(ε/10)Θ_clamp，乘五再支付 εΘ_clamp/2。因此五倍 Θ_clamp−Σ(E_p+S_p) 的上界保留 otherSeedTerms 与原未测换算价。这里 cubeCredit 只出现一次，未借用 H430 目标作前提。

**其余职责。** 原未测换算价仍以真实整数计数出现在右边。进一步的 H430 数值改进、good-pair 项、Γ9–21 的真 switched/单位面、增强根、后继四轮、430+11 与整 h34 仍需各自的付款。本包完成上一份逐标签独审中列出的经典坏角汇总和种子交接。不存在整黄色职责或 kernel 绿色的连带变更。

**身份。** 三份新 Lean 源共 17 个声明及五个直接导入，逐一核对登记及源行。两份后继作者登记内的 22 个不同引用身份经字节、SHA-256 和 Git blob 对照，含十个固定源码对象及三份发表收据。前置三源和首次独审按 T07_SWITCHED_BAD_PAIR_ALLOWLIST 原指纹复用。新白名单另列三份实现、四份作者记录和本次独审。
