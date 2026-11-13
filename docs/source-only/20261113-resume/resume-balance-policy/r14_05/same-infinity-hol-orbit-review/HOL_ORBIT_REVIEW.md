# 同一无穷远尖点的固定偶权 Petersson 公式

准予作为源码发表。审查对象为 09 的 e6960ce363f0843579463e986a7621bf716be61c97e145f683001998e1c6b75b，三份 Lean，共 18,987 字节，17 个具名定义或定理及一个局部实例。对照基树 a6aec20e831aa7f905533bec69fd0f86cd2bf9b1，核查 T21 的 cuspSum_eq、denominator_modes、periodization、translated_bessel、cuspLimit_eq_Pvector、normalized_P_coefficient 和固定 mathlib 的 Fourier 系数、重编号及单位周期接口。未经 elaboration、编译或内核验证。

在 Γ₀(N) 的两个恒等标架上，周期 N 的辅助展开中，第 n 个频率只在 N 整除整数 n 时留下。取 n=Nh，经单位群加字符正交，余下的模数条件为 N 整除正整数 C，条件满足时产生系数 N，与泊松归一化中的 1/N 相消。整数子格到所有 h∈ℤ 的双射使用非零 N。零频也被这个重编号保留。N=1、C=1 和合数 C 都适用。h 和 m 在终端定理为正数。

水平系数在虚部一、实部周期一提取。被提取的不是一个潜在的同名系数，而是级别 N 上的实际 Hecke 极限向量，先用相同标架的完整 Fourier 周期化，再对正整数 h 选择其 Fourier 槽。热幅的逆因子与水平归一化相配。Bessel 项先保留 (√h/√m)^(κ−1)，乘 Petersson 原始系数所需的 (√m/√h)^(κ−1) 后恰好消去。单位求逆把 S(h,m;C) 改写为 S(m,h;C)，不改变 C 或引入别的群。

对每个 j≥0，κ=2(j+1)，左侧为 4πΓ(κ−1) 乘完整 formsBasis 的 Σ conj(R_i(m))R_i(h)。该定理固定了空间的指定正交归一基。右侧为每一 N 上的 1[m=h] 加上绝对收敛的模数级数，通项是 1[N∣C](2π/C)(−i)^κ S(m,h;C)J_(κ−1)(4π√(mh)/C)。j=0 通过 Hecke 极限包括权二。此式按标记逐对陈述。原块的公共相位在外部有限配对时方可乘入。它没有单独完成两个物理截止的求和、权变量与模数的联合交换、所需误差估计或满范围 J。该三源直接导入 T21，全纯侧没有调用旧 CompactTrace 中的 nativeR。正式叶变更为零。
