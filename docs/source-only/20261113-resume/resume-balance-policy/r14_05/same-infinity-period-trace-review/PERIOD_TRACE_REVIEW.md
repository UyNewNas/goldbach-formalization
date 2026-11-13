# 同一无穷远处固定 period-64 测试的三谱迹公式

R2 冻结 66838fe32428db013cac12b46c2995ab0fc67c130e7b4c8b52d05f1339240e58 通过限定源码审查。两源 10,461 字节、11 个具名声明和两个局部实例，源码逐字节等于前件 82d7f013。谱极限改绑 f4f4787f，固定全纯轨道使用 e6960ce3；CompactTrace 取 390a1c64。逐项核查了 T21 的 weighted_geometry、positive_holomorphic_diagonal、diagonal_sum、oddProjection、basis_mass 和本级别新公式。未经 elaboration、编译及内核核验。

取任一正级别 q、正标记 m,n、Y>0、单个实际 period-64 测试 Φ。对 κ=2(j+1)，每权原 Petersson 等式的左侧为 4πΓ(κ−1)Σ_i conj(R_i(m))R_i(n)。乘 (κ−1)holWeight/(4π)，借 Γ(κ)=(κ−1)Γ(κ−1) 得到新 basisTerm。两端皆为同 Γ₀(q) 的单位宽度标架。所有 j≥0（包括权二）和每个 j 的完整指定正交基均保留。对满基每项绝对值的和，用同框 m 与 n 的两个基能量界。相应 basisCost 包含 exp(4πm)、exp(4πn)，只用于固定标记的绝对收敛。几何正模数 k 逐项有 q∣k，以同一 S(m,n;k) 的级别一 Bessel 行给出双重可和上界。实际谱及对角均保持级别 q。

令 K_q(G)=Σ_{q∣k} S(m,n;k)G(4π√(mn)/k)/k，D=1[m=n]∫₀∞J₀(x)Φ(x)dx/(2π)。前件标量公式给 D+K_q(residual)=Maaß+Eisenstein。对全纯，对角供应给 Σ_j (2j+1)holWeight_j=−2·diagonalMoment(0,Φ)。于是逐权的 Petersson 右侧对角求和是 −D，得到 K_q(oddProjection)=holSum+D。因 oddProjection=Φ−residual，合并恰为 K_q(Φ)=Maaß+Eisenstein+holSum。两处 D 的系数与符号在 m=n、q>1 时同样正确，m≠n 时各为零。

全体入射 cusp 的连续谱保留负 t 及 1/(4π)，主谱为除 cosh(πt) 的真实 transform，互补谱除 cos(πα)，全纯为 Γ(κ) 加权。该结果按固定 ℓ,Y,m,n,q 精确成立，几何和实际绝对可和。两个 Φ 的物理叠加、原共同 ω 上带行的两余项、(4.29)、完整 J、7/32 和正式叶信用均未在本包封闭。
