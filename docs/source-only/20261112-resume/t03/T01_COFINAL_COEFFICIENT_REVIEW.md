# T01 同系数 All22 合流独审

**源码数学通过。** 本次独审对象是 T01 新写的一个定理 `P4AOriginalFiniteAll22CofinalCoefficient.exists_cofinal_same_coefficient_density_and_count`，源文件 6043 字节，SHA256 `3e4ef38c9abc25e35ef446f52ed9e4b2bba112743445e19f64937e7eeaa9a604`。独立核对的两端分别是 P4 已发表的同系数十九槽计数界和 T09 已独审的真实前三槽付款。两端的 `lowerEarlyDefect` 均来自同一份 `P4AOriginalFiniteAll22RawLedger`，Git blob 为 `88a37861a9d5bdfaec4cdb34196cc0fe5f91afe2`。

## 参数次序

1. 给定正的 `eta,eMax`，分别将 `eta/2` 送入 P4 的 `exists_same_coefficient_density_and_count_with_early_defect` 和早期的 `cofinal_actual_early_defect`。沿 P4 的 (m,r) 先后选择，取两个 (n) 下限的最大值，再取两个正 (E) 的最小值。所得 (E≤eMax)；同一个有理数 (e) 同时满足两端的严格范围。
2. 固定 (0<a≤1/800) 和任意 `qMin,mMin`。P4 给出对所有 (q≥q₀) 和所有允许的 (a) 有效的门槛 (q₀≥qMin)。早期付款在这个 (a) 上选出单个 (q≥q₀)，且 (q>0)、(256∣q)、`mMin≤refinedMesh q`。同时取得一个 (N_E≥2)，对所有实数 `omega≤a` 和其后所有足够大的偶数 (N) 统一成立。这里没有交换早期付款的 `∀a∃q` 次序。
3. 此后固定正的 `nu,v,betaMax`，满足 `nu*v=19/96`。P4 在上述同一个 (q,a) 上选择一次 `beta,k,NC`。逐项保留 `0<beta<1/8`、`beta<betaMax`、`beta²<v`、`nu*beta²<a` 和 `nu*beta<1/1000`。P4 计数源内部以 `min betaMax (h/nu)` 选 `beta`，满足十九槽 raw 源所需的 `0<omega<thirdPrefixRho` 与 `omega≤h`。正的 `omega=nu*beta²` 也满足早期付款的参数域。
4. 最终 `N0=max NC NE`。对同一个 (N≥N₀) 同时使用两式。参数 `tau=alignedWidth (jointIndex (bank m) (data e q a).m) k`、`w=N^omega`、`z=cutoff N=N^(19/96)`、`L=N^(nu*beta)`、`Q=moduli N w` 以及 `rho=FiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L` 均与 P4 原结论逐项一致。两个阈值只合并一次，数值 (N) 选定之前已选好 `beta,k`。

## 密度、编译费与计数

P4 的旧系数是 `currentK−densityReserve−exactSlack+lowerEarlyDefect+eta/2`。对该 `omega,N` 的物理早期差严格小于 `eta/2`。使用已发表的 `ImbalancedChen.densityScale_pos`，(N≥2) 保证 `singularSeries N / log N>0`。新上界是

```text
(currentK − densityReserve − exactSlack + eta) * singularSeries N / log N
− p4aActualPresieveCorrection (F (bank m) (width r) n (data e q a) omega N) N N w z
```

右侧保留同一真实预筛修正。P4 已用一次 `compilerReserve` 建立原界，新证明显式继承原 `compilerExpense` 严格界及 `rho d≠0 ⇒ d<N^(599/1000)`。计数端乘以非负有限基数 `(realHalfProductSource b N T).card`，因此无需假设该基数为正。对每一个 (0<b<1)、(T>0) 且 `ceil(z)≤T^(b/(1+b)))，原 `RealB b N` 界仍含同 (Q,ρ) 的 `realPhysicalDistributionError b N T Q rho`、`ceil z` 和 `T+1`。

## 选择与核验范围

本轮有一个新的 Lean 源和一份原作者选择登记 `af7d9c18c9bd9c31cebcdf06b6bf28b3cd063a07ab47f1394856107961f7ab41`。白名单另列两个直接导入、P4 的十九槽内部前提、原 `densityScale_pos`、T09 早期原审，以及安装用的作用域补丁。三个未上传的 P4 草稿均不在此定理的直接或新增依赖中。

源码层面的离散与均匀参数已够作这个合流。全模数真实有符号分布误差的付款、附加 PP 精度对同一次 `beta,k` 的要求、整个包的安装和 Lean 核验仍各有独立职责。这里保留原 `densityReserve` 和 `exactSlack`，没有把它们用于分布误差。未执行 Lean、LSP、有限守卫、数值证书或 CI。
