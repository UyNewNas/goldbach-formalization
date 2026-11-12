# 精确复用入口

基线：`3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9`，bare mirror `goldbach-proof-github-sync-20261110.git`。

| 原模块/文件 | 原声明 | 本次用途 |
|---|---|---|
| ImbalancedChen/P4BIntegerShiftOuterCarrier.lean | P4B.integerShiftNatAbs_dvd_iff_modEq | 所有 M,d 的完整 divisor/residue 同余，无 M≤N |
| 同文件 | P4B.integerShiftNatAbs_eq_natSub_of_le | 仅真实正 prime-test 分支，把 integer shift 化回 Nat.sub |
| 同文件 | P4B.sum_weight_mul_physicalDivisorSum_integerShift_eq_same_rho_main_add_errors | 已有自然 carrier 完整框架；标签版只作必要泛化，未改原定理 |
| ImbalancedChen/P5zPositiveFamilyBudget.lean | p5z_labelledDistributionError_eq_primeProductSignedError | k,P,N 独立；特化 P=2*N、target N，直接 reuse |
| 同文件 | p5z_labelledMass / labelledPrimeMass / labelledSmallPrimeMass / labelledCoprimeCorrection / labelledDistributionError | 完全沿用原定义，保标签、原 signed rho 与 exact coprime mean |
| ImbalancedChen/P5zMarkedPrimeFamilyMultiplicity.lean | p5z_marked_prime_product_fibre_card_le | 原 k^k 重数界，tuple cap P 可独立取 2*N；无新重数证明 |
| 同文件 | p5z_markedProductWeight_sum | 已有任意固定 rank 的 signed pushforward；本次选择任意标签直接 Fubini以免增加支撑前提 |
| 同文件 | p5z_markedPhysicalWeight_test_sum | 如将来需要 marked 子族，可在 cap P 内先选 S、完整 target 仍为 N；本次 full-family 特化无需新增 adapter |
| docs/source-only/20261110-yellow-closure-10t/t04_compiler_physical_payment/successor_finite_policy/P4AOriginalFiniteFallbackCount.lean | P4AOriginalFiniteFallbackCount.upper_majorant | 原 moduli N (N^omega)、原 fallback rho 的 all-natural 非负 polynomial majorant；原参数及前提原样调用 |

旧完整自然 carrier 与 labelled rank-two pushforward 已查；没有可直接满足 T07 任意 rank full-labelled primeMass 的无 hcap 上筛声明，因此新增两条安装映射。import 名称采用原工程的正常模块映射；P4AOriginalFiniteFallbackCount 的原物理路径仍位于 source-only，映射规则不在本任务修改。
