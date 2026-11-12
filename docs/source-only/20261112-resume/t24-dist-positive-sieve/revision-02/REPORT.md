# T24：完整正外权的有限 integer-shift 上筛桥

状态：SOURCE_ONLY / YELLOW / UNCOMPILED；`compiled=false`、`kernel_verified=false`、green credit 0。未运行 Lean、Lake、LSP、stage、proofguard、数值 producer、远端写入或 CI；只写本独占目录，未改原 continuation、HEAD、index 或其他任务目录。

基线是 bare mirror `goldbach-proof-github-sync-20261110.git` 的 `3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9`。复用旧定理而不改其正文；见 REUSE.md 与 REGISTRY.json 中的基线物件及内容 SHA。

## 复用判定与新增范围

旧 `P4BIntegerShiftOuterCarrier` 已证明全部自然数 M,d 的
`d ∣ ((N:ℤ)-(M:ℤ)).natAbs ↔ Nat.ModEq d M N`，并已有自然数 carrier 的完整同 rho Fubini。旧 `P5zPositiveFamilyBudget` 已有任意 rank、独立参数 k,P,N 的 `p5z_labelledDistributionError_eq_primeProductSignedError`。以上均直接复用，未新增 Nat.dist/同余引理，未再证 prime-product 重数。

零新映射不足：旧 P5z labelled 正测试上筛本身要求整个 S 的 f(t)≤N；旧 P4B 上层是 RealB 的自然 carrier，旧显式 labelled outer pushforward 限 rank 2。T07 的真实 smoothRank 使用任意 k 的标签族，且 W 在 N<M≤(1+h)N 仍可正。旧通用 `p5z_markedProductWeight_sum` 也可以在已有全支撑≤P的证明后转接；此处用更短的任意标签 Fubini直接调用旧同余引理，完全免去新支撑前提及产品 pushforward 转换。

仅新增两个模块：

- `P5zLabelledIntegerShiftPositiveSieve`：完整标签的 congruence Fubini、exact-coprime mean、mass/density recenter、真实正 primeMass 上筛、独立 tuple cap P/target N 的 small-prime fee，以及有限 occurrence 汇总。
- `P5zFiniteFallbackPositiveOuter`：把原 `P4AOriginalFiniteFallbackCount.upper_majorant` 原样接入。B,r,n,e,q,a,omega,N,tau,L、原 moduli、原 rho/beta attachment 均不改。全 prime-tuple 特化直接复用原 Part3 signed-error equality。

## 有限数学内容

记 X(t)=`((N:ℤ)-(f t:ℤ)).natAbs`。无论 W,rho 的符号如何，完整 S、完整 Q 都满足

`Σ_t W(t) physicalDivisorSum Q rho X(t)`
`= Σ_q rho(q) C_q/φ(q) + E`
`= mass(W) physicalDensitySum Q rho + coprimeCorrection + E`，

其中 C_q=`p5z_labelledCoprimeMass S f W q`，E 是未改定义的 `p5z_labelledDistributionError S f W N Q rho`。M=N 时 X=0，全部 d|0；M>N 时用真实的负差绝对值。两类点均保留在 C_q、mass 与 E 中。

当 W≥0 且原 all-natural upper majorant 成立，得到

`p5z_labelledPrimeMass ≤ mass*density + coprimeCorrection + E + smallPrimeMass`。

正测试的实际条件仍是 `f(t)<N ∧ Prime(N-f(t))`。只有此条件成立的分支使用旧 `integerShiftNatAbs_eq_natSub_of_le`。其余分支（包括 f(t)≥N）测试为零，由整个 divisor polynomial 非负支付；从未要求每个 rho(q) 非负，也未取 rho 的正部。

`smallPrimeMass_le` 对 S⊆`labelledPrimeTuples k P`、W≤B、B≥0 给出 `B*(k^k)*z`。证明只对真实 small-prime-test 支持按 partner p=N-M∈range z 分纤维；在各纤维中 M<N 可推出 M=N-p，再用旧 `p5z_marked_prime_product_fibre_card_le`。完整主项、完整 E 与 PP 权重不作此过滤；不需要 P=N 或整个 S 满足 M≤N。可直接取 P=2*N，W≤1，z=ceil(cutoff N)。

## T07 消费入口及正负方向

T07 真实对象是 `Part5OriginalH430ClassicalSmoothRankAccounting.smoothRank`，k=`rank cs.length r`、S=`Part3.labelledPrimeTuples k (2*N)`，W=`Part5OriginalH430ClassicalSmoothRankSupport.W cs · ν δ h c`。由 T07 的 `W_bounds` 可取 hW≥0 与 B=1。展开其 testWeight 后，ordinary smoothRank 等于本桥的 labelledMass，tested smoothRank 等于 labelledPrimeMass。这里未 import T07 尚未冻结的新源，也未重复其 smooth/Fourier/全 dyadic 恢复。

`fullPrimeTupleMass_le` 取 P=2*N 时，余项严格是

`Part3.primeProductSignedError k (2*N) N Q rho W`。

中间参数 2*N 是 slot cap；第三参数 N 才是移动剩余类的原目标。原 prime_test 与目标 N 均不变。

`sum_physical_eq_main_add_errors` 允许 dependent branch type、任意有限真实 occurrence 集 I、任意有符号 occurrence 系数 a_i、任意有符号标签权 W_i：完整等式可先合并全部 r/词、重复出现及正负项。

`sum_primeMass_le_main_add_errors` 的单侧上筛只允许 a_i≥0、W_i≥0，保留一个 `Σ_i a_i E_i`。负 occurrence 若进入最终 upper 目标，必须有相应 lower 方向的真实估计；不能将本 upper 乘负数后仍声称 upper。完整 signed identity 本身始终可用。取绝对值只能针对已合并的整个 signed sum，不能从此桥推断每支或每模数的绝对值预算。

## 明确保留的义务

本桥只完成 finite algebra/inequality，不声称 Part5 已闭合。后续仍需：

1. 对原 actual rho/commonQ、原参数的密度供应；未添加密度上界假设来冒充定理。
2. T07 真实 W 的 ordinary mass/collar、exact-coprime correction，以及涉及的 cutoff 定义等同或适用范围证明。
3. 原 actual smooth family 在 P=2*N、target N、同一 rho 与 Q 上的 signed PP 适用及定量预算，或对全部真实 occurrence 合并 signed sum 的合法供应。这里仅复用 equality，不证明或假设任何未证 PP 估计。
4. 原 upper_majorant 的 hL:1<L、hwL:N^omega≤L、hwz:N^omega≤cutoff N、hz:cutoff N≤N。其 all-natural x 量词没有扩大，直接取 x=X(t) 即可。

静态检查仅确认新源无 sorry/admit/axiom、声明与映射列表、基线复用文件内容及 SHA；不替代 elaboration 或 kernel 验证。最终冻结以 REGISTRY.json 的 SHA 为准，提交 T09 独审，未获审前不作接纳或绿色结论。

## 修订 02 选本

T09 独审确认首版 smallPrimeMass_le 的 `Finset.sum_filter _ _ _` 多传一个显式参数：锁版 Mathlib 的 s 是隐式参数。本选本唯一 Lean 修订为显式 `(s := S)`、原 predicate、W；所有声明、数学前提、结论及安装映射不变。原首版文件、REPORT、REUSE 与 REGISTRY 全部保留。实际特化模块逐字节不变。

T09 已审其余证明与 same Q/rho 特化，未见第二个必改处；正式 verdict 以其独立 review/allowlist 为准。两份 source-only 模块仍未编译、未 kernel 验证，green credit 0。
