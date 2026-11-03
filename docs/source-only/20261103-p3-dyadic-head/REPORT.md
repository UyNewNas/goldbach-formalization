# P3.6 — exact dyadic head-family reduction and joint conductor bound

Base commit: `b12b805d6ea7c7b3253ad8eefce91f2e5c4e825f`.
Base tree: `cebb56442cbf5ff3bb602333db90a0c8b6fb4cf5`.
Branch: `chatgpt/p3-dyadic-head-family-20261103`.
Packet: `docs/source-only/20261103-p3-dyadic-head/`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. FULL P3.6 REMAINS OPEN.**

Five new proof modules supply the exact interval-family construction and a finite, explicit same-rho JOINT row estimate. It has no selectorMass, pair cardinality, headMultiplicity or number-of-head-blocks factor. This is stronger than merely moving these quantities into a new premise. The actual small-conductor prime theorem and the existing complete high-conductor/quotient ledger are invoked. The scalar cutoff and logarithmic costs are still displayed; the arbitrary-log full mother/grid PP terminal is NOT claimed here.

No Lean/Lake/compiler, kernel replay, transitive-axiom inspection, repository numerical producer, repository finite guard, Codex task, connected-computer operation, child agent or explicit CI dispatch was run. A small independent Python combinatorial regression WAS run; its precise scope is below. VERIFY is unexecuted. No independent reviewer is claimed. Production files, earlier packets, locked dependencies, toolchain, constants, manuscript, main branch, external tracker and the excluded full87 work are unchanged. Publication is only to the named new branch with a skip-CI commit; no merge, PR, release or paper publication is requested.

## The problem removed from the finite estimate

The preceding packet had joint beta L1/L2 norms but retained different actual head intervals. Summing the old head energies produced headMultiplicity. This packet does NOT claim that the old multiplicity is small. It changes the analytic organization by an exact binary expansion before taking norms.

Each actual integer interval `(a_t,b_t]` is an upper prefix minus a lower prefix. At scale d a prefix n has one key `floor(n/2^(d+1))`, gated by the actual binary digit `(floor(n/2^d) mod 2)=1`. The associated left-half cell is

`(2*b*2^d, (2*b+1)*2^d]`.

All such cells at the SAME scale are disjoint. Every cell is clipped to the COMMON original window `(floor M,floor(2M)]`. The clipping is performed in the finite interval definition, not by asserting that arbitrary test values outside the source vanish. The two endpoint lanes are kept separately. The exact number of scales is `D=Nat.log 2 P+1`, with `P=floor(2M)`. The existing logarithmic depth bound is reused.

## Exact source construction

`P2GammaDyadicHeadIntervals` proves the binary cut recurrence, prefix telescope, finite interval expansion including zero/equal endpoints, clipped expansion, same-scale disjointness, and total same-scale nonnegative head mass bound. No enumeration or numerical proof guard appears in these Lean proofs.

`P2GammaDyadicHeadSource` takes occupied endpoints from the ACTUAL `clipLo/clipHi` floors. Unoccupied original rows receive two equal endpoints at the common lower cut and are separately proved zero using the original Cartesian source. The existing joint retained complement is partitioned by the prefix key and its zero/one digit gate, so each labelled old pair belongs to one beta block per scale and lane. Both old primes, every original tail position, equal-product multiplicities and quotient one survive.

`original_joint_eq_dyadic` is an equality with the original full outside Cartesian sum, before absolute values. `same_rho_dyadic_source` connects its two prefix lanes to the exact nonprincipal character rectangles at the SAME actual `upperRho`, including the full sign-selected beta factor and original upper cutoff 19/96. Positive modulus and target coprimality follow from actual coefficient activity. The original AP-minus-exact-q-coprime-mean and target residue remain unchanged.

No original rootQ, causal mark, modulus coefficient or physical level is changed by the dyadic representation. In particular, this source identity does not construct a common causal physical Q.

## Joint energies, with no hidden block count

Write `k=cs.length+3` for a full mother word `c::cs`, `V=lower delta l`, and let the complex outer selector satisfy `norm(sigma(t))<=h`, where h>=0. The preceding joint beta supplier is used with the actual digit-gated selector. At each scale and each endpoint lane, it supplies

`sum_b L1(beta_b) <= h*(2V)*(1+log(2V))^(k-1)`,

`sum_b L2(beta_b)^2 <= h^2*(2V)*(1+log(2V))^(k^2-1)`.

The new disjoint head basis gives

`sum_b L2(alpha_b)^2 <= P`.

Finite Cauchy is applied AFTER these whole-family estimates. Thus the sum of the energy products actually used by the large sieve is at most

`E = sqrt(P)*sqrt(h^2*(2V)*(1+log(2V))^(k^2-1))`.

There is no multiplication by the number of original pairs or by the number of binary blocks. The head cells need not have long lengths; the inherited complete-scale theorem is applied with the common padded head/complement lengths, not with a cell's potentially tiny length.

## Complete high-conductor payment

`P2GammaDyadicFamilyEnergy` sums the EXISTING complete high-conductor/quotient theorem, including its actual weaker-large-sieve logarithms. This is not a proof for only one dyadic conductor shell. Let `Vcap=floor(2V)`, `ell=logGauge Q`, and retain the exact upstream constants `cLS=lsLogCoefficient` and `cD=dyadicCountCoefficient`. The factor is

`Phi(P,Vcap,Q,b0,ell) =`
`  8*sqrt(P)*sqrt(Vcap)*ell/2^b0`
`  + 8*(cLS+1)*cD*(sqrt(P)+sqrt(Vcap))*ell^3`
`  + 64*cLS*Q*ell`.

At each head scale/lane the high ledger is bounded by `E*Phi`. After BOTH endpoint lanes and all scales it is bounded by `2D*E*Phi`. The quotient projectors and the original beta coefficient are inside the existing high ledger throughout.

## Actual small-conductor prime supply

`P2GammaDyadicSmallConductorFamily` turns each clipped cell into an exact original prime-SW interval by monotone clamping its two real endpoints to `[M,2M]`. Empty or out-of-window cells become equal-endpoint intervals. The two finite carriers are proved equal; there is no rounding or boundary reserve hidden here.

The proof invokes `actual_variable_prime_lowConductorTotal` and the actual complex log-hat Abel theorem. The derivative constant and the SW constant are chosen BEFORE N, all intervals, keys, selectors and conductors. For the chosen mesh `delta=boundaryLogMesh B N`, the existing profile conversion supplies the polylogarithmic norm, with fixed `W=1+2Dhat/(1-kappa)^B`. Actual occupancy supplies `x=M*V`, the positive power floors for both factors, `N^(1-kappa)<=x<=N`, and the target-scale transport. No SW, BV, PP, source mass or profile bound is assumed as a caller licence.

If the prime accuracy is A and the low conductor cutoff is `T=2^b0`, the one-scale/lane bound is

`Low = C*M*[h*(2V)*(1+log(2V))^(k-1)]*T^2*(logGauge Q)^2/(log x)^A`.

Summing beta L1, not a separate worst-case error per block, yields `2D*Low` for the complete two-lane/head-scale small ledger. The theorem is uniform in the numerical cutoff b0 after the common threshold.

## New terminal statement and exact boundary

The final module is `P2GammaDyadicJointRowEstimate`; its main declaration is

`ImbalancedChen.P2GammaDyadicJointRowEstimate.exists_chosen_joint_row_estimate`.

For fixed real prime accuracy A, positive natural mesh exponent B and `0<=kappa<=1/100`, it chooses C>0 and one original-N threshold. Afterwards it covers all actual occupied original head/complement rows, all `0<=nu<=1`, `0<=epsilon<=1/1000`, retain/cap policies, finite modulus subfamilies, bounded complex selectors and numerical cutoffs b0. The active physical coefficient fits `Q0=floor(x^(9/20))` by the EXISTING actual upper rank-two support theorem, including its full beta factor.

With Q=Q0 in the two displayed budgets, the source-written conclusion is

`norm(original joint signed Cartesian row) <= 2D*(Low + E*Phi)`.

The left side is the original complete outside-pair sum, not an invented majorant source. The proof invokes BOTH supplied ledgers, and an exact zero theorem handles the complementary unoccupied original charts. No energy, interval-family estimate, source identity, small conductor or PP conclusion is an input.

This is an explicit finite conductor bound. It is NOT yet a final `C*N/(log N)^a` theorem: b0, the stronger prime accuracy, joint divisor orders and all logarithmic costs must next be selected and balanced with fixed-before-N quantifiers, then summed over the complete chosen grid and literal mother occurrence list. The old selectorMass-bearing theorem is not edited or relabelled as a completed PP theorem.

## Reuse and inspection provenance

The new files import the previous actual block-source packet and reuse its joint fibre norms. Directly inspected pinned repository sources include Q's real head-window dictionary, O's prime small-conductor bridge, O's complete high-conductor polynomial ledger and dyadic conductor sum, P's retained geometry, and O's actual smooth-log-hat derivative/Abel supplier. Their exact paths and Git blob IDs are recorded in REGISTRY. Previously read complete-scale and actual rank-two support statements remain unchanged imports.

A few general Mathlib API names (natural logarithmic depth and finite Cauchy) were checked against the public official current documentation. Those documentation checks are NOT a check against the project's pinned Mathlib revision or a successful elaboration. The original manuscript was not newly fetched; this increment concerns the directly inspected finite source definitions and their existing analytic suppliers. No new external analytic theorem, exhaustive unpublished-work search or independent review is claimed.

## Checks actually performed

The included `check_packet.py` scans the five proof files after stripping nested Lean comments, inventories declarations/imports and hashes their exact bytes. It independently tests the mathematical binary-prefix construction in Python for caps 0 through 64: 2,145 prefix cases, 137,345 clipped interval cases and 329 same-scale disjointness cases. All passed. CHECKS contains the run output.

These finite toy tests do NOT execute Lean, prove correspondence between Python and the Lean definitions, evaluate any actual project certificate/producer, or validate the analytic arguments. The source-only proofs and their transitive dependencies remain uncompiled and kernel-unverified. No green status follows from these tests.

## Remaining P3.6 obligations

1. Balance the displayed cutoff/power/log costs, fix the required joint mother moment order and stronger prime accuracy, and complete arbitrary-log joint grid/mother assembly.
2. Identify the actual causal selected family and common physical Q, then supply the genuine positive-Theta conversion in its required domain.
3. Handle the empty mother lane and the other physical coefficient classes, including high-rank/enhanced same-integer-rho branches, permitted coupled profiles and post-loss costs.
4. Finish the actual full PP terminals and their independent spectral prerequisites; no hUniformPP/hLower/hUpper or unconditional Goldbach closure is claimed.
5. Materialize the import closure, elaborate exact sources, run kernel and transitive-axiom audits, and obtain independent mathematical review.

## Proposed tracker insertion (not an external tracker mutation)

```text
黄｜P3.6 把估计实例化到同一rho和实际PP源族
    蓝｜实际head区间双前缀二进制精确分解、同尺度无重叠能量源码
    蓝｜同rho完整joint行的小／大全导子显式付款源码（不含外层质量或headMultiplicity）
    黄｜显式cutoff／对数费用平衡与完整grid／母词任意对数精度总装
    黄｜共同物理Q、positive-Theta、空母词、高秩／增强分支与全PP总装
```

Only the two narrow source scopes are proposed blue. The whole P3.6 remains yellow and there is no new kernel-accepted item.
