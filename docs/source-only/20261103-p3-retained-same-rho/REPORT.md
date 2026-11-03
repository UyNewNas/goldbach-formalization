# P3.6 — actual same-rho retained row and mother assembly

Base commit: `17813c8649f564a4c960c6ea26c81f04fa643fcc`.
Base tree: `9d6e09f41474f74c74860c537b288756ca9f5713`.
Branch: `chatgpt/p3-retained-same-rho-20261103`.
Packet: `docs/source-only/20261103-p3-retained-same-rho/`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED / FULL P3.6 OPEN.**
No Lean/Lake/compiler, finite guard, numerical producer, kernel replay or explicit CI dispatch was performed. The verification driver is unexecuted. No independent review or transitive-axiom acceptance is claimed. Production imports, prior packets, main branch, manuscript, constants and the excluded full87 work are unchanged by this packet. Commit publication requests skipping CI.

## What changed

The preceding packet supplied all-discarded joint payment and an exact original-Gamma-to-retained reduction. It did NOT bound the retained rows. This continuation actually invokes R18's local conductor estimate on the unchanged original upper rough-MODULUS-rank-at-most-two coefficient, then sums both chosen grid indices and the complete literal mother list with the same rho. It connects the result to the previous joint reduction and explicitly instantiates the existing compact extended-third upper policy.

The distinction between rough modulus rank and outer Gamma-word rank is retained. This is not a statement about every rank or every physical coefficient class.

## Exact coefficient and source

`upperRho` is literally J's `rankRho retain N cap w z Lbeta 2`, with

- `w=N^(nu*epsilon^2)`;
- `z=N^(nu*19/96)`;
- `Lbeta=N^(nu*epsilon)`.

The actual beta sign and the complete beta factor are unchanged. The allowed parameter range is `0<=nu<=1`, `0<=epsilon<=1/1000`, and `0<=kappa<=1/100` (strict positive kappa for the joint discarded composition). No auxiliary analytic level is substituted into rho.

`cartesianRow` is a DIRECT finite sum over the original `headCarrier` and `rootComplementLabels`, with the original `complexWeight`, `betaLabel` and `gammaKernel`. It is not defined as a desired error or as original-minus-remainder. Nonoccupied rows are proved zero for this exact sum.

`cartesianRow_eq_character` consumes Q's exact physical-row dictionary and O's natural-to-character rectangle identity. It retains the original AP-minus-q-coprime-mean, complete complementary multiplicities and moving target residue `(N : ZMod q)^(-1)`. Target coprimality is established for active rho before invoking this identity.

`signed_row_le_local_conductor` uses R18's ACTUAL support theorem on the SAME integer rho. It supplies positivity of q, q-coprimality to N, coefficient height <=1, and `q<=floor(x^(9/20))` on occupied rows. It then bounds the signed modulus sum by the existing complete local conductor norm sum. There is no caller support/energy/conductor licence.

## Local-to-original row estimate

`exists_chosen_signed_rows` invokes `exists_chosen_all_mother_local_conductor`, not a new PP assumption. Occupied complete scales obey `N^(1-kappa)<=x<=N`; the imported original-scale transport converts the local error unit to N. For fixed natural A and positive mesh exponent B, it supplies a C>0 and one original-N threshold before every later pair, mother, grid row, allowed nu/epsilon, retain/cap policy and finite modulus subfamily.

Its conclusion is the actual signed complex row bound `C*N/(log N)^A`. No per-pair or per-word threshold is chosen after arithmetic data. Both original source rows and their L1/L2/Abel costs remain the existing R18/Q/O/P suppliers.

## Complete grid and literal mother summation

`headWordKernel` directly sums the nonempty prime-head rows over both indices. `headWordError` and `headPairError` use the same rho and the ORIGINAL mother occurrence LIST, retaining every repeated word. Empty words are NOT silently assumed absent: `emptyWordError` is their original directly defined smooth-trimmed root-label source.

`retainedPairError_eq_head_add_empty` proves an exact equality with the prior packet's retained source. No count of words or finite guard is evaluated.

For `K=ceil(log(N)/delta+1)` and `delta=boundaryLogMesh B N`, R18 already supplies `K^2<=9*(log N)^(2*(B+1))`. The local row theorem is requested at accuracy `A+2*(B+1)`, then the actual grid sum and literal mother sum are performed. This yields

`abs(headPairError) <= C*N/(log N)^A`

for each original pair, with ONE threshold before every pair. The head-profile cost is not charged a second time: it was paid inside R18's local theorem. This does not claim that arbitrary additional coupled Fourier/Mellin profiles have been supplied.

## Honest outer sum: the cost cannot disappear

Define `selectorMass N sigma = sum_(t in pairSupport N) abs(sigma t)`. The complete outside sum satisfies

`abs(headJointError) <= (C*N/(log N)^A)*selectorMass N sigma`.

This is a proved finite-sum consequence with the SAME coefficient. It is NOT an absolute uniform PP estimate for all bounded selectors: bounded pointwise height alone does not bound this L1 mass. In particular selectorMass is not manuscript Theta and has not been replaced by it.

The prior all-discarded estimate remains the stronger JOINT estimate and is not multiplied by selectorMass. Using the prior exact chosen mesh/ceil grid, the new terminal theorem proves

`abs(E_Gamma_low - E_empty_low) <= (C*selectorMass + eta)*N/(log N)^A`.

The modulus carrier is `[1,N]`; `upperRho_active_mem_target` proves that it contains every nonzero coefficient of this low branch, including the full beta factor. This carrier is only an exact finite enumeration carrier. `physicalUpperModuli` is the ORIGINAL `actualSmallRoughModuli`. The new `upperRho_test_actual_moduli` proves equality of the low signed functional on these two carriers via their intersection, and its two consumers transport the actual Gamma and empty-word functionals. This is NOT a construction identifying original t-dependent rootQ with a common causal physical Q; no high-branch support below N is claimed.

## Actual policy and untouched high branch

`fullUpperRho` is the original `actualSmallRoughRho`, and `highUpperRho` is the existing `remainingRho` with rough rank cutoff two. Neither is defined by subtracting an error. J's existing coefficient identity is lifted to the actual joint Gamma source:

`E_Gamma_full = E_Gamma_low + E_Gamma_high`.

The final declaration

`ImbalancedChen.P2GammaActualUpperLowRankReduction.exists_actualCompact_fullUpper_reduction`

instantiates `retain = actualExtendedThirdCompactUpperPolicy e h m N false`, an actual existing original coefficient, and proves

`abs(E_Gamma_full - E_Gamma_high - E_empty_low)`
`  <= (C*selectorMass + eta)*N/(log N)^A`.

All three final functionals use the ORIGINAL `physicalUpperModuli`, including the untouched high branch. The exact low-carrier identities, rather than an assumption that the whole high branch lies below N, transfer the proved estimate back to this physical carrier.

Fixed height, A, kappa and eta precede C and the common threshold; all later N, allowed nu/epsilon, e/h/m/cap and bounded nonnegative selectors follow it. The high branch, empty low-word lane and outside mass stay explicit. No equality of this compact policy with the uncompleted final full87 policy is claimed.

## Reused evidence and scope

The S29 actual-PP review, R18 report/registry and the relevant R18 proof bodies were read at the pinned base. Also read Q's complete-scale and physical-row dictionaries, O's small-conductor interval bridge, P's local conductor signature and original-scale transport, M's exact character/principal dictionary, and J's actual low-rank coefficient definition/support sources. The prior two local proof files used in the composition were checked against their Git blob identities; both matched. Relevant archived paths are recorded in REGISTRY.

These are exact finite-source/estimate compositions. The original manuscript itself was not newly fetched; manuscript provenance is inherited from the reviewed source chain. No exhaustive search of unpublished local work or independent review of this new packet is claimed. The source-only dependency closure is not installed or compiled here.

## Remaining obligations

1. Actual selected causal-family and common physical-Q identification, with the required quantifier order and selector supply.
2. Positive-Theta relative conversion on that real family. The displayed L1 mass cost is not a solution of this obligation.
3. Full high-rough-rank/enhanced and other physical coefficient classes, additional coupled profile norms, and their actual post-loss support.
4. Empty-word source handling or a proof of absence on the actual required family; no such absence is assumed here.
5. Final actual PP assembly and the downstream hUniformPP/hLower/hUpper targets, plus their independent spectral prerequisites.
6. Dependency installation, exact-source elaboration, kernel/axiom audit and independent review.

## Proposed tracker delta (not an external tracker mutation)

```text
黄｜P3.6 把估计实例化到同一rho和实际PP源族
    蓝｜原上界rough-rank<=2保留行的同rho字符核接合、完整chosen-grid/母词求和源码
    蓝｜接回原始joint Gamma及实际compact upper系数的带显式余项归约源码
    黄｜外层实际causal族/共同物理Q、positive-Theta、空母词及高秩/增强分支和全PP总装
```

Only these narrow source-coverage increments are proposed blue. There is no new green/kernel-accepted item and no claim that the whole parent is blue.

## Verification handoff

Three proof modules, REPORT, REGISTRY and an unexecuted VERIFY driver are added. REGISTRY records raw SHA256, Git blob IDs, bytes, lines and declaration locations. Completed checks are local byte hashing, declaration/import inventory, JSON parsing and a comment-stripped lexical scan for proof admissions/unsafe/evaluation forms. These are NOT Lean elaboration or a proof checker.
