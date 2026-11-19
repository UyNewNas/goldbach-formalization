# P1.4 — true physical divisor d on original prime receivers (finite bridge)

Status: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**, P1.4 **YELLOW**.

## Recovery and frozen baseline

- Previous live task HEAD actually read: `4a1fc6be5ce696842e907ac84a406140517f01af` on `chatgpt/p1-full87-physical-level-separation-20261120-0505`.
- New isolated branch: `chatgpt/p1-full87-true-physical-prime-divisor-20261120-0610`, based on that exact commit, not master.
- New proof source commit: `9c50d4fc1a08e65cb6926d7a44311bc697d282e7` with [skip ci].
- Source: `docs/source-only/20261120-true-physical-prime-divisor/P4AOriginalFull87TruePhysicalPrimeDivisor.lean` (141 lines); Git blob `2484bbfe455c0ae6f6ee87b0662b7a28127b377d`.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Lean `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `09b97db5764ade1246bfb77206baa1b124760958`. Constants `c=49044063/25000000`, `K=8452171/1250000` unchanged.

## Genuine finite arithmetic reduction — candidate Lean proof, not compiled

**First:** For the original signed coefficient
`rho(d) = actualSmallRoughRho retainOdd N cap w z L d` and *the same* physical support `S=actualSmallRoughModuli retainOdd N cap w z`, define the actual physical divisor sum `R(n) = physicalDivisorSum S rho n`. On the actual injective prime receiver set `chenPrimeReceiverSource N`, finite Fubini and the existing Chen source fibre lemma give:

`sum_{n in chenPrimeReceiverSource N} R(n) = sum_{d in S} rho(d) * (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)`.

Thus the PP modulus is the **true small/rough divisor d | n**, not the previously invalid upper shell `Q=n=ab>N/2`. This is the genuine finite `R_N(n)=sum_{d|n}rho_N(d)` direction for an original retained coefficient (policy remains a parameter).

**Second:** For even `N`, apply the **existing proven-in-repository finite** `chenInitialBoundingSieve_rem_eq_source_discrepancy` with `actualSmallRoughModuli_coprime_target` at each physical `d`. The candidate sums over the SAME `rho` and rewrites the exact prime receiver total as:

`M * physicalDensitySum S rho + sum_{d in S} rho(d) * finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) 1 N d - sum_{d in S} rho(d) * chenPrimeDivisorCount N d / phi(d)`,

where `M = #(chenAdditivePrimeCarrier N)`. The modulus-prime exception is a **negative term**, not zero, and the centre-prime correction was already paid exactly in the AP expression. Signed rho is unchanged and no arbitrary AP mean has been inserted.

These are finite source identities: they neither prove an asymptotic AP estimate nor give an application of manuscript `eq:current-PP` (whose labelled-prime-product, smooth `W_N`, mean `X_W^(d)/phi(d)`, coefficient class and fixed-before-N quantifiers still require matching). The proof does **not** yet aggregate `sharedRankFour` and all fifth/sixth ordered occurrences into the *single original* manuscript rho.

## Evidence and checks actually made

- Read prior live HEAD, `REPORT.md`, `REGISTRY.json`, `INPUT_BOUNDARY.md`, `HANDOFF.md`, its full Lean source; inspected original `ImbalancedChen/ActualSmallRoughAttachment.lean`, `FiniteUpperCarrierCore.lean`, `ChenInitialPrimeSource.lean`, `ActualUpperPolicyFiniteBridge.lean` and related physical-rho bridge files. No applicable `AGENTS.md` at root/docs/docs-source-only found (404).
- New Lean source was created and remote-read: source commit `9c50d4fc1a08e65cb6926d7a44311bc697d282e7`, blob `2484bbfe455c0ae6f6ee87b0662b7a28127b377d`, 141 lines, forbidden escape scan negative. This proves GitHub storage, NOT Lean elaboration.
- Locally, exact rational diagnostics over 1,752 randomized finite prime-receiver/policy-independent signed rho instances for even 4<=N<150 passed both identities with zero mismatches. These **do not test** the project's actual policy or perform type checking.
- `lean --version`, `lake --version`, `elan --version` each exited **127**, command not found. Container memory.max **4294967296 bytes**; Git network DNS in container unavailable. Thus **UNCOMPILED / UNEVALUATED**, no fixed-pin Lake staging, kernel replay, transitive axiom audit, independent review.
- No CI dispatched, Codex, user computer, extra resources, pin upgrade, master changes, merges, force push, or source outside this proof packet.

## Still open (do not claim closed)

1. Fixed-pin Lean staging and elaboration of these two candidate theorems; fix real errors if any.
2. Instantiate `retainOdd` with actual frozen fifth/sixth `sharedRankFour` policies, signs, two distinct balances, original ordered occurrence list and original full-87 parent history; prove a **single** physical `rho_N(d)` coefficient pushforward rather than summing unrelated filters.
3. Authenticate final physical cutoff and squarefree/prime-class licences, fixed smooth labelled-prime-product `W_N`, exact coprime `X_W^(d)/phi(d)`, and manuscript same-rho signed PP input with real dimensions.
4. Pay signed PP, modulus-prime correction, lower-half primitive/modulus/centre, ordinary integral, raw/filtered losses versus `H_N` without duplicate reserve or repeated rounding.
5. Saved87 entire archive/numerical source, BOTH/rank9/changed/tagged and independent compiler/density reserves; kernel replay, transitive axiom audit and independent check.

Result is a positive actual-`d` finite bridge following the previous disjoint-support diagnosis, not closure of P1.4 or the full theorem.
