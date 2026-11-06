# P1.4 — actual rank-nine **two-sided** prime window [SOURCE_ONLY]

## Frozen source and target

Continuation base: `2289412178792463fdf9d5bb88a36e50e95aadc5` on `chatgpt/p1-full87-rank9-reciprocal-window-20261106`; independent task branch `chatgpt/p1-full87-rank9-two-sided-window-20261106`. This packet imports the actual 864-line source in `docs/source-only/20261106-full87-rank9-prime-crossover/P4AOriginalFull87RankNinePrimeCrossover.lean`, blob `1c04e79c04abba8e9d657a2cc71bd6d44b12bdc5`, unchanged. The new 318-line Lean **candidate** is `docs/source-only/20261106-full87-rank9-two-sided-window/P4AOriginalFull87RankNineTwoSidedWindow.lean` blob `db367b1558160ed9aabfab286a4a451da92b8232`. No main/master modification, no CI.

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Fixed Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Fixed c=49044063/25000000; K=8452171/1250000.

## Mathematical correction to the one-sided upper cutoff

The previous invoice established a necessary upper cutoff `B*p^3 < max(Rold,Rnew)`, with `B=prod(H8)`, but did NOT establish a necessary lower cutoff. At an **actual** remaining prime `p>=2` the total-product term is redundant, while the inherited square term `J=historyOddSquareCeiling(H8)` is NOT. The original full threshold simplifies to

    T(H8,p) = max(J(H8), B*p^3).

Let `L=min(Rold,Rnew)` and `U=max(Rold,Rnew)`. The prior exact decision-crossing condition becomes

    L <= max(J, B*p^3) < U.

The candidate proves a **disjoint** decomposition:

    HISTORICAL SHELL: L <= J < U and B*p^3 < U.
    CUBIC ANNULUS:    J < L <= B*p^3 < U.

A historical ceiling in the crossing shell permits primes **below** the cubic lower cutoff, so it would be wrong to impose `L <= B*p^3` on every crossing prime. The annulus lower cutoff is valid precisely when `J<L`. Exact equality at `L` is included and equality at `U` is excluded. Two identical frozen levels admit no crossing.

The proof packet supplies the per-original-occurrence realization using `owned87_eighth_state_exact_carrier`, disjointness, exact equality of the original `rankNineReciprocalCrossingCost` with HISTORICAL plus ANNULUS prime-harmonic list sums (one occurrence, one cost), conditional vanishing of the historical fee when `J<L`, and the corresponding old-minus-new finite upper bound over the SAME owner/trim eighth-state list of any actual Cell. Actual physical prefix mass `|s.mass*prod(g_N selectedPrefix)|`, signs and occurrence multiplicities are preserved. This is not a new policy, prime distribution estimate, or a reserve debit.

## Checks and exact status

- Read and compared the branch/head, latest REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF and the full predecessor file; read actual eighth-carrier, frozen-level source, inherited-square ceiling, original same-signed helper, Chen prime-density supplier and fixed manuscript. No AGENTS.md was found at root or source-only ancestors.
- Independently tested **25,000** exact-integer synthetic history/level pairs, including **18,741** threshold/ceiling equality setups: **3,907** historical-shell, **5,382** cubic-annulus and **15,711** noncrossing cases, zero mismatches; this is NOT saved87.
- Source blob `db367b1558160ed9aabfab286a4a451da92b8232` was returned by GitHub. No mathlib/Lean elaboration or execution; source remains **SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT**.
- No kernel replay, transitive axiom audit, independent review, full original 87 archived numerical replay, prime AP/centre/modulus estimate, uniform same-rho prime-harmonic asymptotic, or reserve payment.
- The new source contains no new axiom, sorry/admit/native_decide or unsafe escape by static scan. This scan does not establish Lean correctness.

## Remaining obligations

Actual full-87 common RealizedHistory is not globally supplied. Uniform same-rho harmonic payment must treat the historical-shell *and* cubic-annulus regimes separately, on actual frozen parent/cap levels at the same source; a cubic annulus estimate alone is insufficient. The original attachedLeafTest full-q primitive/AP, centre, modulus terminal mismatch, rank>=11 deletion ledger, sixth filter, ordinary residual integrals, saved87 original gains, changed/tagged and both reserves remain open. Independently compile and kernel-replay candidates before granting green status.
