# P5.6 → h34 — actual unresolved q-to-marked debt: ordinary upper envelope

Date: 2026-11-09 UTC.
Repository: UyNewNas/goldbach-formalization.
Independent branch: `chatgpt/p5-h34-actual-unpaid-ordinary-envelope-20261109`.
Verified predecessor: `69ee64474e5832b35b159ba9d4920f31203fcdf9`.
Initial mathematics commit: `bf580c44eea11d34ce751642080f9fc50d8a0b55`.
Strengthened uniform-mathematics commit: `6d0676ab66ab049d888cc78a2a76007ed319c8bb`.
Mathematics blob: `831338e7f8977ccbe2fab5d78203e4cd817a2e66`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`.
Pinned Lean: `v4.33.0-rc1`. Pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Mathematical source increment

New `Part5OriginalH430ActualUnpaidOrdinaryEnvelope.lean` (170 lines; four theorem candidates, two definitions).

1. `actual_resolved_Phi_nonneg` proves the genuine `resolve`-generated product-family Phi is nonnegative, using the exact occurrence-preserving pushforward, positive path marks and natural source-sieve cardinalities. Every original Fin list occurrence survives its product-fibre aggregation. No eta, roughness, cutoff or positive-Theta premise.
2. `actual_unpaid_nonneg_le_original_card` proves at each real root (N,p,tag,Q,g) that the ORIGINAL cardinal-minus-5Phi positive-part debt lies in `[0,#originalReceiver(N,p)]`. This does not assume q=d or an owner.
3. `actual_U34_unpaid_nonneg_le_original_count` sums BOTH genuine U3 and U4 root bands with their original quotient q counts, preserving the double U4 tag in the overlap. For every chosen depth, the total debt lies between zero and the original `currentChenUpsilon3+currentChenUpsilon4`.
4. `eventually_actual_U34_unpaid_le_ordinary_upper` combines this with the existing ACTUAL ordinary original U3/U4 asymptotic upper-mean theorem. Its quantifier is uniform in precision n, tau and **all** depth choices after N, with the one threshold determined by epsilon alone. For sufficiently large even N:
   `actualU34Unpaid(N,n,tau,depth) <= (I3_ordinary+I4_ordinary+epsilon)*singularNormalization(N)`.
   This is **not** an H430 bound. The ordinary upper coefficient may be far too large to pay the needed h34 saving. It is a rigorous-looking *candidate source* for a worst-case debt benchmark only, not final formal proof credit.

## Critical non-equivalences and open mathematics

- This bounds the debt only by the whole original q count; it does **not** show `o(Theta)`, a useful smaller constant, or the H430 upper selected-count estimate.
- Actual (tag,p,q) source is **not** identified with a generated product d, rank-two Fin position, or actual full/selected/inherited owner. The original U4 duplicate charges remain present.
- Roughness, cutoff, owner depth/z0, root count weights, cross-q/tag payment, six rejection lanes, signed Euler suffix, native-history quality, all-action CLOSED-CELL, base/switched/seed/floor, manuscript-local PP/same-rho and one common430+11 refinement remain OPEN.
- P1.4, P3.6, original c/K, 7/2 root norm, row norm12, true alpha, same physical Q, and manuscript pin are unchanged.
- No new external analytic theorem is implemented. See EXTERNAL_INPUTS.md.

## Validation and staging

Read back mathematics commits and blob through GitHub, verified only task-owned new directory, and performed static forbidden-token/delimiter checks. The previous h34 automation was recorded in_progress, so this increment went to an isolated branch instead of updating its branch.

The execution container has no Lean/Lake/Elan binary and cannot DNS-resolve github.com for a native Git clone. The new module imports earlier `ImbalancedChen.Part5OriginalH430ActualMarkedRootConsumer` which is currently only present in a `docs/source-only/...` packet, **not** staged at the corresponding `ImbalancedChen/` import path on this branch. Thus no valid elaboration or compile result is possible without staging those pinned dependencies and acquiring the fixed toolchain. Existing CI does not automatically stage this packet. No kernel replay, transitive-axiom audit, independent review, numerical430 finite certificate, or CI run was performed. All inherited finite guards remain **UNEVALUATED**.

All four new theorem declarations are CANDIDATE ONLY, not formally checked. No green status.

## Exact next step

1. Stage the pinned source-only predecessor chain in a *separate isolated compilation workspace* without overwriting production files or changing CI, or obtain a job that explicitly materializes those source-only imports. Run pinned `lake env lean` and repair actual elaboration failures.
2. More importantly, locate the real upper-H430 selected-count owner and prove an **effective** q/tag-to-history payment that shrinks the unpaid debt beneath the H430 available reserve; the ordinary fallback bound alone is insufficient. Preserve the six rejection lanes and signed orientation.
3. Continue CLOSED-CELL, original base/seed/floor, PP/same-rho and joint430+11 only against the unchanged frozen manuscript.

**完整h34稿内证明仍未闭合。**
