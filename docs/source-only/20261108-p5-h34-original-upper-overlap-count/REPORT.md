# P5.6 → h34 — original U3/U4 selected-q overlap and Chen-quarter source

Date: 2026-11-08 UTC.
Status: **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

- Branch: `chatgpt/p5-h34-request-admission-20261105`.
- Previous verified remote HEAD: `fbb80889efe5bfd1d26e31737f1f14b002ab91bb`.
- New mathematics commit: `9c4b168d3cb3ca2138b5176aa4ed006037eb886f`.
- New mathematics file: `Part5OriginalH430OriginalUpperOverlapCount.lean` (155 lines, 10 candidate theorem declarations, 3 definitions); Git blob `a2ac7b1726a4ee2133f49fa6b0e6c9dbec468983`.
- Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, unchanged.

## Why this is a new manuscript-internal source step

The frozen manuscript §5 (Y3, Y4, W) has the literal full sifted quotient Q_p(N^a) twice on the overlapping prime band `N^a <= p < N^(59/250)`: once inside U3 (upper endpoint 1/3) and once inside U4 (upper endpoint 59/250). The two labelled negative terms in Chen's 1/4 root functional must therefore preserve two ORIGINAL q/tag occurrences, regardless of whether a historical first-exit event could cover either of them.

The existing `Part5OriginalH430TaggedArithmeticReceivers` already identifies the original U3+U4 count as the cardinality of two tagged sigma families. The new packet refines that identity to a **disjoint prime/q-fibre split** using the already-proved concrete selector subset from `CurrentChenSinglePrimeUpperFiniteMean`. Define E as the genuine U3-only (p,q) sigma family and F as the complete genuine U4 (p,q) sigma family, with exactly the source's original sifted q for both.

The candidate Lean statements establish:

    originalPairs U3 = E ∪ F,   E ∩ F = ∅
    count(U3) + count(U4) = card(E) + 2*card(F)
    -(U3+U4)/4 = -card(E)/4 - card(F)/2

The signed sum identity works for any **common signed arithmetic weight** w(p,q): the originally tagged total is sum_E w + 2*sum_F w. It does not identify arbitrary tag-dependent w3,w4, and crucially does not claim the SAME historical event is allowed to pay both labels. The negative quarter is the literal Chen root occurrence coefficient, not a historical Euler mass.

The new `original_exclusive_pairs_card_fibres` keeps every complete q receiver under the original p. No diagonal cancellation, artificial quotient by products, fake shared Q, or artificial U3/U4 disjointification appears.

## What remains genuinely open (manuscript-INTERNAL)

1. Identify U3/U4 upper H430 selected-count **historical owner**, actual z0, root count weights, full/selected/inherited stage and each q/tag occurrence. The exact arithmetic double-count now needs *two actual payment licences* or an explicit unpaid overlap.
2. Resolve collisions between distinct q, across U3/U4 tags, and within historical (Q,p,ell) keys. Retain erased-position weight, signed arithmetic/history gap and cutoff, rough, Rosser and policy rejection lanes.
3. Prove the signed Euler complete suffix and first-excluded payment direction at the correct upper-stage owner. The ordinary LOWER h-start is not such an owner.
4. Complete request-level Buchstab/retention and full all-action CLOSED-CELL induction, real base/switched/seed/floor, feedback integral–Theta–count link and manuscript-local PP/same-rho.
5. Close native-history proper/equality/inherited mass and **one common nested 430+11 causal refinement**, preserving true alpha, same Q, c/K, root norm 7/2 and row norm 12.
6. Install, elaborate, Lean compile, kernel replay, transitive-axiom audit and evaluate inherited finite numerical430 guards.

This packet does not infer pointwise sieve bounds from exact cardinal arithmetic. Original U3/U4 upper integral phases from `ee2072a` and `51a1e0f` are unchanged; identifying them with integer counts remains open.

## Engineering and independent validation limits

Only the new source-only file is in the mathematics commit. No production/P1.4/P3.6 file, pinned manuscript, old packet, CI workflow or dependency was edited; no CI or heavy build was dispatched. The remote blob was read back and a static nested-comment/delimiter/forbidden-token check passed. **These checks do not imply parsing, Lean elaboration, a compiled theorem, kernel replay or an axiom audit.** All candidate proofs and all finite numerical430 tables remain **UNEVALUATED**; green credit remains zero.

**NEXT:** locate the genuine upper H430 owner at the ORIGINAL `Y3/Y4` selected-count consumer and show how both labels in F are handled; do not use the lower h-start or implicitly charge one historical exit twice. If that successor is already implemented, instead advance the next still-open full/selected/inherited source bridge.

**完整 h34 稿内证明仍未闭合。**
