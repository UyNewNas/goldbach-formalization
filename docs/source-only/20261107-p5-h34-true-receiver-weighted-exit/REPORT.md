# P5.6 → h34 — true tagged q-dependent arithmetic receipt weight to signed historical exit

Date: 2026-11-07 UTC.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Verified prior remote HEAD: `2763aff366e832b2176c86b5442ed11150321c9b`.
Lean source commit: `147a6600cfb0f9a90bae98dc42021bebb9b98a17`.
Source git blob: `57839326a52ac6fe2c50bab751c7a3eca01d1bbb`.
Source: `Part5OriginalH430TrueReceiverWeightedExit.lean` (202 nonempty-line-file trailing-newline convention; 203 lines split).
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`.

**PARTIAL_SOURCE_INCREMENT / H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.**

## What was actually added

The previous signed-exit ledger `Part5OriginalH430RealSignedExitPayment` only decomposed the positive bare key mass `originalEventMass (p,ell)`, multiplied by q/tag fibre cardinalities. This was not the genuine U3/U4 arithmetic receiver contribution when q-dependent signed source weights or literal integer receipts are needed.

The new candidate module has 203 source lines (202 inserted lines according to GitHub diff), 4 public definitions (`fourthFrozenFail`, `fourthRejectedFail`, `fourthDistinctKeys`, `fourthKeyReceipt`), one further definition (`fourthNonEventWeight`), 3 public theorem proof bodies and one private helper theorem.

1. `two_source_true_weight_sum_by_keys` exactly reindexes TWO distinct original `Finset TaggedReceiver` sources for arbitrary `wF wR : TaggedReceiver → ℝ`. It retains every U3/U4 tag and quotient q; no injectivity, cardinality bound, mass positivity, or event equality is assumed. A missing source key has an empty event fibre, proved in `fibre_empty_of_key_outside`.
2. `two_source_true_weight_signed_exit_gap` replaces exactly ONE contribution per distinct key with the genuine `actualRankTwoSignedExit`, and keeps the entire difference `sum of original q/tag weights in that key - signed exit` as a separate **UNPAID** residual. Unlike the previous bare mass ledger, it works for w=1 (literal integer receiver occurrences), general q-dependent weights and signed weights. The result is an exact algebraic identity, **not** a payment inequality.
3. `original_U34_rejected_weighted_signed_exit_gap` composes the existing `original_rejected_eight_lane_signed` for the full actual `rejectedOriginal N` tagged source with that exact key ledger. This covers the two true event-bearing `ownPolicyFail` lanes and retains the other SIX genuine lanes in `fourthNonEventWeight`: gateBlocked, ownCarrierOutside and ownPolicyPass in both frozenOnly and rejectedFrozen. It keeps source parameters `hN, htau, htauhi, hn` unchanged.

For any original tagged receiver weight w, abbreviate `F/R` for the two true fourth lanes, `K` for the union of their event keys, `E(k)` for the *signed real historical exit* and `B` for the six non-event lane weighted sum. The final candidate identity is:

    sum_{z in rejectedOriginal} w(z)
      = B + sum_{k in K} E(k)
          + sum_{k in K} [sum_{z in F_k} w(z) + sum_{z in R_k} w(z) - E(k)].

The bracket is NOT zero. E(k) retains the actual negative sign and remaining Euler product, and a shared event key is charged once, not once per q or tag. w is not silently identified with an historical mass, and no extra historical event has been invented.

## Exact remaining manuscript-internal mathematical obligations

- Establish original count-specific/analytic q-weight correspondence, real root weights, full/selected/inherited owner and filtered historical correction. This source covers the actual rejected arithmetic tagged set only, not complete selected-count U3/U4 ownership.
- Prove the *direction and magnitude* of the per-key residual against the original source and actual signed Euler correction; bound multiple q/tag receipts, cross-lane overlap, and all six genuinely unpaid non-event lanes.
- Complete true CLOSED-CELL predecessor induction; original base/switched/seed/floor and q80 integrals/Theta/count; manuscript-local PP/same-rho; native-history proper/equality/inherited mass; one common 430+11 nested causal refinement.
- Complete Lean elaboration, kernel replay, transitive axiom audit and held numerical430 finite certificates.

## Verification boundary

- Authenticated GitHub file readback: source blob `57839326a52ac6fe2c50bab751c7a3eca01d1bbb`.
- Actual GitHub compare at source commit: one added Lean source file, 202 insertions and zero deletions.
- Local in-tool static forbidden-token check, nested-comment and balanced-bracket check only.
- NOT RUN: Lean parser/elaborator/build, kernel replay, transitive axiom audit, independent checking, CI, numerical430 or inherited finite guards. Nothing is green.
- No new sorry, admit, custom axiom, unsafe/native proof escape, CI dispatch, toolchain upgrade, modified production module or outside-task file.

**Next precise action:** bind the actual selected U3/U4 count unit/q-weight source and historical root selection to `fourthKeyReceipt`, prove a directional payment budget for signed Euler exit versus true arithmetic counts, then resolve six non-event receiver lanes. Do not replace q-receipts with bare key mass, claim multiple payments per key, or relabel manuscript-local ownership as an external input.
