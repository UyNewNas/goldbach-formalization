# P5.6 → h34: original U3/U4 arithmetic row to frozen-root count dominance

Date: 2026-11-05. Parent: `dc8bda297a0eb87de6f07503a4ec3456e3d22d31`.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT**.
Entire manuscript-internal h34 **OPEN**.

## Why this is the next bridge, not another feedback-list identity

Previous packet `dc8bda2` identifies `generationValue` with a marked old-table
sum over the full selected frontier, but the original U3/U4 arithmetic
source was never proved to equal that feedback list.

In particular the original U3/U4 rowTotalLevel is a VARYING function of
the selected prime p, while rootQ in the generated request history uses
the LOWER frozenLevel n. Setting the two Q values equal is false in
general; using the original Q without paying this change can reverse
the arithmetic comparison.

This packet proves a one-sided **arithmetic-count** comparison across
that genuine root freeze. It keeps the actual original source,
the unchanged p and the strict sifted receiver predicate.

## New file

`Part5OriginalH430RequestedOriginalRowFreeze.lean`: 223 lines,
7 theorem proof bodies (one private finite-sieve monotonicity lemma).

The local theorem chain:

1. `frozen_residual_le_original`: frozen residual ≤ original residual,
   using the actual mesh lower bound and original root total.
2. `frozen_exponent_le_original`: preserves the physical max-two
   clamp: min(a,R_f/2) ≤ min(a,R_o/2).
3. `frozen_cutoff_ratio`: connects the actual physical query to
   R_f/alpha_f = min(a,R_f/2), under the genuine root floor guard.
4. `frozen_root_sameQ_cutoff_power`: reconstructs the SAME frozen Q
   in `(rootQ/p)^(1/alpha_f)`, with no substitution of original Q.
5. `sifted_source_antitone`: source cutoff monotonicity with the
   original finite receiver, congruence and coprimality tests.
6. `original_row_card_le_frozen_row_card`: for the same p and N,
   original physical U3/U4 row count ≤ frozen-root strict sieve count.
7. `original_U34_le_frozen_root_cutoff_counts`: sums the inequality
   over BOTH original prime selectors, preserving their overlap's
   multiplicity and the upper-cost inequality direction.

The resulting source-level mathematical shape is

```
Upsilon3(N) + Upsilon4(N)
  <= sum_{p in original U3 band} |Sifted(N,p,(Qf(U3,p)/p)^(1/alpha_f))|
   + sum_{p in original U4 band} |Sifted(N,p,(Qf(U4,p)/p)^(1/alpha_f))|.
```

Here Qf is precisely the generated frozen rootQ and alpha_f its
physical argument, not a new or independently adjustable level.
U3 tail parameter tau and original U4 mainResidual are unchanged.

## Strict limits

- This is an **upper** count comparison, as required when decreasing the
  cutoff; it is NOT an equality and does not identify the right side
  with `generationValue`, `requestValue`, or the feedback table.
- The original prime-root summations are retained without replacing
  their multiplicities by a single disjoint union or a 7/2 factor.
- The root's positive feedback mark 1 is NOT the complete outer
  root-count weight, nor a proof of native-history mass normalization.
- Source count ownership, full/selected/inherited filters, rejection
  lanes, all-action CLOSED-CELL induction, fixed/switched/seed/floor
  payments, same-rho/PP, and common 430+11 refinement remain OPEN.
- No P1.4/P3.6 changes; no external analytic theorem implemented.
  No new axiom, target-equivalent count hypothesis, sorry/admit, unsafe,
  native proof escape, dependency change, production-module edit,
  numerical430 replay, or CI dispatch.

## Validation and next exact input

Lean/Lake not run. No elaboration, kernel replay, transitive axiom audit,
independent review or numerical verification. All proof bodies and prior
finite guards are **UNEVALUATED**; simple source-only syntax scans and
GitHub object/hash checks are not a proof acceptance receipt.

For staging: place this file under
`ImbalancedChen/Part5OriginalH430RequestedOriginalRowFreeze.lean` after
the prior source-only h34 chain and its frozen U3/U4 source.
This packet does not make the earlier staged modules buildable by itself.

Next: identify the actual frozen-root sifted counts with the correct
full/selected/inherited original arithmetic source occurrences and
their owner/prime multiplicities, then pay real base/seed/floor and
native-history costs. Do not replace that missing identification by
a new field or analytic assumption.
