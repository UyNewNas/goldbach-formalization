# P5.6 → h34 — actual rank-two event occurrence capacity and cross-lane key overlap

Date: 2026-11-07 UTC. Repository: `UyNewNas/goldbach-formalization`.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
**Verified prior HEAD:** `92b29ef0261a52aff8d107edaacb716437564aa1`.
**New Lean source commit:** `938dc74f26533d9c60cadd464d3cdde3327fa139`.
**Source blob:** `e264fee420cb7c0fb8e4bc9c49050e7edf4be745`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`;
`paper/source/manuscript-body.tex` is unchanged.

Status: `PARTIAL_SOURCE_INCREMENT` / `FULL_H34_OPEN` /
`SOURCE_ONLY` / `UNCOMPILED` / `UNEVALUATED`.

## The actual source advance

Added `Part5OriginalH430EventOccurrenceCapacity.lean` (354 source lines,
7 public theorem proof bodies, 3 private theorem proof bodies, 1 definition).
This packet does NOT re-do receipt fibre grouping or merely assert a
count licence. It evaluates the occurrence semantics of the *actual*
recursive list `historicalRejectedEvents`:

1. `rejected_prefix_strict_growth`: every rejection in a recursive
   admitted continuation has an additional selected letter. Therefore
   it CANNOT be mistaken for an immediate rank-two event at the old root.
2. `immediate_rejected_event_occurrence_count`: the number of literal
   events having selected prefix exactly `r :: pre` equals the number
   of actual occurrences of `r` in the remaining carrier for which
   the immediate retention test fails. This holds for arbitrary lists
   and policies, even before distinctness is known.
3. `actual_rank_two_event_capacity_le_one`: specialize to the
   genuine `roughPrimeUniverse N cap 0 p`, using its existing
   `roughPrimeUniverse_nodup` proof. At fixed historical root `p`,
   there is at most ONE list occurrence of an event with exact
   prefix `[ell,p]`. This is NOT one event per arithmetic quotient q.
4. `frozen_fail_key_exactly_one_rank_two_event` and
   `rejected_frozen_fail_key_exactly_one_rank_two_event`: combine
   that capacity bound with the previous *conditional* real-event
   witness. For each distinct key in its original fourth lane and
   `z0 <= cap`, the actual list contains exactly ONE matching
   rank-two event. Different original first-bad cutoff functions
   remain distinct.
5. `fibre_card_one_plus_excess` and
   `signed_source_one_event_plus_excess`: decompose a source fibre
   into its first unit plus the exact `card - 1` surplus, retaining
   every q and U3/U4 tag and arbitrary signed weights.
6. `two_original_fail_lanes_unique_event_key_budget`: charge
   **one distinct (p,ell) key across BOTH original fourth lanes**
   as the *candidate* historical event unit. Any key appearing in
   both lanes contributes another explicit overlap term. Each lane's
   within-key `card-1` excess remains explicit. The exact signed
   equality is:

       receiver mass from F and R
       = sum over (KF union KR) of W(key)
       + sum over (KF intersect KR) of W(key)
       + sum over KF of (|F_key|-1)*W(key)
       + sum over KR of (|R_key|-1)*W(key)

   where W(p,ell)=1/(p-1)/(ell-1). The intersection is a genuine
   *potential double charge*, not a second paid historical event.

## Precise interpretation and open obligations

This establishes source-level occurrence *capacity*, not a complete
historical payment. The noninjectivity bottleneck is now quantified:
for a key with two or more q/tag receipts, the same rank-two event
does not supply a distinct event occurrence to each receipt. Any
future payment must prove a different q-aware weight identity,
obtain another genuinely distinct history/owner supply, or leave
the excess/overlap in the unpaid exception ledger. It cannot use
event existence as an injective matching licence.

The full original U3/U4 selected-count/root count-weight identity,
root-stage presieve compatibility, actual full/selected/inherited
owner and filter, gateBlocked/carrier-outside/policy-pass payments,
CLOSED-CELL arithmetic predecessor and correct base/switched/seed,
feedback integral-Theta-count, manuscript-local PP/same-rho,
native-history mass and ONE common nested 430+11 causal refinement
remain manuscript-INTERNAL and OPEN. P1.4 and P3.6 are untouched.

No c/K, root norm 7/2, row norm 12, real alpha, same-Q condition,
scalar/specified-cell distinction, source quotient multiplicity or
payment count was changed. No external PNT/Mertens/BV proof was
implemented. No new axiom, unproved target-equivalent premise,
proof placeholder, unsafe/native escape, toolchain change, CI dispatch,
merge, or production file change.

## Validation and next exact action

Authenticated GitHub source commit/tree and blob were read back:
one new Lean path, 354 lines, zero deletions. A static forbidden-token
scan passed. Text-only checks do not establish Lean elaboration.
**NOT RUN:** Lean parser, elaboration, compilation, kernel replay,
transitive axiom audit, numerical430 replay and independent review.
Any inherited finite guards remain UNEVALUATED and no new node is green.

**Next action:** bind the unique (p,ell) rank-two event to its genuine
full/selected/inherited owner and the actual signed historical correction
`historicalExitValue` (which includes the remaining Euler product),
rather than confusing the bare event mass W with a fully paid count.
Determine, using literal original q-source arithmetic, how to pay or
explicitly retain each q/tag surplus and each shared-key overlap. Then
continue the native U3/U4 seed/base and CLOSED-CELL bridge.
