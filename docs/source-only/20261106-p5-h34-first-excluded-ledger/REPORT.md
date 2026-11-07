# P5.6 → h34 — occurrence-preserving historical first-excluded ledger

Date: 2026-11-06 (UTC).
Repository: `UyNewNas/goldbach-formalization`; branch `chatgpt/p5-h34-request-admission-20261105`.
Pre-write baseline: `355568ba237ad538c359f2e78f88fd8532d42a63`.
New source commit: `45b8da2fffff27f1efdcc28d72fe96be4e87b5ad`.
Original entry SHA `0a3fa5a` remains initial-only and was NOT reset to.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` (body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.**
The complete manuscript-internal h34 remains OPEN. No Lean elaboration,
kernel replay, transitive axiom audit, finite certificate/numerical430 replay,
CI dispatch, toolchain upgrade, or production module installation.

## Actual source advance

New `Part5OriginalH430HistoricalRejectedExitLedger.lean` (267 nonterminal newline-delimited lines; 2 definitions, 6 theorem proof candidates). The preceding `HistoricalPolicyGates` packet provided candidate-policy equivalences; this packet does not reproduce that gate. It constructs the **actual historical first-excluded event list** using the original `firstExitCorrection` recursion:

- `historicalRejectedEvents` records every rejected selection as an occurrence with the full selected prefix, flipped parity, inherited unsigned mass times the selected prime's original weight, and the exact unprocessed suffix. The skip branch is retained even when another selection is examined.
- `historicalExitValue` assigns that event its **signed** correction term with the genuine residual Euler product over the recorded suffix, not a nonnegative proxy.
- `historical_rejected_events_sum_eq_correction` supplies a structural-induction proof candidate that the sum over **all list occurrences** is exactly the original recursive `firstExitCorrection`. This is a full finite-event ledger, not a statement that its mass has been bounded.
- `rejected_remaining_has_literal_event` preserves the ordered `before ++ r :: after` position. When a real next-prefix test fails, the exact event is present; there is no quotient by `p`, `q`, arithmetic product or label.
- `ordinary_frontier_first_excluded_event` uses the **actually admitted parent** on the original ordinary-Rosser frontier and a failed next-prefix test to construct the first-excluded event. `ordinary_root_correction_eq_rejected_events` specializes the ledger equality to the real capped root carrier and real local reciprocal prime weights.
- `frozen_only_quotient_first_exit` and `rejected_frozen_quotient_first_exit` specialize the event construction to their respective real quotient first-bad factors and distinct physical cutoffs. They preserve the old `jointFirstPrime` identity only under actual quotient-first conditions and require **real remaining-carrier membership and an actual failed Rosser prefix test**. Those conditions are NOT proved universally.

These are six uncompiled candidate proof bodies. No new axiom, sorry/admit, target-equivalent licence or analytic theorem was introduced.

## Critical mathematical boundary

The ledger proves conditional local historical first-exit membership; it does
**not** prove that every `(U3/U4,p,P,q)` corresponds to an ordinary,
full/selected/inherited historical rejection, that a first-bad arithmetic
prime survives the real cap, or that the correction ledger has the original
selected-count multiplicities or signs. In particular, a first-excluded
history event need not be the least factor of `N-P`; the prior selected root
cannot be reselected after it is already in the history.

The same literal `c/K`, root norm `7/2`, row norm `12`, alpha, same-Q,
specified-cell vs scalar read semantics, original occurrences and 430+11
budget were not modified.

## Internal remaining tasks

1. Prove universal physical-cap and Rosser retained-policy decisions for the actual U3/U4 receivers or isolate genuine exceptions; establish full/selected/inherited first-excluded owner and exact (tag,p,P,q) occurrence matching.
2. Bind the actual signed correction event values to the `frozenOnly` and `rejectedFrozen` arithmetic rejection sums; prove correct root weights, owner multiplicities and rejection payment. The present event ledger is only the historical side.
3. Complete request-level Buchstab/retention and the all-action CLOSED-CELL count induction; base, fixed/switched/seed/floor applications, PP/same-rho and literal feedback integral consumption.
4. Close native-history quality and outer integral—Theta—count linkage plus one common nested 430+11 causal refinement.
5. Stage the prerequisites; run Lean elaboration, kernel replay, transitive axiom audit, and all finite guards/certificates. Every such item remains UNEVALUATED until executed.

## Next bounded action

At this exact new ledger, compare the pinned manuscript's actual
full/selected/inherited retained policy with the ordinary-Rosser
`historicalRejectedEvents` recursion. Produce a *source-level* policy
mapping and a true occurrence/weight transport for individual
`(tag,p,P,q)` or record a concrete exclusion/cap obstruction. Do not
continue producing only equivalent Boolean candidate gates.

## Validation performed

GitHub tree/blob and source-commit creation, non-force ref update with
expected prior SHA. Static text check for prohibited placeholders, and
declaration presence. These are not Lean checks, which remain NOT_RUN.
