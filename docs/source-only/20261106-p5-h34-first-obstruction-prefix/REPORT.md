# P5.6 → h34 — exact least-prime prefix of the original arithmetic receiver

Date: 2026-11-06 UTC. Repository: `UyNewNas/goldbach-formalization`.
Branch: `chatgpt/p5-h34-request-admission-20261105`. Predecessor: `a4f0a2f9094e4c3685c60adda11945875a0eac51`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.**

## New manuscript-internal work

`Part5OriginalH430FirstObstructionPrefix.lean` imports the last verified-by-readback *source-only* h34 first-bad-prime-owner module and strengthens the arithmetic owner to the actual least prime divisor of each rejected quotient `q`, rather than merely a chosen divisor below a cutoff.

- `first_bad_le_every_prime_divisor`, `no_earlier_prime_divides`: the prior `Nat.find` witness is least among *all* prime divisors of q; no earlier factor occurs in the ordered quotient prime-factor prefix.
- `rough_iff_below_first_bad`, `rough_at_first_bad`: exact real cutoff threshold `ChenPrimeRough x q ↔ x ≤ ell` (given actual failure at the source cutoff), including equality at the threshold.
- `first_bad_cutoff_invariant`, `first_bad_ordered_cutoffs`: owner stability across genuine rejecting cutoffs. The latter requires an actual proved cutoff inequality, not a new count license.
- `frozen_only_additive_prefix`, `rejected_frozen_additive_prefix`: specialize the threshold to the distinct frozen-only and still-rejected arithmetic channels, preserving the original U3/U4 tags, p, integer quotient q and additive prime P=N-pq.
- `first_bad_divides_difference`, `raw_label_divides`, the two tagged `..._divides_N_sub_P` declarations: show the genuine first obstructing prime divides N-P through the **actual** integer-quotient source. The quotient q is not assumed prime.

**Important distinction:** the least prime factor of q need not be the first factor of N-P, because the original selected root p can occur earlier. Hence none of these statements identifies the least-quotient-factor owner with the manuscript's historical full/selected/inherited first-excluded-prefix owner. Signed multiplicity, the true causal p-prefix order, and both rejection payments remain unproved.

The pinned manuscript's ordered first-exit principle is `paper/source/manuscript-body.tex` lines 377–391 (upper parity) and 694–716 (lower parity); positive-feedback count and common refinement appear at lines 790–877. This packet establishes only the arithmetic precondition for matching to that historical prefix.

## Exact open obligations

1. Identify the original full/selected/inherited history owner for each tagged (U3/U4,p,P,q), explicitly including any p which precedes ell. Show the correct first-excluded prefix, parity, signs and **list occurrence** multiplicities; do not equate a q-fibre cardinality with a generated root mark.
2. Pay both `frozenOnly` and `rejectedFrozen` signed rejection masses and match the actual original U3/U4 selected count and root weights.
3. Complete the all-action CLOSED-CELL arithmetic induction and true ordinary/fixed/switched/seed/floor payments.
4. Complete manuscript-local PP/same-rho, feedback-integral/Theta/count, native-history and a single nested causal 430+11 refinement.
5. Install under the pinned Lean toolchain and execute elaboration, kernel replay, transitive axiom audit and finite numerical replay.

## Validation

Static source-only declaration/forbidden-token/delimiter checks may be recorded. This is not a Lean parse or proof check. No toolchain upgrade, CI dispatch, heavy compilation, production edits, or change to c/K, root norm 7/2, row norm 12, true alpha, same-Q, fixed/scalar read semantics, 430+11 or the manuscript pin. All finite guards remain UNEVALUATED.

**Next action:** read the literal original first-excluded-prefix filter and root-prime ordering; map the new exact quotient prime prefix into it (or exhibit the precise mismatch), retaining tag/p/P/q and count multiplicity. Complete h34 remains OPEN.
