# P5.6 → h34 — genuine quotient-factor exclusion and initial historical carrier

2026-11-06 UTC. Source-only, manuscript-internal, partial increment.

- Repository: `UyNewNas/goldbach-formalization`.
- Existing dedicated branch: `chatgpt/p5-h34-request-admission-20261105`.
- **Actual pre-write HEAD:** `18eb768aa82e34dc4be578d85eec7552fe140076`.
- **New Lean source commit:** `0de3aeee71ff5a05baad97765106102eb423c9ab`.
- Original entry `0a3fa5aa639e74122fbef18be02f0ad6fa8a77a0` is only the initial reference, not the last baseline.
- Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`; `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` (not switched).

## Actual mathematical advance

New file: `Part5OriginalH430QuotientBadPhysicalCarrier.lean` (193 lines, **9 candidate theorem bodies**).

The previous first-excluded ledger established a *conditional* historical event for an arithmetic rejected quotient, but did not establish that the quotient's prime factor can even enter the original historical prime alphabet. The genuine `chenQuotientPrimeSource` has stronger data than arbitrary factorization of `N-P`:

```
0 < q,  q ≤ N,  Nat.Coprime q N
```

This is the existing, literal `raw_quotient_data` assertion; it is not assumed for all numbers `N-P` and not a new sieve input. A prime `ell` dividing this **q** must satisfy `ell ≤ N` and `¬ ell ∣ N`. The new file provides proof candidates `raw_quotient_factor_not_target` and `raw_quotient_factor_le_target` using the actual source, gcd and prime > 1. In particular, the old suspected target-divisor obstruction is **absent for actual raw quotient receptions**, subject to successful Lean verification.

`raw_bad_in_initial_historical_universe` uses those facts to establish
`ell ∈ roughPrimeUniverse N cap 0 z0` from the two remaining explicit physical comparisons:

```
N < cap
cut ≤ z0
```

The first-bad factor is genuinely prime and lies below `cut`. This does not assert those comparisons for every actual historical stage.

The above is specialized separately to the actual `frozenOnly` original strict cutoff `(N:ℝ)^a` and `rejectedFrozen`'s original root-dependent `frozenPrimeCutoff`, with `frozen_only_bad_not_target`, `rejected_frozen_bad_not_target`, `frozen_only_bad_in_initial_historical_universe`, `rejected_frozen_bad_in_initial_historical_universe`. Their U3/U4 and (p,P,q) provenance, including overlapping root bands, is not identified away.

Finally `frozen_only_bad_root_enumerated` and `rejected_frozen_bad_root_enumerated` construct an actual original `firstExitNextSelectionCandidates` occurrence **at the empty root stage**, with the original `1/(r-1)` weight, whenever these physical comparisons hold. No Boolean Rosser admission, selected-history frontier, or rejection-event identity is imposed.

## What is **not** proved

1. The actual cap and root z0 comparisons for *each* frozen historical root; the current lemma uses `N < cap` and `cut ≤ z0` as openly stated physical premises.
2. Moving from the initial root alphabet to an **arbitrary post-root** `frontier.remaining`: skipped primes, already-selected p and strict descending ordering all matter. An initial candidate is not a first-excluded historical owner.
3. Original full/selected/inherited filtering and the multiplicity- and sign-correct map from tagged (U3/U4,p,P,q) to actual history events. Two rejection lanes have not been paid.
4. Request-layer Buchstab/retention and all-action closed-cell count induction; original root weights, base/fixed/switched/seed/floor, literal feedback-to-integral, PP/same-rho.
5. Native-history quality, outer integral–Theta–count and the common 430+11 nested causal refinement.

## Reused inputs and exact boundary

Only original project Lean results, pinned local source-only candidates, and standard Lean/Mathlib finite arithmetic are used. No new PNT/Mertens/BV theorem, custom axiom, `sorry`, `admit`, `unsafe`, or native proof shortcut. The fixed c/K, root norm 7/2, row norm 12, alpha, same-Q, scalar-vs-specified-cell distinction, occurrence counts, payment counts, and finite certificate targets are unchanged.

## Validation and handoff

**SOURCE_ONLY / UNCOMPILED / UNEVALUATED.** GitHub source commit and its one-file diff were read back. Static text inspection is not Lean parsing, elaboration, kernel replay, or transitive axiom audit. No CI job, heavy build, numerical430 replay, dependency change, production-module install, force push, or default-branch merge. Inherited finite guards remain UNEVALUATED. No green nodes.

**Next independent action:** use the *literal frozen-history cap and z0 definitions* to discharge `N < cap` and `cut ≤ z0` where genuinely possible. Then follow actual one-step root selection to the post-root remaining carrier, identifying precisely the selected/omitted cases; compare against `historicalRejectedEvents` and full/selected/inherited filtering with per-receiver sign, root weight and occurrence multiplicity. Do not assert general owner identity where the policy/cap comparison fails.

**Full manuscript-internal h34 proof still OPEN.**
