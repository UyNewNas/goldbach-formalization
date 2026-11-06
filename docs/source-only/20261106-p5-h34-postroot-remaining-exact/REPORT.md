# P5.6 → h34 — exact genuine post-root remaining carrier

Date: 2026-11-06 UTC. Scope: manuscript-internal source-only increment.

- Dedicated branch: `chatgpt/p5-h34-request-admission-20261105`.
- **Verified pre-write baseline:** `214442a7f801ba357ac2421fe836d5ebd3ca9fbd`.
- Original initial entry `0a3fa5aa639e74122fbef18be02f0ad6fa8a77a0` was NOT used as a new baseline.
- Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` — `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` (unchanged).
- File: `Part5OriginalH430PostRootRemainingExact.lean`: **283 lines**, **8 candidate theorem bodies**.

## Real mathematical increment

At a genuine positive-rank frontier of the *original* `firstExitDepthFrontier` recursion, the retained selected prefix is nonempty. The already-existing `mem_firstExitDepthFrontier_roughPrime_remaining` gives an actual last selected prime `p` and *literal* remaining carrier `roughPrimeUniverse N cap 0 (p:ℝ)`. This `p` itself belongs to the capped original universe, so `p < cap` follows without asserting any universal `N < cap`.

For a prime factor `ell` of a genuine original `rawTagged N` quotient `q`, previous source `raw_quotient_factor_not_target` derives `ell ∤ N` from the original `Nat.Coprime q N`. The new theorem `raw_factor_post_root_remaining_iff` therefore derives the sharp **if and only if**:

```
ell ∈ frontier.remaining  ↔  (ell : ℝ) < (frontier.selectedPrefix.headD 0 : ℝ)
```

No additional post-root premises `N < cap` or `cut ≤ z0` occur. They remain potentially necessary for the *empty-root* enumeration, and no claim discharges those root-stage gates. The new `raw_factor_post_root_candidate_iff` turns this into literal original next-candidate enumeration, while `raw_factor_not_post_root_of_order` excludes the non-strict case rather than guessing an owner.

The two original arithmetic lanes are instantiated **separately** in `frozen_only_bad_post_root_remaining_iff` (original `N^a` cutoff) and `rejected_frozen_bad_post_root_remaining_iff` (actual root-dependent frozen cutoff). The generic `raw_factor_post_root_rejected_event` and two lane consumers pass strict order and a **genuine failing ordinary Rosser prefix** into the existing historical rejected-event ledger. They preserve actual sign `!frontier.positive`, mass `frontier.mass * 1/(ell-1)`, and the ledger's original list suffix. These are CONDITIONAL event certificates, not assertions that every original arithmetic receiver belongs to such a frontier.

## Still open — genuine manuscript obligations

1. Relate every original tagged `(U3/U4,p,P,q)` receiver to the **actual** root-stage and post-root history, including whether the strict order and ordinary Rosser rejection hypotheses really hold. The sharp carrier criterion does not supply those premises.
2. Identify **full / selected / inherited** filtering and owner; prove a sign- and multiplicity-correct map between arithmetic receivers and literal historical event **occurrences**. Multiple q labels may produce the same ell/event; no injection or payment is inferred.
3. Prove or classify root-stage `cap/z0` inequalities, especially where an empty-root candidate is actually needed; do not promote the new positive-rank result to rank zero.
4. Bound and pay both `frozenOnly` and `rejectedFrozen` signed mass; connect original U3/U4 selected-count and root weights to generated history.
5. Request Buchstab/retention and **all-action CLOSED-CELL** count induction; base/fixed/switched/seed/floor, literal feedback-to-integral and manuscript-local PP/same-rho consumers.
6. Native-history quality, outer integral–Theta–count, and a single common nested 430+11 causal refinement.

## Source and engineering boundary

Imports only previously recorded original first-exit geometry, genuine quotient source and source-only candidate ledgers, plus Mathlib arithmetic. No external analytic theorem was reimplemented or newly postulated. c/K, root norm 7/2, row norm 12, actual alpha, same-Q, distinct scalar/specified-cell reads, original occurrence/payment counts and all finite certificate targets remain fixed.

**SOURCE_ONLY / UNCOMPILED / UNEVALUATED.** Static placeholder and delimiter scans are not Lean elaboration. No Lean compiler, kernel replay, transitive-axiom audit, finite certification or CI run was performed. No production module, P1.4 or P3.6 was changed. No new green node. The eight declarations are blue **only** in the narrowly described source-coverage sense.

**Next exact action:** compare the obtained strict post-root order criterion against the fixed manuscript's *actual selected-history root/owner mapping*, and seek an occurrence-preserving relation to `historicalRejectedEvents`. Treat failed strict order and failed Rosser rejection as explicit exception lanes, not absent mass. Continue request-level Buchstab/retention if it becomes the nearer non-duplicated dependency; no new same-scope interface shell.

**Full manuscript-internal h34 proof remains OPEN.**
