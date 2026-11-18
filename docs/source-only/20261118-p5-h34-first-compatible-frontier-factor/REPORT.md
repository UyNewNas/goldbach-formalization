# P5.6 → h34 — canonical original q factor vs actual rank-two frontier

Date: 2026-11-18.
Repository: UyNewNas/goldbach-formalization.
Continuation branch: chatgpt/p5-h34-full-tagged-actual-fin-20261112.
Last confirmed pre-write remote HEAD: 92f4c5ef575a7a822079b83571f97f6390ce48fa.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Pinned Lean: v4.33.0-rc1. Pinned Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

STATUS: SOURCE_ONLY / CANDIDATE / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.

## Exact manuscript-internal source increment

New module: Part5OriginalH430FirstCompatibleFrontierFactor.lean.

The previous packet proved that a tagged original (U3/U4,p,q) receipt chooses the least Rosser-retained prime divisor ell of the actual q. A separate older manuscript-local packet proved BOTH directions between retainedOriginalSecond and a real length-two firstExitDepthFrontier state at the receipt's physical Q.

The new module joins these two actual (non-assumed) result chains:
- frontierEligibleSecond requires BOTH a genuine prime divisor of original q and an actual rank-two historical state with ordered prefix [ell,p], retaining tag/p-specific physical Q.
- frontier_eligible_iff_actual_second identifies that real frontier condition with the original ordinary Rosser retention test (not with a fabricated historical owner).
- canonical_key_iff_first_compatible_frontier characterizes the literal canonical (tag,p,ell) key as the LEAST q-dividing rank-two frontier-compatible prime.
- smallerOriginalPrimeFactors lists genuine earlier prime factors of q without asserting they are absent.
- smaller_q_factor_not_retained and smaller_q_factor_not_in_actual_frontier show those earlier factors are excluded by the actual second Rosser policy and the real rank-two frontier, respectively.
- canonical_key_actual_frontier_and_earlier_blockers retains the genuine second-rank frontier witness, its positive alternating sign and exact product mass, with no earlier q-dividing frontier factor.
- canonical_key_unique_actual_frontier_state reuses the genuine fixed-Q/prefix state uniqueness result. It says NOTHING about list-position multiplicity or the many-q-to-one-frontier capacity gap.

This is a precise first-eligible FRONTIER compatibility statement. Historical FIRST-EXIT/first-forbidden ownership is a different notion and remains unproved; a smaller non-retained q factor can exist, and a frontier state may be compatible with many distinct original q receipts. No count or signed Euler mass has been paid. The prior finite tag/p/ell receipt capacity ledger is unchanged.

## Scope and validation

Only new source-only files in the independent h34 directory. Neither P1.4/P3.6 nor production/CI, external analytic proofs, dependency versions, frozen manuscript, c/K, root norm7/2, row norm12, alpha, same-Q or 430+11 are modified.

GitHub app push permission was checked. The exact prior dedicated h34 branch HEAD was read; no in-progress or queued GitHub Actions run was found for that branch. The 20261105 REPORT, REGISTRY, EXTERNAL_INPUTS and related source, most recent source/REPORT/REGISTRY and actual rank-two forward/converse implementations were inspected.

Local environment has git, but not lean/lake/elan or the staged pinned import closure. No Lean parsing/elaboration, actual compilation, kernel replay, transitive axiom audit or finite certification was performed. Static placeholder checks are NOT compilation. Status must remain SOURCE_ONLY / UNCOMPILED / UNEVALUATED; no green node.

## Remaining manuscript-internal work

1. Prove the relationship (or a precise unmatched/rejection lane) between first q-compatible retained rank-two frontier and the manuscript's real first-excluded/first-forbidden history owner. Neither can be substituted for the other.
2. Prove original U3/U4 full/selected/inherited correspondence to actual historical list positions, multiplicity/capacity and root norm7/2. Keep actual q/tag counts and signed Euler remainder terms.
3. Close strict-prime Buchstab/retention physical sources, all-action CLOSED-CELL induction, genuine seed/base/fixed/switched/floor payments and dynamic ideal gap.
4. Finish manuscript-local PP/same-rho, native-history, integral–Theta–count and one common 430+11 nested causal realization.
5. Stage fixed imports, run actual incremental Lean/Lake compilation, kernel replay, transitive axiom audit and finite certificate checks.

FULL h34 manuscript-internal proof remains OPEN.
