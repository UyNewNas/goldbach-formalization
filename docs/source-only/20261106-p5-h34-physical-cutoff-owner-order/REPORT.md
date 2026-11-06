# P5.6 → h34 — physical-cutoff order of original p and rejected quotient, with exact signed split

Date: 2026-11-06 UTC. Repository: `UyNewNas/goldbach-formalization`.
Branch: `chatgpt/p5-h34-request-admission-20261105`. **Actual baseline:** `69dd7c5feb21273e8f1b11771a49d06cf09f0700`.
Initial task entry `0a3fa5a` is historical only; no fallback to that baseline.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. No manuscript, parameter, c/K, alpha, root norm 7/2, row norm 12, common-Q or 430+11 change.

## Substantive new manuscript-internal source
`Part5OriginalH430PhysicalCutoffOwnerOrder.lean` contains 231 lines and 11 theorem declarations. It imports the pinned predecessor `Part5OriginalH430JointPrimePrefix` and creates no stand-in version of arithmetic receivers.

1. `root_le_bad_iff_quotient_rough_at_root` connects the original selected p to the quotient's real strict roughness at the **same p**. The strict reverse case is `bad_lt_root_iff_quotient_not_rough_at_root`. The tie belongs to the root-first lane. These statements are attached to a genuine failed-q certificate, not a freely supplied numerical least-factor.
2. `joint_eq_root_of_quotient_rough` / `joint_eq_bad_of_quotient_not_rough` transfer these two cases to the actual arithmetic `jointFirstPrime = min(p,ell)` for the original N-P.
3. `frozen_only_joint_order` and `rejected_frozen_joint_order` instantiate **both actual rejection channels**, preserving the original U3/U4 label, selected p, integer q, additive P, and distinct original/frozen strict cutoffs.
4. `frozen_only_root_first_of_root_le_physical`: if the selected p is at/below that root's frozen physical cutoff, the frozen-admitted q is p-rough and the full N-P begins at p. `rejected_frozen_quotient_first_of_physical_le_root`: if the frozen physical cutoff is at/below p, the still-rejected q has an obstructing ell strictly before p. **These physical comparison hypotheses are explicit conditions, not proved globally.** Neither implies a historical first-excluded owner.
5. `tagged_signed_mass_order_partition` gives an exact signed-weight split by p-roughness for an arbitrary tagged finite receipt family. The two instantiated formulas preserve **all** repeated (U3/U4,p,P,q) receipts in their Finset representation. Neither part is bounded, paid, or identified with full/selected/inherited history.

## Exact internal boundary
The true manuscript first-excluded owner is a causal, ordered, retained-prefix policy event (including cap, rank/parity, sign and selected/inherited gates), **not** necessarily the least divisor of N-P. The above source only gives the arithmetic order test and exact signed split needed for a subsequent comparison to the real tree. In particular, selected p versus frozen physical cutoff has not been shown to obey either one-sided comparison at every original root; those cases remain distinct. No equivalence between arithmetic receipts and generated feedback occurrences is claimed.

Still open: actual historical first-excluded candidate matching (p versus ell and earlier retained primes), root count weights and per-q multiplicities, two signed rejection masses and owner disjointness, all-action Buchstab/retention CLOSED-CELL counting, seed/base/floor, manuscript-local PP/same-rho, outer integral—Theta—counts, native-history quality and one causal 430+11 refinement.

## Verification, ownership, and next concrete action
SOURCE_ONLY / UNCOMPILED / UNEVALUATED. No Lean parsing, elaboration, kernel replay, transitive axiom audit, finite430/numerical replay or heavy CI was run. Text-only forbidden-proof-escape and delimiter screening cannot certify proof correctness. No green status or formal credit. No production source, existing source-only directory, P1.4/P3.6, dependency, workflow or manuscript is changed.

Next: instantiate the actual `firstExitNextSelectionCandidates` / `firstExitDepthFrontier` order and the fixed historical policy on each tagged (U3/U4,p,P,q). Prove (or reject) correspondence between arithmetic p/ell case and the policy's **first excluded** prefix with its cap, sign, parity, and every original occurrence. Only then pay the signed lanes. Avoid another generic receipt reindexing.
