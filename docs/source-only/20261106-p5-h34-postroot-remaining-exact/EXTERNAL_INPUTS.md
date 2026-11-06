# External inputs — P5.6 h34 post-root exact carrier

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.

**New external analytic inputs: NONE.** No PNT/Mertens/BV theorem is introduced, proved anew, strengthened or weakened. Existing exact interfaces and the original library/Mathlib base are left unchanged.

The new theorem `raw_factor_post_root_remaining_iff` uses old **manuscript-local** `mem_firstExitDepthFrontier_roughPrime_remaining`, `mem_roughPrimeUniverse`, `raw_quotient_factor_not_target`; the candidate theorem uses `actual_next_candidate_iff`; the event theorem uses old `ordinary_frontier_first_excluded_event`. These are not outsourced as external mathematical hypotheses; they must themselves compile when the staged source-only chain is installed.

Standard Lean/Mathlib: natural-to-real casts, strict inequalities, list membership, primes and finite list/frontier reasoning; no new nonstandard axiom. Exact Mathlib revision is the unchanged repository `lake-manifest.json` at baseline `214442a7f801ba357ac2421fe836d5ebd3ca9fbd`; the toolchain is unchanged and not independently kernel-audited in this packet.

**Still manuscript-internal:** true original receiver-to-history stage/owner and multiplicity map, failing Rosser gate for all relevant receipts or explicit exception accounting, signed rejection mass, original selected-count, request Buchstab/retention and closed-cell induction, PP/same-rho matching, feedback base/seed and integrals, native-history and one common 430+11 refinement. None has been reclassified as an external input or assumed by an axiom.

All new and inherited finite guards: **UNEVALUATED**. Lean elaboration, kernel replay and transitive axiom audit: **NOT_RUN**.
