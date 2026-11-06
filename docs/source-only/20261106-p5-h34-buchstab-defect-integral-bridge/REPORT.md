# P5.6 / h34 — actual Buchstab read-to-integral defect bridge

Date: 2026-11-06. Repository: `UyNewNas/goldbach-formalization`.
Work branch: `chatgpt/p5-h34-request-admission-20261105`.
Verified baseline: `f8c3a3babd6810fdfbf73c30aedae91108a5abf4`; the initial `0a3fa5a` is not the current head.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes` at `ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).

## Actual new source

New source-only module `Part5OriginalH430BuchstabDefectIntegralBridge.lean`, 196 lines, 5 theorem bodies, one definition. Source Git blob `e4d9e632a4493a981131d67bc942ead969565ffe`.

This packet continues from the earlier `Part5OriginalH430ActualReadEdgeDefect` (source commit `15752ca83b6f700835536dcfa322cf12cf57b4ab`, documentation head `f8c3a3babd6810fdfbf73c30aedae91108a5abf4`) and **reuses** the previously existing `Part5OriginalH430RequestedSignedStep` and `Part5OriginalH430RequestedNonbankLevel`. No repeated retention/Buchstab supplier or assumption that a literal suffix equals an arithmetic prime sum.

* `buchstabReadIntegralResidual` is the original **signed** selected-request read minus the same parent's original Buchstab integral profile. The actual `Index` preserves repeated path positions and `levelMark`, the actual resolver determines the selected cell, and the unchanged `rootQ`, ceiling and upper/lower polarity are used.
* `buchstab_actual_suffix_residual` reconstructs the original chosen integer `buchstabValue(iterate g)` divided by `2^80` at each actual Buchstab winner, without replacing the winner with a synthetic scalar owner.
* `buchstab_defect_ideal_split` is the exact finite identity
  `sum_B defect = signed_suffix_to_integral_residual + (strict_prime_integral - strict_prime_actual)`.
  The latter two terms have the same previous-generation ideal profile, so no duplicate correction is introduced.
* `buchstab_defect_le_integral_residual` pays only the strict-prime-to-integral term using the **existing** coefficientwise absolute row error (via `buchstab_abs_le_applied` and `buchstab_applied_le_rowError`). It does **not** pay or sign-bound the original suffix-to-integral residual.
* `actual_one_generation_integral_residual_upper` joins that payment to the real all-action read-minus-child difference: retention cancels, bank winners retain their original candidate gap. `uniform_actual_one_generation_integral_residual_upper` uses one **pre-N** threshold from `uniform_level_buchstab_supply`, leaving `epsilon * buchstabLevelTheta` plus the **unpaid signed residual** and bank candidate terms.

The mathematical advance is a precise separation of the formerly unpaid Buchstab suffix-to-prime discrepancy into a quantitatively controlled strict-prime-to-integral component and an explicitly unpaid integer-suffix-to-integral component. It is not a complete arithmetic source estimate; obtaining the required directional upper/lower control for the remaining integer suffix is the next required manuscript-local action. No new analytic theorem is proved.

## Scope and validation

PARTIAL_SOURCE_INCREMENT / **FULL H34 OPEN**.
SOURCE ONLY / UNCOMPILED / UNEVALUATED. No Lean elaboration, kernel replay, transitive axiom audit, numerical430 or other finite certificate replay. No formal verification credit. Source-token static scan excludes disabled proof escape markers; this is not typechecking. No CI was dispatched, no toolchain or dependencies changed, no production modules edited, no master merge, and P1.4/P3.6 remain untouched.

The source-only packet may require staging and correction before Lean accepts it. Its claims above are exact descriptions of **intended candidate statements**, not an assertion of kernel-proved theorems.

## Still open (manuscript-local)

1. Prove the **directional** estimate for the genuine integer suffix-to-integral residual, with correct upper/lower polarity, physical ceilings, actual finite precision and base/floor/seed terms. The existing strict-prime row bound does not imply this remaining estimate.
2. Bind bank base/fixed/switched/feedback terms and the actual one-generation read/child comparison to the original CLOSED-CELL arithmetic predecessor induction; do not identify the request-list values with U3/U4 selected counts without proving the source correspondence.
3. Complete actual original U3/U4 full/selected/inherited count source, root weights, history owner, exception classes and repeated-event fibre payment. Resolve prior pre-sieve/root-stage mismatch against the actual history stage, not by assuming an impossible rank-one owner.
4. Complete manuscript-local PP/same-rho, native-history mass, outer integral–Theta–count mapping, and the **same** 430+11 nested causal refinement.
5. P0-controlled staging and full Lean compile / kernel replay / transitive axioms and finite certification. These have NOT been run.

## Next exact action

Inspect fixed-version `buchstabValue` and original Buchstab table's integer suffix rule. Prove its **one-sided** selected-cell comparison with the ideal integral (including rounding and correct polarity), then specialize `buchstabReadIntegralResidual` without changing the actual source. Keep the remaining bank candidate/base/seed terms explicit until their separate payments are proved.

The GitHub commit SHA is the commit that adds this report and the source; the final branch-head/readback is determined after the ref update, not asserted in advance.
