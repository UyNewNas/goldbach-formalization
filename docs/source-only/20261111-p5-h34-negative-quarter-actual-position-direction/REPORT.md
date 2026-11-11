# P5.6 / h34 — original negative-quarter actual-position direction

Date: 2026-11-11.
Repository: `UyNewNas/goldbach-formalization`.
Branch: `chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109`.
Verified incoming head: `69abdde6025a2ed118ab4df9b8dcb6ad73dfa48b`.
Candidate Lean source commit: `cf9b34cf3b7c1c9f3eab6184f5c7fe76af7bfc2c`.
Source blob: `dd6744bdf6238358c43f76ff170de659abeb7cb1`.
Source module: `Part5OriginalH430NegativeQuarterActualPositionDirection.lean` (224 lines, one definition, nine theorem candidates).

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Fixed provenance and isolation

Manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, as fixed in earlier proof mapping. Original U3/U4 tagged prime selectors, true q receivers and original Chen negative-quarter coefficient are retained; no manuscript, c/K, root 7/2, row 12, true alpha, same-Q, CI, branch merge or toolchain change. Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. P1.4 and P3.6 are untouched.

## Genuine new internal proof-source work

The earlier unit-weight result established that unit arithmetic-minus-history mass is nonnegative on an actual observed rank-two Fin position, and hence a **lower** bound for unsigned original U3+U4 counts by a piece of rank-two history and six explicit unpaid lanes.

The original Chen U3/U4 term in the same pinned source is **negative**:
`originalU34SignedQuarter N = -(currentChenUpsilon3 N + currentChenUpsilon4 N)/4`.
It is negative on **both** original tags; two tags on the U4 overlap are not merged. The new source does not incorrectly treat the signed coefficient as a positive U3 weight minus one negative U4 tag.

The new source defines `originalNegativeQuarterReceipt` and gives the exact signed tagged-source specialization. At a real fixed-Q observed Fin index, write `R` for original unit representative arithmetic weight and `H` for true observed rank-two historical mass. Then
`G_unit = R - H` while `G_quarter = -R/4 - H`, hence the **exact** relation:

`G_quarter = -G_unit/4 - 5H/4`.

The source proves nonnegative `H` using actual observed (p,ell) primality and the real rank-two mass formula. Therefore the candidate proof entails
`G_quarter <= -5H/4 <= 0` per actual position. This is lifted to every genuine Q-dependent Boolean postfilter, without assuming correspondence with the manuscript's full/selected/inherited predicates.

At the actual ordinary Rosser complete-prefix gate (only), the original tagged negative-quarter source is exactly the kept historical mass plus the genuine signed arithmetic/history gap plus the six **still unpaid** q/tag/rejection lanes. As a consequence the signed subtraction admits an **upper bound** by `-H/4 + six_lanes`. This is the correct inequality orientation. **It is not the lower bound on the negative Chen subtraction needed to finish the main lower sieve count**; no six-lane smallness or sign cancellation is claimed.

## Formal limitations

Every new theorem body is **uncompiled**; the source-only import chain has not been installed and validated with pinned Lean and Mathlib. No Lean parser, elaborator, kernel replay, transitive axiom audit or finite certificate replay ran. A static placeholder scan cannot certify correctness. No `sorry`, `admit`, custom `axiom`, `unsafe` or equivalent target assumption was inserted.

GitHub source was read back from `cf9b34cf3b7c1c9f3eab6184f5c7fe76af7bfc2c` with exact blob `dd6744bdf6238358c43f76ff170de659abeb7cb1`; the comparison against the prior head showed one new source file, +224/-0. This is provenance evidence only, not verification of any proof. Local executable checks: no `lean`, `lake`, or `elan` available, and native Git access to github.com failed DNS resolution.

## Remaining manuscript-internal obligations

1. Prove a usable **lower** payment bound for the actual negative quarter in the correct Chen lower-bound direction, including genuine six rejection/collision lanes and sign-preserving U4 overlap; the upper-bound direction from this packet is not enough.
2. Identify true full/selected/inherited original q/tag owner/filter correspondence, original root 7/2 and the appropriate historical signed Euler suffix. A rank-two observed position is not a full-depth owner.
3. Pay q-fibre physical source and selected-row residuals, stage correct base/switched/seed/floor and preceding real CLOSED-CELL induction.
4. Complete manuscript-local PP/same-rho, native history, outer integral/Theta/count mapping and common 430+11 causal refinement.
5. Stage and genuinely compile the new source plus direct dependencies with exact pinned toolchain; kernel-replay and audit all axioms and finite certificates.

**Next action:** Use the original six unpaid lanes and full-depth owner to establish the missing **lower** inequality for the signed negative quarter; do not recycle the newly proved upper direction as a Chen lower-bound result. Independently, stage and run pinned incremental Lean compilation when a buildable source-only closure becomes available.

**完整h34稿内证明仍未闭合。**
