# P0 Round 16 — signed zero-extension accepted as a source candidate

Frozen manuscript: `ba6ec11d800eccc54406490631895e174de85766`. Shared proof baseline remains `1a80c1bcce67886f699d097fc37fd245cd3620bf`. No change to manuscript, mathematical constants, toolchain, mathlib or goldbach dependency.

## Parent P0 receipt and verification outcome

P0 parent: `6180a183af1c669f46d6b7525393c21b2b33757b`.
Core CI [38452357365](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38452357365) concluded **SUCCESS**, including full root build, bundled stock root leanchecker replay, root axiom audit and complete Round3/Round4/Round6 compiler type exports (Round6 observed 23+22+15+9=69 defining-module declarations). Variable-envelope CI [38452357448](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38452357448) concluded **SUCCESS**. Earlier failing Round6 run `38428024402` must not be used as a receipt.

One producer-vs-integrator census discrepancy remains in the intake metadata: P1 listed generated `ImbalancedChen.actualPrimeBoxOwnCubeMinusSum.eq_1`, while the P0 defining-module census did not. Preserve the precise source/object inventories and their contextual differences; do not silently rewrite producer metadata.

## P4 supplier and exact source identity

P4 fixed producer: `a384f908968abf909d87fc1ec859e7b471d6af42`; specialized run [38387317409](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38387317409) succeeded. It ran five strict builds, five bundled leanchecker replays, a 75-declaration producer audit, and an aggregate fresh replay according to its archived run. The producer verification commands must still be checked for explicit trustLevel=0 binding before calling them equivalent to a standalone P0 three-gate receipt.

This batch changes only `ImbalancedChen/UpperCoefficientPerturbation.lean`, from Git blob `7b024033e58e19c0dcf94de322d6cb7d6815d987` to the producer's byte-exact blob `345858a00ee4eda72a90ba968c73a431397b3848`, adding exactly two existing lemmas (35 lines) with all other text unchanged:
- `ImbalancedChen.supportedDivisorSum_eq_of_subset`.
- `ImbalancedChen.supportedDivisorSum_le_of_zeroExtension`.

Direct imported module `ImbalancedChen/ActualSmallRoughAttachment.lean` is identical between producer and integrator: blob `28c930a8464a16d9acfb2b3580465f11def99acc`.

## Mathematical scope and obligations

The zero-extension lemma transports the *signed* finite divisor sum across raw and compiled supports under `Rraw ⊆ R` and vanishing raw coefficients on `R \ Rraw`. The companion inequality also requires `∀ d ∈ R, raw d ≤ compiled d`. These are **not** proofs of the actual `hUpper`, pointwise rough majorant, density estimates or total arithmetic error payment. `hLower` also remains unpaid, and the final `current_theorem_1_1_of_manuscript_bounds` bridge stays conditional.

## New P0 exact-head verification queue

This is a **SOURCE_ONLY_INTEGRATION_PENDING_ROOT_CI** handoff: it reuses the fixed producer evidence but does not claim the new P0 root has compiled. Require after this commit the matching-SHA core full build, root bundled leanchecker replay, transitive axiom audit, complete compiler types (including the two newly introduced declarations), Round6 census and variable-envelope gates. Retain all raw logs; do not treat old green CI as evidence for the new P0 SHA. Never merge default branch merely to validate.
