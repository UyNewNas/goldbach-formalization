# P5.6 / h34 — marked-source degeneracy: external inputs

This packet introduces **no new external analytic theorem** and no new custom axiom.

Reuses the existing in-repository manuscript-local definitions and source-only consumers at the fixed revision:
- `P2EnhancedTwentyOneSameQWeighted.Phi`: exact finite sum of nonnegative coefficient times natural source sieve count.
- `P2EnhancedTwentyOneSameQWeighted.Theta`: exact physical Q normalizer; zero sigma kills the finite sum.
- `Part5OriginalH430TrueCountMarkedGap.unpaidOriginalMarkedGap`: original arithmetic q-cardinality minus five times the positive marked Phi, truncated at zero.
- Mathlib: `Finset.sum_le_sum`, `Finset.sum_le_sum_of_subset_of_nonneg`, cast nonnegativity, monotonicity of multiplication and max, and linear arithmetic.

None of these is claimed compiled or kernel-certified in this packet. The local q-source-to-marked family matching, its threshold/quantifiers, root-specific Q, H430 full/selected/inherited owner, PP/same-rho, and joint 430+11 causal refinement remain **manuscript-INTERNAL** and must not be moved into this external-input registry as assumed theorems.

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` (`paper/source/manuscript-body.tex`). No external input changes.
