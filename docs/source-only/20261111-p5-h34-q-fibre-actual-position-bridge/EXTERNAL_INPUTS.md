# P5.6 / h34 — external input boundary: original q-fibre actual-position bridge

Manuscript remains fixed: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`.
Mathematical commit: `a10dc0f05616fa880d20b44dc9c28c86a15c8460`. Source: `Part5OriginalH430OriginalQFibreActualPositionBridge.lean`.

**New external analytic theorems or axioms: NONE.**

No PNT, Mertens, BV, Rosser, prime-distribution, prime-square-sieve or other classical external input was reproved or declared.

Existing fixed local imports and exact use sites:

- `ImbalancedChen.Part5OriginalH430OriginalQFibrePhysicalDebt`: `original_q_fibre_physical_gap_is_tagged`, `original_q_fibre_physical_gap_abs_bound`, `originalQFibrePhysicalGap`, `originalQFibrePhysicalSourceDebt`, `originalQFibreSelectedRowError`. Used in the original tagged receipt correspondence and final bound. These are prior **manuscript-internal candidates**, not new external assumptions.
- `ImbalancedChen.Part5OriginalH430QDependentPositionErasure`: `complete_original_source_with_q_dependent_erasure`, `actual_position_signed_partition`, `erasedOriginalPositionArithmetic`, `keptOriginalRankTwoMass`, `keptOriginalRankTwoGap`. Used for the actual Q-dependent positions and true erased-position source term; this is prior **manuscript-internal** work.
- Existing original true-position and ordinary complete-prefix results: `actual_position_rep_weight_sum` from `Part5OriginalH430TruePositionReceiptLedger` and `actual_prefix_keeps_position_rep_weights` plus `actualFullPrefixGate` from `Part5OriginalH430FixedQPositionFilterLedger`. Used to prove the erased arithmetic term is exactly zero under the actual ordinary prefix gate, without asserting full/selected/inherited equivalence.
- `Part5OriginalH430ActualPositionMassGap.originalSixUnpaidReceiptLanes` is carried unmodified; it contains the two collision/surplus lanes, post-root failure, no second prime, root cutoff and root policy exclusion.
- Standard Mathlib finite-sum algebra, ring arithmetic and linear arithmetic (`Finset.sum_eq_zero`, `linarith`) are invoked through the unchanged imported Mathlib dependency graph; no new analysis is outsourced.

**Remaining MANUSCRIPT INTERNAL, not recategorized as external:** actual full/selected/inherited compatibility, q/tag owner at true historical positions, positive arithmetic-to-history payment, root 7/2/row 12, six rejection lanes, seed/floor/base/switched inductive comparisons, PP/same-rho and native-history Euler suffix, Theta/integral/count consumer and causal 430+11 nested refinement.

The new Lean source remains uncompiled. Kernel replay, transitive axiom audit and finite430 evaluation are not performed. No sorry/admit/custom-axiom escape was introduced.
