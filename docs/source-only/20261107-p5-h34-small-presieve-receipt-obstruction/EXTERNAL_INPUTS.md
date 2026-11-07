# P5.6 h34 external-input boundary — small-presieve original receipt obstruction

Fixed manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766,
paper/source/manuscript-body.tex blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79.
Toolchain: Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**NEW EXTERNAL ANALYTIC INPUTS: NONE.**

## Precisely reused internal interfaces and application sites

- OriginalSelectedRootFibres.original_selected_all_cutoff_if_small: for actual originalTagged N, the whole source equals its actual rootCutoffBlocked family when z0 <= N^a. Called by physical_accepted_empty_of_small and six_unpaid_lanes_eq_cutoff_of_small.
- OriginalSelectedRootFibres.selected_root_licensed_iff: for a REAL original receiver, rootLicensed under actual tag/p-dependent physical Q implies strict p < z0. Called by physical_accepted_empty_of_small.
- ActualRootStageReceipts.physical_accepted_eq_actual_stage: with unchanged z0 <= cap, connects original stage-zero next-selection candidates to actual physicalRootAccepted. Called by original_stage_empty_of_small.
- TaggedRankTwoFibreCapacity.retainedReceipts / observedRankTwoKeys, PhysicalSlotCollisionLedger.observedPhysicalSlots, TruePositionReceiptLedger.observedReceiptQs: actual original q/tag source and physical-Q/Fin history ledgers, reduced to emptiness without re-indexing or deduplication. Called by the corresponding new empty-source lemmas.
- QDependentPositionErasure.complete_original_source_with_q_dependent_erasure: exact all-original signed accounting at physical Q-dependent kept list positions, arithmetic/history gap, erased original weights and six unpaid lanes, with the real z0 <= cap. Called by complete_original_source_unpaid_of_small.
- TaggedArithmeticReceivers.original_U34_eq_tagged_card: literal original selected U3/U4 tagged q-count identity. Called by original_U34_count_unpaid_of_small.
- Standard Mathlib Finset filters, empty-set image, sums and real arithmetic are reused, not reimplemented.

The new condition z0 <= N^a is a local premise of the obstruction, NOT a theorem about the selected manuscript's actual presieve. Its negation alone is not an owner licence. This packet neither assumes the final h34 goal nor implements PNT/Mertens/BV or any other external proof.

## Explicitly internal and still open

The correct z0/presieve stage, genuine full/selected/inherited count filter, original root weights, q/tag owner multiplicities, signed first-excluded Euler suffix payment, request-level all-action CLOSED-CELL, base/seed/floor, PP/same-rho, native-history mass, outer Theta/count matching and common nested430+11 causal refinement all remain manuscript-INTERNAL, unproved.

SOURCE ONLY / UNCOMPILED / UNEVALUATED. Transitive axioms and inherited numerical certificates were not audited.
