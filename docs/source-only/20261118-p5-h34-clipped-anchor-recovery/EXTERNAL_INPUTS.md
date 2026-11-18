# P5.6 / h34 — clipped selected-anchor recovery: external inputs

Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Pinned implementation: Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Verified incoming h34 HEAD: e22648772dbe5f30bd963e4780fb50acfd112369.
Source commit: 63779ff5ff426214fc752df031a2759474e6ae6d.

**New genuinely external analytic / number-theoretic hypotheses: NONE.**
No PNT, Mertens, BV, new prime theorem, extra arithmetic oracle, target-equivalent count condition, custom axiom, unsafe proof, or certificate bypass is provided.

## Existing math library interfaces (not recreated)

- Ordered-real \`min\`, \`max\`, subtraction, finite \`Finset.range\` sums, \`Finset.sum_range_succ\`, multiplication/distributivity and elementary \`linarith\` identities: candidate clipped_step_balance, clipped_range_balance, action_anchor_balance, bank_selected_anchor_balance. These are routine algebraic tools, not analytic count inputs.
- Finset nonnegative sums and order-preserving multiplication: candidate effectiveAnchorRise_nonneg, effectiveAnchorRecovery_nonneg, bank_selected_anchor_recovery_nonneg and bank_selected_effective_rise_le_backward_variation.

## Fixed original manuscript-local code reused

- \`P5OriginalFeedbackTableKernels\` original Q80 decoding, \`iterate k true\`, \`floorValue\`, actual W1/W2 fixed-cell and real endpoint definitions. The new \`effectiveAnchorRise\` and \`effectiveAnchorRecovery\` use the identical literal iterate k and k+1; no new update rule or independent recurrence is substituted.
- \`Part5OriginalH430SelectedPositiveAnchorPayment.actionPositiveAnchorAllowance\`, \`bankSelectedPositiveAnchorPayment\` and the true \`originalW2At\`, \`w1Cell\`, \`w2Cell\` anchors: candidate action_anchor_balance preserves the 4:1 W2 split, rather than assuming an unweighted scalar lookup.
- \`Part5OriginalH430SelectedAnchorBackwardVariation.actualUpperCellDrop\`, \`actionBackwardDrop\`, \`firstOriginalGeneration\` and \`bankSelectedSeedAnchorPayment\`: candidate effectiveAnchorRise_le_drop and bank_selected_effective_rise_le_backward_variation explicitly compare clipped deterioration with the earlier gross variation.
- Original \`Part5OriginalH430RequestedLevelBankSupply.selectedLevel\` and \`occurrenceScale_nonneg\`: selected finite-sum identity/inequalities retain actual occurrence multiplicity and physical same-Q Theta.
- Existing \`Part5OriginalH430ExactOuterQ80FloorCredit.frozen_root_le_prefloor_with_complete_credit\` includes both original integer-floor losses with capped, correct-sign credit. Existing \`Part5OriginalH430ClosedCellPositivePrefloor.bank_prefloor_le_closed_cell_positive\`, \`Part5OriginalH430ClosedCellIdealSplit.bank_closed_cell_positive_sandwich\`, and \`Part5OriginalH430SelectedPositiveAnchorPayment.bankFixedSlackMass_le_selectedPositiveAnchorPayment\` are composed in the root candidate; the full preceding CLOSED-CELL premise remains visible and UNPROVED.

## Unfinished manuscript-local consumers (NOT delegated externally)

- Actual finite Q80 update/seed estimates sufficient to bound the selected effective rise and zero-iterate endpoint gap, as opposed to merely showing a nonnegative decomposition.
- Genuine all-action CLOSED-CELL count induction, original base/fixed/switched/seed/floor, Buchstab retention/strict-prime physical source and terminal seed.
- Original U3/U4 full/selected/inherited count identity, causal owner, root norm 7/2, q/tag multiplicities and rejected lanes.
- PP/same-rho object/quantifier compatibility, native-history/signed Euler, outer integral–Theta–count and the common nested 430+11 refinement with unchanged c/K and row norm 12.
- Pinned Lean/Lake import-closure compilation, kernel replay, transitive axiom audit, and inherited finite guards (UNEVALUATED).

No custom axioms or externally justified h34 closing lemma have been added. Source-only Lean proof bodies are uncompiled candidates, not proof-correctness claims.
