# P5.6 → h34 — external input boundary: positive closed-cell ideal/fixed split

Pinned manuscript: \`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766\`.
Pinned toolchain: Lean \`v4.33.0-rc1\`, Mathlib \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`.

**New genuinely external analytic inputs: NONE. No new custom axioms.**
This packet implements only manuscript-local finite row decomposition, nonnegative theta/mark transfer, and positive-part inequalities, using existing pinned source-only interfaces. Those prior Lean declarations are UNCOMPILED candidates, not certified external black boxes.

## Reused manuscript-internal interfaces, exact consumer sites

- \`Part5OriginalH430FixedReadRows.cellReadIdeal_split\`, \`readFixed_value\`:
  original \`cellReadIdeal a b = readFixed 1 a b + dynamicIdeal a b\`, and sum of \`readFixed theta a b * oldAtomValue H h b = theta*fixedValue H a\`, for any original 106 action, signed arrays and real theta. Consumer: \`idealCellProfile_fixed_dynamic\`, then \`closedCellPreFloorAtom_exact_split\`.
- \`Part5OriginalH430SelectedFixedReadSupply.idealCellProfile\`: original sum over \`RowAtom\`, upper and lower old arrays as actually used. Consumer: exact split; no new normalizing constant.
- \`Part5OriginalH430ActualFixedClosedCell.selected_fixed_reference_upper\`: under \`∀ i : Fin 200, ∀ s ∈ queryCell i, floorValue (iterate g.val true) i ≤ F s\`, guarantees \`fixedValue (iterate g.val true) a ≤ fixedReference F a\` for every actual \`Original106Action\`. Consumer: \`fixedReadSlack_nonneg\` and pointwise positive sandwich. This *predecessor hypothesis* remains a manuscript-local unproved induction premise; it is NOT outsourced.
- \`Part5OriginalH430RequestedMember.rootHistory_support\`, \`parentWindow_logs\` and existing \`thetaAtom_nonneg\`: under \`4 ≤ N\`, \`0 ≤ tau ≤ 1/12\`, \`1/(n+1) ≤ 11/384\`, actual prime/coprime and physical root band, give genuine nonnegative parent theta on each actual \`Fin\` occurrence. Consumer: \`true_occurrenceTheta_nonneg\`, then level positive sums. Same root-specific \`Q\` preserved.
- \`Part5OriginalH430RequestedLevelBankSupply.selectedLevel\` and existing positive \`levelMark\`/\`mark_pos\`: genuine original 106 selected requests and list-position multiplicity. Consumer: \`bank_closed_cell_positive_sandwich\`, \`bank_fixed_slack_nonneg\`.
- \`Part5OriginalH430ClosedCellPositivePrefloor.frozen_root_le_closed_cell_positive_with_credit\`: existing conditional true-root upper for 430 generations, all actual seed/Buchstab/bank/applied terms with capped floor credit on the left. Consumer: \`frozen_root_le_ideal_balance_plus_fixed_slack\`.

## Reused foundational Lean/Mathlib reasoning

Finite \`Finset.sum\` distributivity, \`max\` monotonicity, \`mul_nonneg\`, \`mul_le_mul_of_nonneg_left\`, \`ring\` and \`linarith\`. No PNT, Mertens or BV theorem is re-proved.

## Internal obligations not reclassified as external

Positive \`base + idealFeedback - dynamicIdealProfile\` quantification; actual nonnegative W1/W2 fixed slack control; correct induction base/seed/floor/switch; genuine U3/U4 owner, root factor 7/2, full/selected/inherited filters, rejected lanes and q/tag; manuscript-local PP/same-rho correspondence; native-history, signed Euler, outer integral–Theta–count, and common 430+11 causal refinement.

No Lean compile, kernel replay or transitive axioms audit has occurred, so neither this packet nor its transitive imports is certified.
