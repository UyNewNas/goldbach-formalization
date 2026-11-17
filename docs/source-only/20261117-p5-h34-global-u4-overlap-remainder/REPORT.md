# P5.6 → h34 — complete original U3/U4 balance over distinct U4 overlap and remaining true Fin receipts

Date: 2026-11-17.
Base commit: `2a396049a3a364aeaeb06df9a64a01316074b69d`; mathematical-source commit: `3c30b592790a03c31177d19d6e3e398233313c0e`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## What is genuinely new

The previous 20261117 packet split ONLY the Fin positions occupied by distinct retained original U4 overlap slots into a mandatory two-tag baseline and all additional q/tag receipts on each slot. It did not show where the remaining true Fin-position original receipts or the four outside-source original rejections sat in the entire original U3/U4 count.

This packet supplies the complete *arithmetic source* reconciliation. It uses the real fixed-physical-Q Fin image from `Part5OriginalH430DistinctU4FinReceiptDebt`, and reuses the whole original tagged-source/four-lane result from `Part5OriginalH430FourLaneFullTaggedFin`. It introduces `otherFinUnitReceiptsAtQ`, an explicit, nonnegative count of original receipts at ALL other real Fin positions of the same Q. This is not a fake selected/inherited owner, representative q or discarded exceptional term.

For each real observed Q:
- `actual_all_tagged_unit_nonneg` and `other_fin_unit_receipts_nonneg` prove only the arithmetic nonnegativity of the new leftover count.
- `actual_fin_unit_overlap_partition` splits the entire real Fin list source into distinct U4-overlap Fin image and every other Fin occurrence, including unoccupied positions which have zero arithmetic source.
- `actual_fin_two_tags_excess_and_rest` refines this into two tags per distinct U4-overlap physical slot, all excess q/tag receipts on these slots, and all remaining Fin-position receipts.
- `all_observed_fin_two_tags_excess_and_rest` sums over every actually observed physical Q separately.
- `original_u34_count_full_overlap_balance` reconciles this complete observed source with the original U3+U4 count, retaining the exact FOUR outside-source rejection terms.
- `original_negative_quarter_full_overlap_balance` gives the same exact equality for the original Chen negative-quarter arithmetic contribution, without reversing its sign.

Writing D(Q) for the distinct U4-overlap occupied slots, E(Q) for extra original receipts on them, O(Q) for all other original receipts at true Fin positions, and L4 for the four real outside-source rejections, the *candidate source* identity is:

  Upsilon3(N) + Upsilon4(N) =
    sum_{Q observed} [2 * |D(Q)| + E(Q) + O(Q)] + L4(1).

Consequently the original negative-quarter contribution is minus one quarter of that entire right-hand side. There is NO claim that O(Q), L4, E(Q), or the two-tag baseline are small or paid by Euler history mass.

## Exact boundary / what remains open

The source is new and was committed, **not Lean compiled**. No Lean, Lake or Elan binary is on this execution container's PATH; native GitHub git access cannot resolve github.com; the pinned source-only import closure is not staged. No kernel replay, no transitive axiom audit and no finite certificate evaluation ran. Text search and GitHub blob/compare are not type checking. No green nodes are granted.

The following remain manuscript INTERNAL: binding each original full/selected/inherited causal owner to complete q/tag receipts (without duplicating owners when U4 overlaps); proving signed Euler/root norm 7/2 quantitative payment of 2*|D|, E(Q), O(Q), L4, and relevant other count losses; original selected-count bound; request-level Buchstab/retention and CLOSED-CELL all-action induction; original base/switched/seed/floor and manuscript PP/same-rho; native-history mass, Theta/integral/count and one genuinely shared 430+11 causal refinement. The upper Q-selected count has NOT been closed merely by this exact count-source identity.

No P1.4/P3.6 files, CI configuration, dependencies, old source packets, or master were edited. Original c/K, exact root norm 7/2, row norm 12, same Q, alpha, signed overlap, and source-count semantics are unchanged.

Next exact action: install the pinned transitive import closure without upgrading and incrementally compile this source plus its prerequisites. Then locate the actual frozen full/selected/inherited causal owner predicates and prove a concrete owner-to-tagged-receipt *payment* inequality (not another arbitrary filter or abstract receipt identity), starting with O(Q) and the unavoidable two-tag baseline.
