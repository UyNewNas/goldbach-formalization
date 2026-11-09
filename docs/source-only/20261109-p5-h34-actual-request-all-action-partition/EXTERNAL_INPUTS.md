# External input ledger — actual request all-action partition (2026-11-09)

**New genuinely external number-theory inputs: NONE.**

Pinned manuscript (unchanged): `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. No manuscript switch, no c/K adjustment, no alteration to root norm 7/2, row norm 12 or true alpha.

## Existing foundational and mathematical APIs

- Mathlib `Finset.filter`, `Finset.mem_filter`, `Finset.sum_filter`, finite unions and disjoint sum, `Option.map`, dependent `Fin` indexing and finite sum rewrites. Reused as ordinary library facts, not new analytic axioms.
- `Part5OriginalH430RequestedReads`: `resolve`, `Selected`, `requestValue`, `resolve_none_value` and the original scalar/specified-cell read semantics. Invoked by `actualChoice`, `actual_choice_iff_selected` and `unresolved_level_value_zero`.
- `Part5OriginalH430RequestedHistory`: `levelOccurrence`, `levelMark` and the original index of generated occurrences. Invoked throughout to preserve actual request generations, original path multiplicities and positive weights.
- `Part5OriginalH430RequestedLevelBankSupply`: original 106-bank `Index`, `selectedLevel` and `sum_selectedLevel`. Reused by `bank_level_sum_eq_original_106` and `resolved_level_sum_all_actions`. Its preceding analytic local estimate remains a SOURCE-ONLY UNCOMPILED manuscript-local candidate, not an externally validated theorem.
- `Part5OriginalH430BankSlotTargets`: exact `actionOfSlot` / `slotOfAction` bijection through `slot_action`. Used for bank exhaustiveness over `Fin 106`.
- `P5OriginalFeedbackTableKernels`: original `roundDecision`, `iterate`, `Choice`. Used only at the actual resolver output; no replacement scalar owner is invented.

## Mathematical obligations NOT outsourced

The new source gives an exact request-action FINITE partition, not the manuscript count induction. Actual Buchstab/retention error supply, all-action CLOSED-CELL estimates, correct base/seed/floor, full/selected/inherited source-owner matching, original U3/U4 q/tag count multiplicity, actual remaining signed Euler payment, PP/same-rho, native-history and nested 430+11 are **manuscript-internal and still open**. These obligations are not marked external or replaced by assumptions of their own conclusions.

Nothing in this packet rederives or alters PNT, Mertens, BV or any other genuinely external analytic theorem. There is no new `sorry`, `admit`, custom axiom, unsafe or native proof escape. The existing fixed-source prerequisite packets have not been compiled or audited here; no independent Lean proof credit is inferred from a text-only source increment.
