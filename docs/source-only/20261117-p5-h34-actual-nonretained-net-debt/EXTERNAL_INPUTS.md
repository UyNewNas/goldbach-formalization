# P5.6/h34 — nonretained physical net deficit: external boundary

Pinned manuscript ba6ec11d800eccc54406490631895e174de85766;
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

New external analytic inputs: NONE. New axioms: NONE.

Reused existing manuscript-local declarations:
- ActualRequestAllActionPartition.resolved_level_sum_all_actions,
  actual_choice_iff_selected, bank_level_iff_actual_bank
- ActualNetDefect.selected_buchstab_combined_unpaid,
  selected_bank_combined_unpaid, combinedPhysicalUnpaid_nonneg
- RetainedZeroNetDefect.actual_retained_level_combined_unpaid_zero
- RequestedReads.resolve_none_value and RequestedBranches.exterior_children_empty
- PhysicalRoots.rootQ and RequestedLevelBankSupply.levelMark/selectedLevel.

Mathlib Finset sums, List sums, real positivity and simp are reused.
No PNT/Mertens/BV lemma has been re-proved. There is still no
per-occurrence Buchstab/bank positive net gap payment: the existing
signed physical trim, coefficient estimates and row mass bounds are not
by themselves a source-matched proof of that payment.
Original U3/U4 full/selected/inherited owner, PP/same-rho, signed Euler
native-history and one 430+11 refinement remain INTERNAL, not outsourced.
No transitive axiom audit was run.
