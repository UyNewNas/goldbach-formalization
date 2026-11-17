# P5.6/h34 — selected request all-action wave / external input boundary

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean `v4.33.0-rc1`; Mathlib commit `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New external analytic inputs: NONE.**

## Reused interfaces and invocation points

* Pinned Lean core/Mathlib: List map/flatMap/append finite sum algebra and real
  distributivity, used in `sum_map_flatMap`, `sum_map_scale`,
  `wave_successor`. These are foundational library operations, not new
  PNT/Mertens/BV assertions.
* Existing **manuscript-local, uncompiled candidates** from
  `Part5OriginalH430RequestedBranches`: `children`, `branchEdges`,
  `edgeWeight`, `edgeValue`, `edgeRow`, `retained_edgeValue`,
  `edgeRow_value`, `exterior_children_empty`. The new module invokes
  them in `step_exterior_zero`, `step_retained`, `step_buchstab`,
  `step_bank`, `step_row_value`.
* Existing **manuscript-local, uncompiled candidates** from
  `Part5OriginalH430RequestedHistory`: `history`, `origin`,
  `prepend`, `mark`, `mark_origin`, `mark_prepend`;
  used in the finite wave zero and successor theorems.
* `Selected`, `resolve` and `roundDecision` remain the literal
  production request reader; no alternate or strengthened selection is
  substituted. The new `step_retained` and `step_buchstab` require
  only the real selected-choice proof.

## Still internal and not outsourced

Actual quantitative request-level Buchstab/retention; CLOSED-CELL count
induction, base/switched/seed/floor; complete U3/U4 original count owner,
full/selected/inherited filters, signed Euler and root norm7/2 payment;
same-rho/PP compatibility; native-history/Theta/integral and one
430+11 causal refinement. No h34-equivalent axiom, assumed count licence,
sorry/admit, unsafe or external theorem proof is introduced.

No independent verification of earlier external inputs or transitive
axiom closure is claimed. Source remains UNCOMPILED, finite certificates
UNEVALUATED.
