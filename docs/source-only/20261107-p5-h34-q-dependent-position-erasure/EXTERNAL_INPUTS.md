# External input boundary — per-Q actual position erasure

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
file `paper/source/manuscript-body.tex` (blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Toolchain: Lean `v4.33.0-rc1`; Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New external analytic inputs: NONE.** No PNT, Mertens, BV, distribution
or other external theorem has been reimplemented, strengthened or newly
axiomatized.

## Exact reused source and invocation

1. Manuscript-internal
   `Part5OriginalH430ActualPositionMassGap.complete_original_source_at_actual_positions`,
   invoked by `complete_original_source_with_q_dependent_erasure`
   with the **existing** `z0 ≤ (cap : ℝ)` premise. This theorem
   includes all original U3/U4 tagged quotient receipts and six
   explicit unpaid lanes; it is source-only, not independently compiled.
2. Manuscript-internal
   `originalWeightAtActualPosition`,
   `observedRankTwoMassAtPosition` and
   `originalRankTwoPositionMassGap`: definitions reused at
   `kept_position_original_weight_mass_gap` and the global ledger.
   The true rank-two history mass is inherited from the actual
   frontier `FirstExitFrontierInvariants` in the predecessor source,
   not postulated here; its old Mathlib/analytic dependency tree is
   not re-audited in this packet.
3. Manuscript-internal
   `Part5OriginalH430FixedQPositionFilterLedger.keptPositions`
   supplies real `Fin` LIST-index filtering. Standard Mathlib
   `Finset.disjoint_left`, `Finset.sum_union`,
   `Finset.sum_add_distrib`, finite filters, and ring algebra
   implement only the new finite partition proofs.
4. The new `keep : ℝ → FirstExitDepthState ℕ → Bool` is a free
   finite-bookkeeping **parameter**, NOT a hypothesis asserting
   that any event is full/selected/inherited or an owner. Its
   genuine manuscript match is an OPEN internal obligation.

## Manuscript-INTERNAL, not outsourced

Original count-stage full/selected/inherited exact predicates,
quantifiers, root count weights, rejected/event owner multiplicity,
physical stage matching, directional first-excluded signed Euler
suffix payment, request-layer Buchstab/retention and CLOSED-CELL,
feedback/floor/base/seed/PP/same-rho, native-history mass and common
430+11 causal refinement are all still OPEN.

SOURCE ONLY / UNCOMPILED / UNEVALUATED. No new axioms or proof escapes,
and no transitive axiom audit or numerical430 replay was carried out.
