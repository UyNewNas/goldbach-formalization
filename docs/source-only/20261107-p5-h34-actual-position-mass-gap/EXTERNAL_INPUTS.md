# P5.6/h34 — external input ledger for actual Fin-position mass gap

Pinned manuscript `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`
and Lean `v4.33.0-rc1` / Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**No new external analytic result or axiom in this packet.**
The proof bodies reuse the already-staged manuscript-local
`original_count_source_five_unpaid_lanes`,
`retained_receipts_actual_position_signed_ledger`,
`fixed_q_slot_position_prefix`, and actual rank-two frontier
definitions. These are NOT claimed independently compiled.

Already-present imported Mathlib finite `Fin`/`Finset` sum
reindexing, ring arithmetic and list simplification are used only as
general algebra. The actual source of state sign and mass is the
repository's existing `FirstExitFrontierInvariants`:
`mem_firstExitDepthFrontier_positive_eq_evenListLength` and
`mem_firstExitDepthFrontier_mass_eq_selected_prod`, invoked in
`observed_fixed_q_position_true_sign_mass`; their carrier is the
literal `roughPrimeUniverse N cap 0 z0`, their selector is the
unchanged `ordinaryRosserRetainedPolicy lower Q`, and the initial
prefix/sign/mass are exactly `[]/true/1`.

The PNT/Mertens/BV interface families are unchanged, not reproved
and not newly called by this packet. Any such inherited input from
the long source chain retains its original hypotheses and pinned
version; no transitive-axiom audit is claimed.

**Manuscript-INTERNAL and still OPEN:** true
`full/selected/inherited` count gate/phase binding, root-weight and
q multiplicity, actual signed first-excluded Euler suffix and its
directional payment, request-level Buchstab/retention and all-action
CLOSED-CELL, feedback-to-integral/seed, PP/same-rho, native-history
mass and one common causal 430+11 refinement. None becomes an
external hypothesis or an axiom merely by this accounting step.

SOURCE ONLY / UNCOMPILED / UNEVALUATED.
