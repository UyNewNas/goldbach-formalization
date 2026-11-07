# P5.6 → h34 — original q/tag arithmetic weights at actual rank-two LIST positions

Date: 2026-11-07.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Verified predecessor HEAD: `9264d50919221afabd9451c530c070aa18343cf7`.
New mathematical source commit: `06f16cfc3664818aace3615e27224b701a532fee`.
Source: `Part5OriginalH430TruePositionReceiptLedger.lean`, 235 lines,
3 definitions and 7 candidate theorem proof bodies; Git blob
`d3fe3a8527eb59fd3fda8af9f512607749fa8da9`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Toolchain pinned: Lean `v4.33.0-rc1`; Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE ONLY / UNCOMPILED / UNEVALUATED / COMPLETE H34 OPEN.**

## Actually added

The previous fixed-Q packets established finite `Fin` positions in the
literal `firstExitDepthFrontier 2` LIST for distinct observed physical
`(Q,p,ell)` slots and separated kept/erased slots for a Boolean position
test. But no actual original arithmetic q/tag receipt weight had been
transported onto these positions. This packet provides that next bridge.

- `observedReceiptQs` is the finite *actual observed* physical-Q image,
  not a fabricated common-Q pool.
- `slotRepresentativeArithmeticWeight` evaluates an arbitrary original
  `w : TaggedReceiver → ℝ` on the previously selected **original q/tag
  representative** of each physical slot. Its value may depend on the
  original quotient q, tag and root p. It is NOT the history mass.
- `originalWeightAtActualPosition` sums those genuine receipt weights at
  a true bounded `Fin` position of the fixed-Q rank-two history LIST.
- `actual_position_rep_weight_sum` reindexes exactly between every
  actual list index and all observed source slots at that Q.
  `actual_position_preimage_subsingleton` preserves the previous
  injection: a fixed-Q position cannot be claimed by two distinct
  physical slots. `actual_position_weight_zero_outside_slots`
  identifies positions that carry no representative arithmetic receipt.
- `actual_prefix_keeps_position_rep_weights` instantiates the **one real
  recursive ordinary Rosser complete-prefix gate**. This gate already
  holds for every actual rank-two list member. It is explicitly NOT the
  manuscript's entire full/selected/inherited count-source filter.
- `observed_slot_rep_weight_by_Q` and
  `observed_slot_rep_weight_at_actual_positions` sum across distinct
  original physical Q values, each with its own genuine rank-two list.
- `retained_receipts_actual_position_signed_ledger` transports the
  ORIGINAL U3/U4 retained q/tag source (arbitrary signed q-dependent w)
  to (i) one representative arithmetic receipt weight per actual
  historical position at each physical Q, (ii) EVERY colliding tagged
  key at one physical slot, and (iii) EVERY additional original q at
  one tagged key. Terms (ii) and (iii) are **UNPAID**, not dropped.
  The position term (i) is also only arithmetic bookkeeping; it has
  NOT been proved to equal the signed Euler event, owner payment or
  native historical mass.

The packet does not add a source-count licence or change the true
c/K, root norm 7/2, row norm 12, physical Q, alpha, U3/U4 overlap,
scalar-vs-specified-cell reading or original q-occurrence multiplicities.
It does not touch P1.4/P3.6, production files, CI, toolchain or manuscript.

## Exact remaining manuscript-INTERNAL obligations

1. Bind original count `full/selected/inherited` filters and lower/upper,
   physical z0, phase switch to the genuine Fin positions. The one ordinary
   Rosser full-prefix gate is insufficient.
2. Prove source count-specific weights, root weights, q/tag owner
   multiplicities and correct **directional** signed Euler payments.
   Cross-tag collisions, same-key surplus and root/second-stage policy,
   cutoff, no-factor and non-event exclusions are still UNPAID.
3. Complete all-action request-level CLOSED-CELL induction, all genuine
   Buchstab/retention source consumption, feedback rounding and integral
   terms, literal base/switched/seed/floor.
4. Finish manuscript-local PP/same-rho, native-history mass,
   integral—Theta—count connection and the ONE common 430+11 nested
   causal refinement. None may be reclassified as an external theorem.
5. Install and compile the source-only chain, kernel-replay, audit
   transitive axioms and check inherited finite numerical430 guards.

## Verification and safe continuation

Authenticated GitHub source readback: blob
`d3fe3a8527eb59fd3fda8af9f512607749fa8da9`.
The source commit compared one added Lean file / 235 added lines / zero
deletions against `9264d50919221afabd9451c530c070aa18343cf7`. Before writing, static forbidden-proof-marker
and raw delimiter-balance checks passed. Those are NOT Lean elaboration.
No Lean/Lake was executed; NO CI was dispatched, NO kernel replay,
NO transitive-axiom audit and NO numerical430 certification occurred.
All candidate proofs and finite guards remain UNEVALUATED; no green node.

Next precise action: instantiate the true manuscript selected/inherited
predicates and phase/owner against these actual Fin positions, proving
which original source receipts survive each filter, and carry every
unmatched position/q/tag or rejection as a signed unpaid debt. Do not
turn arbitrary arithmetic w or a Boolean filter into a payment licence.
