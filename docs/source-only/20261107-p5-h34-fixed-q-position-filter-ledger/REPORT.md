# P5.6 → h34 — true fixed-Q rank-two LIST position erasure ledger

Date: 2026-11-07.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Verified prior HEAD: `c7f1d7911f41f2dcbc2c4f3a8665a03a9171db88`.
New mathematical source commit: `1af75f514aa62703c55e507f48823b6c3955e8c6`.
New Lean module: `Part5OriginalH430FixedQPositionFilterLedger.lean`
(204 lines, 10 theorem bodies, 5 definitions and 1 abbreviation; source blob
`4048a967b297b020ea6f75f26c55b860d75b6b76`).
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Pinned Lean: `v4.33.0-rc1`; Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE ONLY / UNCOMPILED / UNEVALUATED.**
Complete manuscript-internal h34 remains OPEN.

## New exact source obligations addressed

1. The preceding packet injected distinct observed physical `(Q,p,ell)`
   slots into genuine `Fin` positions of `actualPhysicalRankTwoList` at
   the SAME physical Q. This packet constructs a post-frontier position
   filter `keptPositions` by a literal Boolean state test, retaining
   actual LIST indices rather than converting to distinct state values.
2. `keptSlots` and `erasedSlots` partition the observed fixed-Q
   source according to that slot's previously selected actual list position.
   `kept_erased_union`, `kept_erased_disjoint`,
   `observed_slot_erasure_card`, and
   `observed_slot_erasure_signed` supply exact unsigned and arbitrary
   signed reindexing. The deleted slots are UNPAID, not silently dropped.
3. `keptPositionMap` uses the previous actual `fixedQSlotPositionMap`
   only for survivors. `kept_position_injective` and
   `kept_slots_le_kept_positions` prove that distinct surviving physical
   slots consume distinct kept bounded historical LIST positions.
   `slot_capacity_with_erasure` retains every erased slot explicitly:
      |observed Q slots| <= |kept historical positions| + |erased Q slots|.
   This is pre-payment capacity accounting, NOT an inequality for original
   tagged q receipts and NOT an assumption about the manuscript owner.
4. The specifically instantiated `actualFullPrefixGate` is the
   original `ordinaryRosserPrefixAdmissible lower Q` used by the same
   `firstExitDepthFrontier 2` recursion. Applying the existing actual
   positive-rank frontier admission theorem at each Fin position proves
   `actual_rank_two_full_prefix_passes`, then proves ALL actual
   rank-two positions survive this *one* full-prefix Rosser test and
   `actual_full_prefix_erases_no_observed_slots`. No threshold Q>1
   is inserted: the positive-rank theorem supplies admission directly.

## Critical distinction / open binding

The generic Boolean `keep` above is a finite transport variable,
not a hypothesis that the original manuscript `full/selected/inherited`
count filter is true. The one concretely discharged `actualFullPrefixGate`
is the ordinary first-exit full-prefix Rosser admission test. It is
**not** identified with the whole manuscript's full/selected/inherited
count-source filtration, physical phase switch, or original owner weights.
Erased slots for the still-unbound gates are NOT shown empty.

Surplus original q within one tagged key, U3/U4 cross-tag collisions
and shared Q/p/ell slots still have the earlier explicit unpaid ledgers.
The root U3/U4 count weights are not the first-exit rank-two mass;
the original q need not be a prime. No double payment is inferred.

## Verification & repository isolation

- Prior GitHub ref, exact source commit and blob, and one-file source diff
  were read back. Source change was a non-force fast-forward with the
  previous remote HEAD as the expected SHA.
- 204 lines, 10 candidate theorem bodies, 5 definitions, 1 abbreviation.
  Raw delimiter count balances and forbidden proof escape token scan passed.
  These are only static checks and are NOT Lean parsing, elaboration or
  proof checking.
- No Lean/Lake execution, heavy compilation, CI dispatch, kernel replay,
  transitive axiom audit, independent review or finite numerical430
  replay. All inherited and new finite obligations remain UNEVALUATED;
  no green status or formal-credit claim.
- No P1.4/P3.6, production modules, toolchain, CI, parameters, fixed
  manuscript, or prior packet was edited.

## Exact next task

Read the actual manuscript-local `full/selected/inherited` source
predicates AND the original generated/arithmetical phase gates. Identify
which actual `FirstExitDepthState` and `Fin` occurrence passes each
specific gate, then instantiate the survivor/erasure ledger with those
actual tests and carry deleted original receivers to the unpaid lanes.
Do not assert the Boolean `keep` corresponds to an actual count gate
until that identity is derived. Continue the literal tagged q/root-weight
owner with all collisions and signed Euler payments.

Remaining independent manuscript duties: request Buchstab/retention
and all-action CLOSED-CELL; correct base/switched/seed/floor,
feedback integral–Theta–count and local PP/same-rho; native-history
proper/equality/inherit mass and one common nested causal430+11
refinement. Subsequent staging, compilation, kernel replay, exact
transitive-axiom audit and finite table verification remain required.

完整 h34 稿内证明仍未闭合。
