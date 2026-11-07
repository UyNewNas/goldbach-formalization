# P5.6/h34 — genuinely external inputs (fixed-Q filter ledger)

Previous HEAD: `c7f1d7911f41f2dcbc2c4f3a8665a03a9171db88`.
Mathematical source commit: `1af75f514aa62703c55e507f48823b6c3955e8c6`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`, blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Newly required external analytic inputs: NONE

No PNT, Mertens, BV, Buchstab, Rosser asymptotics or other external
analytic proof was added, changed or implemented. No new assumption,
custom axiom, theorem-equivalent licence or proof escape was added.

## Exact preexisting interfaces consumed

- `fixedQSlotPositionMap` and `fixed_q_slot_position_injective`
  from the preceding manuscript-local `Part5OriginalH430FixedQSlotInjection`
  candidate module. At a fixed literal physical Q, every observed
  `(Q,p,ell)` source slot is assigned an actual bounded
  `firstExitDepthFrontier 2` LIST position. Reused at
  `keptPositionMap` and `kept_position_injective`.
  These preceding proofs have NOT been compiled.
- `mem_firstExitDepthFrontier_ordinaryRosser_admissible_of_pos`
  from original `ImbalancedChen/FirstExitFrontierAdmission.lean`:
  for k>0 a genuine member of the original root
  `firstExitDepthFrontier k (ordinaryRosserRetainedPolicy lower Q)`
  has `ordinaryRosserPrefixAdmissible lower Q` at its complete prefix.
  Called with k=2 and true original
  `roughPrimeUniverse N cap 0 z0` at
  `actual_rank_two_full_prefix_passes`. This is a finite
  **manuscript-local** tree result, NOT an external Rosser bound.
- Pinned Lean/Mathlib `Finset.mem_filter`, disjoint finite-set union
  sums/counts, `Fintype.card_le_of_injective`, ordinary finite
  subtypes, `List.getElem_mem`, `decide_eq_true`, and `omega`.
  Called in `kept_erased_union`, `observed_slot_erasure_signed`,
  `kept_slots_le_kept_positions` and the actual full-prefix gate.

## Still manuscript-internal, NOT outsourced

The explicit arbitrary `keep` is only a finite predicate argument.
No theorem asserts it is the actual full/selected/inherited count gate,
or that the still-unmatched owner keeps a particular q/tag receipt.
Original count weights, actual phase/z0 and lower/upper, all exceptional
lanes, signed Euler payment direction, CLOSED-CELL induction, literal
base/seed/floor, PP/same-rho, native-history mass, and the common
430+11 nested causal refinement remain internal obligations.
Every finite numerical430 guard is UNEVALUATED.
