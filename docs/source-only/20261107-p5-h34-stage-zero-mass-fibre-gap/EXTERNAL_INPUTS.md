# P5.6 h34 — external-input boundary for rank-one mass / q-fibre gap

Status: SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Original manuscript remains pinned to
`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex` blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Lean toolchain remains `leanprover/lean4:v4.33.0-rc1`.
Mathlib remains `leanprover-community/mathlib4@e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Existing external inputs called but not implemented

- Lean/Mathlib list constructor equality, finite sums and sum
  distributivity, casts, prime `one_lt`, `linarith` and `ring`.
  Called in candidate mass/suffix proofs and root-fibre surplus
  bookkeeping. No analytic number theory is newly assumed or proved.
- Existing compiled infrastructure:
  `ImbalancedChen.FirstExitCandidateGeometry.mem_firstExitNextSelectionCandidates_iff`,
  `decreasingList_suffix_eq_filter_lt`,
  `roughPrimeUniverse_pairwise_gt`,
  `roughPrimeUniverse_filter_lt_eq`, and
  `mem_roughPrimeUniverse_upper`.
  Called by `stage_zero_candidate_mass_sign` and
  `stage_zero_candidate_exact_suffix`. Their exact original carrier,
  descending order and cap assumptions are preserved.

## Existing manuscript-local interfaces (NOT external)

- `Part5OriginalH430ActualRootStageReceipts.originalStageRoot`
  and `selected_stage_signed_original_fibres`, at the unchanged
  true physical per-root Q. Used in
  `original_stage_root_exact_geometry`,
  `stage_original_receipt_root_mass_total` and the mass gap.
- `Part5OriginalH430TaggedArithmeticReceivers.original_band_prime`,
  `originalBand`, `originalReceiver`, `originalTagged`.
  Used in the actual positive root-mass and q-fibre calculations.

Every above candidate source-only interface remains uncompiled; no
claim is made that the whole transitive trust closure has been audited.

No PNT, Mertens, BV, Buchstab distribution theorem or other external
analytic result was created, strengthened or proved. No target
equivalence is assumed. The manuscript's own q-owner mapping,
selected/full/inherited filters, signed payment and common refinement
are still INTERNAL obligations.
