# P2.9: exact root-cell dictionary for original marked masses

**Status: SOURCE_ONLY_UNCOMPILED. Formal credit: 0.**

This increment partitions the original U3/U4 root-prime sum by the already
defined cumulative `RootCode n`. It keeps the original prime `p`, the
dependent `LevelIndex N n root t p dep`, the selected finite set `B p`,
and every original `levelMark` in the sum. The new public mass conclusions
name the existing `ordinaryBad`, `markedConverted`, and `markedTheta`;
there is no replacement mass definition and no new J.

## Exact new source result

The sole new Lean file is
`ImbalancedChen/P2FiniteMarkedGamma5ActualRootCells.lean`.

- `originalRootCellBand` is the original `originalBand N root` filtered
  by the existing code of
  `(sourceRoot root t (physicalPrime N p)).physical.total`.
- `originalRootCellBand_Q` derives
  `rootQ N n root t p = cellQ N n c` from that membership. It reuses
  `Part5OriginalH430SameQHistoryCells.codeLevel_rootCode`; it does not
  choose a representative prime or differentiate a discontinuous rootQ.
- `ordinaryBad_original_cells` partitions the literal
  `sum p, sum l in B p, levelMark l * ordinaryBad N (rootQ ...) (wordProduct l)`.
- `markedConverted_original_cells` identifies the original full
  `sum p, markedConverted (B p)` with the root-cell sum of
  `levelMark l * (thetaConversion N (wordProduct l) *
  switchedFibre false N (cellQ N n c) (wordProduct l))`.
  This retains the inclusive Gamma5 and Gamma9--21 sources, all word-list
  repetitions, and the original d-dependent density conversion.
- `markedTheta_original_cells` uses exactly the same root cells and
  dependent history positions for the original seed normalizer.

All identities hold for every N, n, generation, root and t, with no
positivity, asymptotic, target-equality or payment hypothesis. The input
`B p` is an actual finite selection of the original dependent history
positions, as in the existing seed theorems; it is not a supplied
mass estimate. Taking `B p = seedPositions N n root t p` specializes the
generation-zero identities to the existing positive seed selection.

The root-cell index type is RootCode n and depends only on n. It is
fixed before N increases. The
actual prime p and its history index continue to vary inside the same
cell sum; the result does not replace them by a family chosen after N.

## Reused source and exact owner selection

The proof directly imports the selected old sources for
`Part5OriginalH430SameQHistoryCells` and
`Part5OriginalH430SeedSameCarrierPP`. In particular it reuses:

| Existing FQN suffix | Role |
| --- | --- |
| `Part5OriginalH430SameQHistoryCells.cellQ` and `codeLevel_rootCode` | Existing deterministic level of each cumulative root cell |
| `Part5OriginalH430SeedSameCarrierPP.converted_eq_untested` | Exact inclusive converted-to-untested source dictionary |
| `P2OriginalW2CentreThetaPayment.weighted_fiber_sum` | Retain all original marks when equal products occur |
| `Part5OriginalH430SeedHistoryMass.markedConverted`, `markedTheta`, `wordProduct` | Original seed expressions and original history products |

The full paths and blob/SHA256 pins are in REGISTRY.json. In a combined
closure, use the current radial-package owner postimage of
`Part5OriginalH430FrozenRootRefinement` together with
`P2FiniteMarkedGamma5FrozenConstants`. For the old arithmetic history
owners, retain the actual-source-rank postimages of
`Part5OriginalH430SeedHistoryMass`,
`Part5OriginalH430TaggedArithmeticReceivers` and
`Part5OriginalH430HistoryQuotientCounts` and their extracted cores.
Do not load an original owner alongside its relocated same-FQN core.

The old selection manifest is a source-selection reference, not a new
qualification of its full import closure. This increment does not
repair missing old imports, rebuild native suppliers or grant credit to
the historical source-only candidates.

## Duplicate-work check and the limited advance

The existing `SameQHistoryCells.sum_cellFamily` already partitions
`readyCatalog`, which contains the geometric all-Programs catalog.
Its `cell_Theta_exact` concerns that catalog. The existing
`RequestedMember.rootHistory_catalog` gives existence of a catalog
label preserving node, word and code; it is not an injective map of
history occurrences or a marked-mass equality. This increment uses none
of those catalog maps. It partitions the original actual sums directly.

The following existing work was found and is not repeated:

- `SeedConvertedMass.original_inclusive_converted_mass`,
  `seed_split`, and `SeedHistoryMass.converted_centre_on_histories`;
- `SeedSameCarrierPP.converted_eq_untested` and the marked same-source
  algebra in `purify_on_original_marks`;
- `ActualSwitchedSmallPayment.all_marked_small_products`,
  `marked_split`, and `actual_small_product_difference`;
- cumulative root-code construction, root-table approximation, and
  the absolute finite query approximation.

The small-product supplier pays the Gamma9--21 small-product terms; its
remaining balance retains Gamma5 literally. That scope is unchanged.

## Remaining manuscript mainline obligation

The source identity now uses a fixed finite list of root-cell endpoint
functions `N |-> N ^ codeLevel n c`, instead of varying Q with a prime
parameter outside the sum. This removes the need for a proposed
rootQ-as-coordinate chain-rule construction.

A smooth admitted family for the actual selected histories is still
required. It must retain the original read/branch/source restrictions,
their marks and coordinate multiplicities, and admit one common
approximation before N increases. A geometric all-Programs catalog
cannot replace those selected histories without changing the mass.
Neither uniform Euler constants for separately fixed p nor finiteness
of `LevelIndex` at each N supplies that assertion.

The existing `ordinaryBad` has complete product at most N. The new
radial package's `naturalOuterMass` covers smooth prime support with
complete product greater than N. They are different pieces, so there
is no equality between those two masses. The next analytic comparison
must bound the full actual smooth ordinary mass by its original sharp
ordinary mass plus the radial excess and the other proper-boundary
excesses, with the same original coefficients. It must then recover the
original finite J bound; no new J is defined here. The original
thetaConversion is also left intact, rather than silently absorbing it
into a smooth weight.

No PP, VM, density, selected-count closure or original U3/U4 count
identification is inferred. The 29 native H247 endpoints remain an
existing native-Binder sufficient/compatibility branch; this increment
does not assert that they are 29 necessary manuscript-mainline duties.

## Manuscript scope

At immutable manuscript ref
`a988cba584d803ae2856a0de50efb582f4f3dd6a`:

- `paper/release-20261106/en/sieve-appendix.tex:494--552` fixes the
  original common Q, selected slots, ceiling and positive marked family.
- `sieve-appendix.tex:1033--1101` requires the same positive marked
  counts, a fixed finite collection of queries before N, and absolute
  errors at zero mass.
- `argument.tex:359--407` applies positive-product distribution to a
  fixed admitted bounded-rank family with its ordinary mass bound; its
  smooth outer approximation fixes precision before taking N to infinity.

The new identities fill a finite-expression omission. The actual smooth
history realization and its ordinary-J comparison remain substantive
formal obligations; this audit does not establish a mathematical
counterexample to the manuscript.

## Validation and publication

The source has been checked statically for preservation of p-dependent
indices, original coefficients, finite-code quantifiers, empty sums and
equal-product multiplicities. No local or cloud compilation was run.
There are no proof holes, new axioms, native_decide or unsafe commands
in the new file. Static inspection is not kernel validation. An independent reviewer read
the exact new source blob and the four old source suppliers, checked the
finite-sum and dependent-index rewrites, and found no source-level
semantic obstruction. That review also grants no compilation credit.

Only GitHub blob objects are created for review. The parent agent owns
any commit, ref update, source staging and subsequent compilation.
