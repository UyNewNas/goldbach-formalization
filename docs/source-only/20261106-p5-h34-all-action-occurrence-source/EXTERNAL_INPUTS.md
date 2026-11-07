# P5.6 → h34 — external inputs for all-action occurrence source

Fixed manuscript mapping is unchanged:
`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`, blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
The ordinary lower-tree starts at `w=a` or `w=h` (lines 695–696);
the symbolic projection presieve `z0=N^omega` is separate (lines 712–719).
No numerical omega or owner relation is inferred here.

## Newly introduced external number-theory inputs: NONE

No PNT, Mertens, BV, new Buchstab estimate, singular-series bound,
new axiom, or target-equivalent count licence is added or proved.

## Existing implementation facts consumed

- `Part5OriginalH430RequestedReads.Selected`, `resolve`,
  `resolve_none_value`, `ReadMode`, `roundDecision` and `iterate`.
  Scalar exterior zero is a statement about the actual current
  closed-cell lookup, not about the original U3/U4 count source.
- `Part5OriginalH430RequestedBranches.children`, `branchEdges`,
  `retained_edgeValue` and original `singleChildren` carriers.
  Retained is a specified-cell child; Buchstab preserves actual upper/lower.
- `Part5OriginalH430RequestedHistory.levelOccurrence`,
  `levelMark`, and `Part5OriginalH430RequestedLevelBankSupply.sum_selectedLevel`.
  Level indices are list positions and retain repeats, not a Finset of
  prime products or catalog cells.
- Ordinary Lean/Mathlib `Option.some.inj`, finite sums,
  `Finset.sum_filter`, constructor disjointness, and case splitting.

The above are source-level imports from the fixed version; the new module
is SOURCE_ONLY, not installed, compiled or kernel-replayed. Its exact
choice/partition candidate statements and their imported dependencies
must be elaborated before they can be treated as proofs.

## Explicit manuscript-internal obligations NOT outsourced

The partition of actual requested one-level values does not establish
Buchstab/retention coefficient bounds, a CLOSED-CELL count inequality,
correct base/fixed/switched/seed/floor applications, manuscript PP/same-rho,
original U3/U4 selected-count equality, its root weight/owner/filters,
or native-history/outer Theta/common 430+11 realization.
The previously discovered conditional presieve obstruction remains open
as a stage/owner matching question. No h34 closure credit is claimed.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED; no finite certificate evaluated,
no transitive-axiom audit and no CI dispatched.
