# P2.4 remaining-source and finite-reuse preflight — 2026-11-26

## Evidence boundary

Read-only source review at proof commit
`d9fae118e953a21e02b1e9ca12b7a2b240070a7e`, while original strict-symbolic-14
task `1edd6847bc294245944456c45df78619` remained queued behind other P2 work.
The last completed strict result remains **301/321 symbolic modules accepted**.
These observations add no compilation, finite-evaluation, or audit credit.
The fixed mathematical scope and 324-module closure are unchanged.

## Remaining symbolic source

Independent review found no definite source-level blocker in Q80Arithmetic,
Q80ArrayTable, Q80CacheEncloser, Q80LogGuards, Q80FixedBindings,
Q80JensenSelection, or Q80Leaf. This does not predict compiler acceptance.

One narrow point is retained for comparison with actual diagnostics:
`P2OriginalCompactQ80CompleteSoundness.list_local_charges` currently uses
`simpa only [val,scale] using h p (by simp)`. Its source denominator unfolds
to `(((2 : Int)^80) : Real)`, while the target uses `(2 : Real)^80`.
Explicit cast normalization may be required. No speculative repair was made.

The call to `nonneg_of_mul_nonneg_left` in Q80Selection was independently
checked against locked Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`,
`Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean`:
the signature accepts `0 <= a*b` and `0 < b` to conclude `0 <= a`.
The existing argument order is correct and should not be changed.

## Existing table-certificate components

This is a reuse inventory, conditional on an actual finite resource failure.
Neither finite candidate A nor B has failed or been evaluated by this review.

- `Certificates/OriginalNodeArraysV1/DataCore.lean` supplies the generic
  four-integer `RawNode`, depth-indexed `NodeTree`, `NodeTree.read`, and
  depth-12 `Block` carriers. Its current initializer and assembled reader
  are specific to Q112 and are not a Q80 certificate.
- `CheckerCore.readCheckBlock_sound` and
  `readCheckBlock_of_64_pages` show the existing block and 64-page aggregation
  pattern. Their current update predicate is specific to the old recurrence;
  its existing checked literals cannot establish Q80 update equations.
- `DelayedPageTransfer.original_read_slot_coverage` provides the existing
  geometry for current and delayed dependencies in the four slots
  `b-5,b-4,b-1,b`. The Q80 update reads the same dependency indices, but a
  Q80 update-congruence theorem would still be needed.
- `ActualThirdOriginalStoredNodeQueryLookup.checked_reader_state_characterization`
  and `CheckedBlockTable.read_eq_original` provide a structural proof pattern
  from exact local recurrence equations to equality of total table readers.
  Their current statements fix the old recurrence and cannot simply be
  instantiated with Q80.

Any such adapter would need to establish exact total equality to the existing
Q80 `sourceTable`, including its initializer and out-of-range default. The
current `WithTable` and cached-run interfaces accept `Array Node`, so a tree
reader is not a drop-in replacement for `tableArray`. The analytic Q80 query,
rounding, leaf, and integration theorems can remain unchanged after an exact
reader equality is proved. No adapter or new proof was written here.

## Existing run interfaces and their limit

`cachedStep_eq` and `cachedRunFuel_eq` already relate the cached driver to the
original driver for arbitrary states and arbitrary fuel, preserving complete
`Except`/`Result` values. The original `runFuel_ledger`, `runFuel_heap`,
`runFuel_serial`, `runFuel_leaf_count`, and `runFuel_serial_nodup` also accept
arbitrary starting states with their respective invariants.

No ready-made theorem was found that composes two exact segments into
`runFuel (m+n) st`. At zero fuel with the loop guard still true, the current
driver returns `.failed .exhaustedFuel`; it does not return a successful
checkpoint. `Result.state` forgets the reason, so it cannot by itself justify
resuming and recovering a complete `Result` equality. Totals, leaf counts,
and heap sizes alone do not bind the seven-field `DriverState`.

The abstract ledger's `Run.next`, unrelated cap-plan `run_append`, and old
source-only trace extension do not supply this missing concrete-driver
composition theorem. They are not added to the present closure.

The original A → B → W route and its unchanged strict and independent-audit
gates therefore remain the execution plan. This inventory is retained to
avoid repeating searches if an observed failure later makes an adapter
necessary.
