# Cell00 continuation with shared accepted dependency storage

The existing v6 proof plan is unchanged: reuse 41 accepted project imports,
then check OriginalParse, OriginalFloors, OriginalArithmetic and
OriginalSourceFacts with normal Lean compilation, independent kernel replay,
and the complete owned-declaration audit. All source and historical receipt
identities, the external snapshot, compiler flags and postflight checks remain.

## Observed resource failure and adjustment

P3 storage recovery v2, task `4731a36a0ec14dc38c38a5b134f2380f`, stopped
before mutation. It observed 349,622,272 available bytes, and the eligible
Git-backed working copies could not reach the former one-GiB startup reserve.
No source, cache, old evidence or working copy was removed by that attempt.

The v7 driver replaces only the two accepted-dependency byte-copy operations
with same-filesystem hard links. Dependencies cannot be any of the four fresh
compiler output targets. Existing destinations and symbolic source paths are
rejected. Every original and linked dependency remains bound to its accepted
SHA256 and is rechecked by the existing frozen-input postflight. The original
v6 driver is itself verified against its published Git blob.

The startup reserve is now 320 MiB: the unchanged 256-MiB per-stage reserve
plus a 64-MiB allowance for new source, audit and receipt metadata. Existing
dependency payload size is still measured and reported, but it is no longer
charged as newly allocated file data. Space checks run before fresh staging,
before linking, and before every Lean/replay/audit stage. A later space loss
still produces a failed attempt, never an accepted proof. No automatic
cross-filesystem copy fallback or deletion is allowed.

This is an execution-resource estimate, not a mathematical assumption.
The fresh result is `attempt007`; prior unsuccessful attempts remain intact.

## Verification before submission

- Three real-filesystem regression tests first failed because the new driver
  did not exist, then passed: identical bytes without a second data allocation,
  preservation of an existing destination, and rejection of a symbolic source.
- The existing v6 regression suite was also run against v7: 42 of 46 passed.
  Four expected incompatibilities are retained in the report: three old tests
  demand the former `copy_dependency` AST verbatim, and one demands the former
  `copying` status string. They detect the intentional resource change; the
  old test files have not been edited or relabeled as passing.
- Actual Lean compilation remains pending at this source checkpoint.

## Completion boundary

Even a successful four-owner result proves only the original Cell00 decoder,
eight simplex arithmetic checks and its Q96 subtotal. It does not prove the
96-row geometric guards, all fourteen cells, the aggregate Saving16 endpoint,
or the same-policy signed distribution input. `P2_5_proved` remains false.
