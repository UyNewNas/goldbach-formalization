# P0 resume: one control branch and bounded verification

The owner resumed hourly P0–P5 work on 15 October. The authoritative branch is
`codex/chen-parts-integration`, continuing `1337e2db4712fb4a9f86add073f771f84b66d0c8`.
The separate `chatgpt/chen-p0-integration` branch is a supplier, not a replacement
for the 17-module checkpoint. Its common ancestor is `59d338b93b2347021237eb51293bb934a316909d`.
No main branch merge, dependency upgrade or root-import change is made here.

The checkpoint identity verifier passed for 110 files and 17 compiled modules.
This was a static archive check, not a new Lean execution. The full P2 checkpoint
already contains 17,572 rows and 186 strip checks; rebuilding the first 192 rows
would lose progress. Full global sums and integral acceptance remain separate.

The actual checkpoint core run [38374498943](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38374498943)
passed root build, root replay, root axiom audit and Round3/4 exports, then failed
Round6 in 17 seconds with `lean::memory_exception`. The later legacy branch's
Round6 success uses a different runner without `-M4096`, a fixed census, and no
serialized/partial checks. It does not replace this stronger pending gate.
The legacy P4 strict source stage also failed at `-t0 -M4096` in
[38475602072](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38475602072).
No identical full-root retry is scheduled.

## This round's next finite requests

1. P1's actual seven-gate historical frontier dictionary. It retains both
   inherited first-cube tests when the third level is below the initial level.
2. P3's repaired ordinary-BV current-lower leaf, keeping all declaration headers
   and the ordinary distribution range unchanged.

Both new sources are SOURCE_ONLY until their exact objects receive successful
strict compilation, native replay, full serialized defining-module/type/axiom
inventory (including private/generated declarations and partial exclusion), and
audit replay. The queue runner retains every failed stage and all imported
source/object companion hashes. The allowed axioms remain `propext`,
`Classical.choice`, and `Quot.sound`.

The finite workflow restores only the cache of the exact prior successful
`59d338b...` root, checks pins and source changes, compiles changed project
prerequisites serially, and never installs new dependencies or rebuilds the full
library. Cache misses are explicit blockers. Reused imported objects are not
reported as newly rebuilt/replayed proof closure.

P0 alone triggers proof-environment work. Status/source publications use
`[skip ci]`. A selected `automation/dispatch.json` change schedules one finite push
job; automatic duplicate core/VE PR jobs on the controlled branch are suppressed.
The full core/VE push workflows and all their internal required gates remain
available for P0's later complete-root acceptance; skipped jobs are not evidence.
All three workflows share one non-cancelling heavy-run concurrency group.
Local process locks are shared across worktrees and inherited by child processes.

Neither `hLower` nor `hUpper` is discharged. The manuscript pin, fixed `currentC`
and `currentK`, quantifier order and final completion criteria are unchanged.

The first PR-only dispatch created no job because PR #4 conflicts with its
base. No merge was performed. The bounded queue now uses its own branch push
event; exact cache availability in that scope is an explicit prerequisite.

Compiler commands retain `-t0 -j2 -M4096`. The bundled checker does not implement
`-M`; its native invocation is recorded as such, with the shared single slot and
`LEAN_NUM_THREADS=2`. No new operating-system hard memory limit is introduced.

## First finite run and revised dependency plan

[Run 38663797841](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38663797841)
on exact commit `10d8627719ff2d303ca67f0f1c32c6f7b29de299` installed the pinned
toolchain successfully, then stopped at an exact-cache miss. Both proof requests
were skipped. This is a terminal setup failure, not a mathematical failure or PASS.
The retained baseline artifact 11790907699 was inspected: its 74 files contain
only Round3/4 audit objects, not the production/import object closure needed here.

The changed plan starts from all eleven fixed dependency source commits, uses
the official Mathlib source-hash cache only for the two targets' actual import
boundaries, and compiles only required project/Goldbach source closures serially.
It does not upgrade pins, restore arbitrary old project caches, or build the whole
root. Fresh objects are marked newly compiled and fingerprinted, never relabelled
as the old accepted cache. Same-job reuse binds source, direct dependency objects,
toolchain, pins and command policy. Strict target/replay/full audit gates remain.

A proposed cross-branch reconciliation was not performed; the integration branch
retains its current ancestry and the other supplier branch remains separate.
