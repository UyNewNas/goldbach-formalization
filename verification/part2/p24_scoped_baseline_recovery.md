# P2.4 scoped baseline recovery after ENOSPC

## Observed problem and unchanged verification boundary

`docs/source-only/20261125-p24-original-compact/p2-cache-migration-01.log`
(SHA-256 `a30b26437ba64665b8f135b2a8135856ff025b7b04159545ad8f6c172048e72f`)
records successful transport of 69 previously verified records in the 322-module
scope. The subsequent original checker failed with `Errno 28` while copying the
unrelated `ImbalancedChen/P2Winner9CompleteSeedBlock26.olean.hash`. Its baseline
copy loop runs before the requested project closure is selected and even with
a zero compilation time budget.

The original checker accepts a baseline path whose HEAD is exactly
`8657cfffef159185f73c6a04ae4d31c846c0d0a9` and whose tracked tree is clean.
Its records bind that commit, target object paths, sources, and dependencies;
they do not bind the absolute baseline path. With the qualified external
snapshot supplied, `ExternalSnapshot.environment` replaces `LEAN_PATH` with
the existing target private library followed by the snapshot's original roots.
Changing only `--baseline-root` therefore leaves the 69 migrated external
bindings intact. The checker, audit, qualification gates, and existing records
are not modified by this recovery tool.

## Narrow implementation

`p24_recover_scoped_baseline.py` defaults to a read-only plan on stdout.
`--apply` removes only regular, single-link project artifacts that are outside
the complete current whole-endpoint closure and the migration receipt's
original scope, unprotected by any direct `*records.json` registry, known to the
pinned baseline's tracked source inventory, and byte-identical to the baseline
artifact at the same relative library path. Target and baseline ancestors must
not be symlinks. Registry object references are resolved before protecting the
physical module and all its facets, including references containing `..`.
Unknown files, changed or partial copies, symlinks, multiple links, protected
modules, and original baseline/donor files are preserved.

All planned copies are rechecked before any deletion; each copy and the bound
registry/receipt inputs are checked again immediately before its unlink. The
first qualifying unlink precedes every output-directory or evidence-file
creation. Python bytecode writes are disabled. Read-only Git calls disable
optional locks, lazy fetching, and transport. The tool opens the existing
migration lock without creating or truncating it. Thus the complete reviewed
source can run through `python3 -B -c` while the filesystem has no free space.
It prints a small plan summary first, and writes the full deletion receipt only
after space is released. An interrupted cleanup records only actual deletions;
it cannot publish a successful mirror receipt.

`--prepare-mirror` is a separate, mutually exclusive mode, used after the caller
fetches and fast-forwards the owned branch. It rechecks the published migration
reference and recovery receipt, then recomputes the current source closure.
The mirror uses `git clone --shared --no-hardlinks --no-checkout`: its working
tree and `.git` administration are independent, while Git objects are borrowed
read-only from the original baseline via a recorded, checked alternates path.
It is not a self-contained duplicate Git object database. Tracked trees up to
64 MiB receive a full checkout; larger trees receive a tracked-clean sparse
checkout of required baseline sources and build metadata. HEAD remains the
exact pinned commit in both modes.

Only existing loadable facets for the current closure are copied into the
mirror library. These are independent regular files, never symlinks or
hardlinks to shared objects. The tool accounts for checkout bytes, mirror
facets, subsequent missing checker copies, and a 256 MiB free-space reserve.
This reserve is a preparation check, not a guarantee of all future build space.
No source compiler, kernel checker, native qualification, or cache-credit
operation is performed by the recovery tool.

## Stable CLI and caller sequence

Both modes accept these common arguments:

```text
--project-root /workspace/p2-4-compact-proof-20261125
--baseline-root /workspace/goldbach-p2
--donor-root /workspace/p2-private-20261124
--external-snapshot /workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json
--attempt attempt-001
--lock-fd 9
```

The caller opens the existing `.lake/p2-private/p24-migration.lock` on descriptor
9 and holds its exclusive lock across the following entire sequence:

1. Inject the exact reviewed script as the `python3 -B -c` argument and pass
   `--apply`. No temporary script or plan file is needed on the full disk.
2. Confirm tracked cleanliness, fetch only
   `work/p2-4-compact-proof-20261125`, fast-forward that owned branch, and confirm
   the actual HEAD equals the fetched HEAD.
3. Run the same reviewed script with `--prepare-mirror` and the same descriptor.
4. Invoke the unchanged strict checker with the caller's requested roots and
   resource limits, the original qualified external snapshot, and the mirror
   path below as `--baseline-root`.

The tool contains no internal fetch, merge, checker, audit, or resource-budget
orchestration. Without `--lock-fd`, each invocation separately locks the same
existing lock; continuous caller-held locking is the reviewed deployment mode.
The lock is cooperative and the task checkout must have a single writer. The
file checks do not claim an atomic compare-and-unlink operation against an
uncooperative concurrent writer.

Successful output paths are:

```text
.lake/p24-disk-recovery/attempt-001/RECOVERY.json
.lake/p24-disk-recovery/attempt-001/RUNTIME_SOURCE.json
.lake/p24-disk-recovery/attempt-001/BASELINE_MIRROR.json
.lake/p24-baseline-8657/attempt-001
```

`RUNTIME_SOURCE.json` records the actual source HEAD used for mirror selection.
The whole-endpoint closure is a safe protection/mirror superset; only the roots
passed by the caller determine what the original checker compiles. Partial
mirror directories are preserved on failure and are never silently overwritten.

## Validation and frozen review

From the repository root:

```sh
python3 -B -m unittest discover -s verification/part2 -p 'test_p24_recover_scoped_baseline.py' -v
```

All 21 local filesystem/Git fixtures passed. They include in-memory `python -c`
execution, zero evidence writes before freeing a copy, all preservation classes,
changed inputs, inode replacement, interrupted cleanup, canonical registry
aliases, runtime source updates between phases, inherited lock identity, clean
full/sparse mirrors, unchanged original baseline files, and independent Lean
artifact copies. No Lean or remote job ran for these fixtures.

Independent read-only review by `p24_stage_closure` reproduced one original
noncanonical registry-alias omission, confirmed its minimal repair with a
permanent regression and an independent temporary counterexample, and reran
all 21 tests. Final review: READY; no remaining Critical/Important findings
within the stated single-writer deployment boundary.

Frozen implementation SHA-256:
`f0129364cff3096f527c134f65ee5c591f8afe1dda572d7737b9dedde296bede`.
Frozen fixture SHA-256:
`188b935a085b8d4cb121ebe1bfbda79f671fd2a57220abb8f6b0c246c1087a84`.
