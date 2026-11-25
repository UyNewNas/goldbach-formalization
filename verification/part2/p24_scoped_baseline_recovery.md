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
tree and `.git` administration are independent. Git storage is inspected and
reported as either exact read-only baseline alternates or independent local
Git object files; the requested clone flags do not establish which layout was
actually produced. The alternates case retains its baseline object dependency.
Tracked trees up to
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

## Actual completed cleanup and pre-checkout continuation

The first real recovery removed 477 qualifying duplicate files, totalling
1,242,067,938 bytes, and reported 1,651,740,672 free bytes. The registry SHA-256
remained `b77b0170e12aec6949b2afb12b8867af41f8a7c99e44791237ba1b2d0cff075e`;
the migration receipt remained
`2d969f9536b0e9faad5436050ff708aaee4e684b2ce94fb35e68bdda218288b4`.
The successful recovery receipt is
`5b47b70bcf6e49e0565951185196c440dbb10a28fe6e6c0adc9752a002be750a`.

The subsequent Git clone completed, but the first preparation implementation
incorrectly required `.git/objects/info/alternates` to exist. The resulting
`FileNotFoundError` occurred before checkout or any Lean artifact copy; the
original strict checker was not started. This was an unnecessary storage-layout
assumption in the preparation tool, not an original verifier condition.

The actual read-only inventory is
`docs/source-only/20261125-p24-original-compact/p2-mirror-inventory-01.log`,
SHA-256 `04198664ef7f53cbfb9afa685a03bf4fe38c1d7b84278176ff57c7bed6a5b790`.
It shows the same pinned HEAD, original baseline origin, independent `.git`
and object root, and only `.git` at the mirror's top level. Its Git object
database contains one pack of 22,444 objects: a 316,907,156-byte `.pack`,
629,504-byte `.idx`, and 89,828-byte `.rev`, all regular single-link files.
There are no alternates. The original baseline instead has ten packs. The
inventory therefore supports reusing the existing independently packed clone.
The reason Git selected that storage layout has not been established; an
isolated Git 2.56.1 comparison produced alternates for both ordinary and linked
worktree sources, so the version or source-worktree distinction alone does not
explain the real run.

For this actual attempt, cleanup is complete: do not run `--apply` again and
do not delete or re-clone the mirror. After the caller refreshes the owned
branch, use **`--prepare-mirror --resume-clone --lock-fd 9`** against the same
attempt. The explicit resume mode requires the precise pre-checkout state:
only an independent `.git`, no index or working-tree/facet files, the pinned
HEAD and matching baseline tree, the original baseline origin, and no worktree
or sparse overrides. Git path/object/index/namespace environment redirection
is rejected. Git administration and object files must remain within the owned
clone, regular and single-link, with no symlink ancestors. An existing
alternates file must identify exactly the baseline object root; its absence is
accepted when the clone has its own local object files. These checks do not add
a full-history audit or a new proof-acceptance gate.

`--resume-clone` is accepted only with `--prepare-mirror`. It skips both cleanup
and clone and continues through the original checkout, scoped facet copies,
and postchecks. The default mode continues to reject an existing mirror.
Runtime evidence records the actual storage kind and whether the clone was
resumed; the successful recovery receipt and proof records remain unchanged.

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
Only the explicitly verified pre-checkout interruption above is resumable.

## Validation and frozen review

From the repository root:

```sh
python3 -B -m unittest discover -s verification/part2 -p 'test_p24_recover_scoped_baseline.py' -v
```

All 25 current local filesystem/Git fixtures passed. The original 21 include in-memory `python -c`
execution, zero evidence writes before freeing a copy, all preservation classes,
changed inputs, inode replacement, interrupted cleanup, canonical registry
aliases, runtime source updates between phases, inherited lock identity, clean
full/sparse mirrors, unchanged original baseline files, and independent Lean
artifact copies. Four targeted continuation tests cover independent packed
clone reuse without any clone call, default refusal of existing directories,
rejection of other interrupted states, and Git environment redirection. They
also verify unchanged Git pack inodes/bytes and unchanged registry, migration,
and recovery receipts across successful continuation. No Lean or remote job
ran for these fixtures.

Independent read-only review by `p24_stage_closure` reproduced one original
noncanonical registry-alias omission, confirmed its minimal repair with a
permanent regression and an independent temporary counterexample, and reran
all original 21 tests. That review was READY within the stated single-writer
deployment boundary. The later real clone-layout failure and its explicit
continuation repair are recorded above. For the current frozen continuation
repair, the reviewer independently reran all 25 tests and two additional
counterexamples: a hardlinked `.git/config` and a dangling index symlink. Both
were rejected without changing the proof/recovery records or creating a
working tree. Current review: READY, with no Critical/Important findings. This
is static review plus local Git/filesystem testing; the revised helper has not
yet demonstrated a successful actual P2 continuation or strict compilation.

Frozen implementation SHA-256:
`a1e7bb6d96248c2f014aa4e862b7182eee955c9fb1b9072bd41402d521c76634`.
Frozen fixture SHA-256:
`e07da33417ca506dd0a6a30191154ca50e20b3529313fe27d50947153723824e`.
