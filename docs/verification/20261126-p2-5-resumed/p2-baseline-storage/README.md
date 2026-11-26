# P2 empty-baseline document storage recovery

This package prepares a storage-only continuation of the existing round4-v3
exact sparse-worktree workflow. It grants no Lean, owned-audit, finite-certificate,
or P2.5 proof credit. No cloud mutation or compilation was performed while
preparing it.

## Fixed scope

The sole editable worktree is this task's isolated empty baseline:
`/workspace/p25-analytic-baseline-8657-20261125`, fixed at commit
`8657cfffef159185f73c6a04ae4d31c846c0d0a9` and tree
`d48c5f773a7fc213e4da7897d3a4a042016a151e`.

Only ordinary tracked files under `docs/evidence/owned-frontiers/` with suffix
`.raw`, `.gz`, `.json`, `.txt`, or `.nul` can qualify. Each must match its exact
HEAD/index blob and an independently read, locally available Git blob. Hardlinks
are excluded. Only their materialized worktree copies are omitted through Git's
exact non-cone sparse rules; the original blobs and index entries remain.

The adapter preserves all Lean files, Python validation scripts, cache objects,
`.lake`, symlinks and their targets, untracked and ignored files, and every other
baseline file. It also protects references collected from the P2 receipt JSON
files, external snapshot, and registered worktree symlinks, including ignored
and untracked sibling symlinks discovered by metadata-only traversal without
following directories that are symlinks. It never expands to
another prefix or worktree.

The P2 proof root remains at commit
`7926999deb30b63976739355b3076990b370e66f` and tree
`1c499b283fd6fa2ae83c8d66d0b2e1ea9e934099`. The complete proof-root file inventory,
including all sources, `.lake`, cached objects, and historical receipts, must
remain identical. All Git objects, refs, registrations, common configuration,
and other worktrees' recorded state must remain identical. Only the baseline's
private index skip-worktree representation and its three sparse configuration
settings may change. The old compilation and audit drivers are not edited.

## Reused checks and independent identities

The adapter loads the existing round4-v3 helper only after verifying SHA256
`23260e963c3cb4c28e8895e6a2c462afd7fc795e848d5271df2ef83b098eb04e`.
It reuses stable inventories, symlink resolution, Git-state and staged-tree
inspection, and JSON reference collection. Its Git commands prohibit transport
and lazy object fetching. The original round4-v3 main is never executed.

The round7 helper is read from the locally present published Git blob at commit
`1e80a5fa2fa2dbb346dbdef5760a7361a8001a46`, verified against SHA256
`7599eb65dd43cf83d9664a719216f546be3b0c7c91100a42ae30de3c7174b8a0`.
Its prior-round validator checks the actual round6 result. The adapter reads the
original P2 `.lake/p25-followup-repairs-attempt006/RUN_RESULT.json`, requiring
SHA256 `9fe39608896832b25314f258da68615b8a1a98f6c63a184bb2359122f67f7bf7`.
It does not substitute the local stdout-derived result.

Round2/4/5/6 graph reconstruction, the 377-module/69-owner scope, current 339
successful normal records and 45 accepted owned records, saved targets/selection,
source/gate pins, accepted audit artifacts, and qualified external snapshot are
validated. The original `baseline_checks()` runs during preflight, immediately
before mutation, and after mutation. Round7 attempt007 must still be absent.

## Capacity and execution

The **128 MiB** (`134217728` bytes) minimum conservative reclaim is this storage
plan's target. The unchanged original proof-space gate is **1 GiB**
(`1073741824` bytes). Neither target changes a theorem or proof-acceptance gate.
The plan also reserves 16 MiB for evidence writes and 16 MiB for subsequent
preparation. Allocated bytes are measured from actual single-link files using
`st_blocks * 512`; this is an allocation estimate and does not assert that an
overlay or reflink filesystem will actually release those bytes. The final
free-space check decides whether the unchanged proof-space gate is satisfied.
No historical capacity estimate is treated as live evidence. The baseline and
P2 proof root must share the same filesystem.

Run the read-only plan first, using the exact runner SHA in `RUN_CONFIG.json`.
Plan mode writes diagnostics outside all registered worktrees and does not
change their files, Git configuration, indexes, or refs. If the single prefix
cannot conservatively reclaim 128 MiB, it stops without enlarging scope.

Apply requires both the exact read-only `PLAN.json` path and its SHA256. It
also reads the adjacent `RESULT.json` and requires a completed
`READ_ONLY_PLAN_VERIFIED` status, no requested or started mutation, and matching
runner and plan hashes. It
regenerates the current plan and demands exact equality of source/context,
worktree inventories, Git state, candidates and rules. Any change requires a new
plan. After sparse omission it verifies the complete preservation conditions and
the unchanged proof-space gate plus preparation reserve. On failure it retains
all evidence and does not broaden scope or perform automatic cleanup.

`RUN_CONFIG.json` contains exact command templates. Its apply placeholder must
be replaced by the SHA of the actual successful cloud read-only plan; this
package has no such plan or recovery receipt yet.

## Local validation

`LOCAL_VALIDATION.json` binds the tested runner, test source and complete test
output. Three isolated real-Git checks passed: exact literal sparse exclusion
with source/symlink/untracked/object preservation; rejection of changed worktree
bytes; and rejection of a missing local blob. A fourth targeted check validates
the prior successful-plan receipt condition, including failed status and wrong
plan hash rejection. The fixtures are disposable
temporary repositories and do not use the P2 cloud worktrees. The full cloud
identity/capacity preflight remains to be executed by the owning thread.
