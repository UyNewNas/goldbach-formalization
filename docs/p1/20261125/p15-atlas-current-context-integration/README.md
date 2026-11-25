# Existing proofs in the current P1 environment

This directory defines two bounded object-integration groups for the existing
`/workspace/blue-member-build` project. It reuses accepted proof source bytes and
the unchanged Batch13 normal compilation, named kernel replay, and complete
environment-owned declaration audit. It does not develop new mathematical proofs
or invalidate the historical acceptance of those sources.

The runner has not been executed in the cloud by this implementation task.
Manifest and Python checks are not Lean acceptance.

## Fixed scope

| Group | Manifest | Complete project source graph | Permitted target objects | Preserved existing dependency objects |
|---|---|---:|---:|---:|
| `atlas10` | `ATLAS10_MANIFEST.json` | 68 | 10 | 58 |
| `p3-20` | `P3_20_MANIFEST.json` | 77 | 20 | 57 |

No arbitrary group, project, or module is accepted. Every invocation verifies the
complete source graph of its group, including unselected target sources. The
manifests bind every source path, byte count, SHA256, Git blob, and import list.
The runner additionally verifies the actual committed bytes and installed graph.

The Atlas source graph is the exact 68-module subclosure of the Phase2
`SOURCE_CLOSURE.json` frozen in commit
`e1a80f6c306b58eadf2a8c6f58f4cbc7385e32d5`, SHA256
`1ae86f80754a3a72fa6250e75afd8f5f97bba1b4c6c5f704dcb0f3b8b2aa5e09`.
Nine target sources are the exact accepted postimages recorded by
`p15-existing-atlas-dependencies/ADOPTION_MANIFEST.json`; the tenth is the existing
`P5SmoothChartHBDyadicPartition` source. Source installation and adoption must
already have completed. This runner contains no source installer.

The P3 graph is the exact 77-module closure in the unchanged Phase1 `P3_REUSE.json`,
SHA256 `1aab54f7655ca68ae24294d49eff3c1f08455d3c31982c78d1e017888bc1316b`.
The 20 targets are precisely its 19 canonical additions plus
`ImbalancedChen.Part3LongSlotDistribution`. All source bytes remain bound to that
original source identity. The historical accepted object hashes in `P3_REUSE`
remain unchanged; they are not treated as expected hashes of newly compiled P1
objects.

Source anchors and historical evidence are read from their fixed published
commit. A later source commit may contain an unrelated Phase2 update, but all
68/77 selected source bytes must still equal these frozen identities. The
executed runner and its fixed manifest must exactly equal the supplied source
commit.

## Why current-context integration is needed

The retained P1 query `job_c2cd8be0074c42d4a623cc17ea8e13c0` completed successfully
without compilation or cache copying. For
`ImbalancedChen.P5SmoothChartHBDyadicPartition`, it computed current depHash
`7739e871e8c291ab`, while the donor's real trace records `d89835432a988a64`.
All seven differing parent `.olean.hash` values also differ. The query's source,
object, trace, and sidecar snapshot was unchanged, with no Built or Failed
modules. The Atlas manifest retains the query identity, saved-observation hash,
bounded command-log binding, and seven exact sidecar comparisons.

The prior donor/receiver observation found 10 absent target objects and 58
existing dependencies: 51 objects matched the donor byte for byte and seven did
not. The runner preserves all 58 receiver identities, including those seven.
It does not replace receiver parents, rewrite donor traces, or claim donor cache
compatibility after the observed depHash mismatch.

For P3, the saved receiver inventory contains 77 modules, with precisely 20
missing objects and 57 existing objects. Five inspected real P3 traces explicitly
record `Module.leanArgs: #[]`; the fixed current P1 configuration uses
`-DmaxRecDepth=100000` and `-DmaxHeartbeats=4000000`. Stock Lake includes these
arguments in its dependency hash. The earlier five-pair ModuleData equivalence
witness has its own preserved scope; it is not a current P1 stock-readiness
receipt or authorization to modify the old traces.

The manifests retain hashes of the already saved observations. This
implementation performs no new remote inventory or historical-source scan.

## Execution and refusal rules

The runner loads exactly the previously published Batch13 API:

- API commit: `4cea0407c1258eaddd7d4952cffa4aea67310422`.
- API SHA256: `95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea`.
- Helper commit: `220c14630ffd266f824bdbf0977147ecb740c0dd`.
- Runtime review SHA256: `34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880`.

`helpers` and `run_owner` are unchanged from the Phase1 runner with SHA256
`f260f575ed6f8a7998fd901d42f0f1cd87115c879c0dc3b2c10f04a7f9b35313`.
The old retained-history, normal-receipt, and partial-audit holds remain in force.
The API still requires every fresh normal compilation to report exactly the one
requested owner as Built and to preserve its dependency context.

Each group uses the existing lane-0 serializer and guard, with its existing
resource policy, runtime state, configuration, and full-owned audit template.
The four protected original P1 roots remain bound to the helper's original
hashes. No flags, package configuration, guards, or resource limits are changed.

The additional integration gates are:

1. Check the complete committed and installed 68/77-source graph and the
   historical source anchor. Match every existing dependency `.olean` and
   `.trace` against the saved receiver fingerprints. Where the retained P3
   observation also binds `.ilean` and absent private/server parts, enforce those
   bindings too.
2. Snapshot all observed companion artifacts for all 58/57 preserved dependencies,
   including hash sidecars, private/server parts, IR, generated C, and setup data
   when present. Require this snapshot, every project source, runtime, and
   configuration to remain unchanged throughout the run.
3. A target without this group's current-commit `NORMAL_PASS.json` must have no
   existing object or companion artifact at any enumerated target path. Unknown
   objects, stale outputs, dangling output symlinks, or incomplete provenance cause
   a hold. They are never deleted or overwritten to enable a retry.
4. A retained normal receipt must pass the original `normal_valid` against its
   actual current source, outputs, dependency context, command, and log. An
   unselected target needed as a dependency must also already have complete,
   valid full-owned acceptance under the same group and source commit.
5. Before each selected target, perform guarded stock `lake --no-build build`
   for its exact committed direct imports, including external imports such as
   `Mathlib`. Require exit zero and empty Built/Failed sets. An empty or unknown
   import set holds; no bare default-target command is issued. The unchanged
   `normal_one` then performs its own direct-project-dependency check.
6. Call the unchanged `run_owner`, `normal_one`, and `audit`. All other target
   artifacts and all preserved dependencies must remain unchanged. An unknown
   failure stops this run and retains its partial evidence for inspection.
7. After successful selected-owner acceptance, perform a final guarded stock
   `--no-build` check for those targets. Require no builds, no failures, and
   unchanged target/dependency artifacts and sources.

The runner never imports donor objects, creates synthetic traces, changes the
original Phase1/Phase2 strict runners, or edits immutable `P3_REUSE` pins. New
target artifacts and their real Lake traces may be produced only by the selected
normal compilation. Reusing new P1 integration receipts in a later owner driver
requires an explicit receipt-selection step; this runner does not silently change
that driver's historical object-selection contract.

## Commands after publication and source installation

Run from the published `/workspace/goldbach-formalization` checkout. Replace
`FULL_PUBLISHED_COMMIT_SHA` with the full commit containing this exact runner and
its two manifests.

```bash
python3 -B docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py \
  --source-commit FULL_PUBLISHED_COMMIT_SHA --group atlas10 --check

python3 -B docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py \
  --source-commit FULL_PUBLISHED_COMMIT_SHA --group atlas10 --run

python3 -B docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py \
  --source-commit FULL_PUBLISHED_COMMIT_SHA --group p3-20 --check

python3 -B docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py \
  --source-commit FULL_PUBLISHED_COMMIT_SHA --group p3-20 --run
```

Omitting `--targets` selects the group's complete fixed target list. An explicit
subset is allowed only within that list; any target dependencies excluded from
the subset must already have this entry point's complete current-commit
acceptance. `--check` performs source/runtime/object/provenance checks only and
does not claim stock readiness or fresh acceptance.

Evidence is written beneath:

```text
/workspace/p1-complete-proof/20261125-p15-current-context-integration-v1/
  atlas10/<source-commit>/
  p3-20/<source-commit>/
```

The API's original per-owner normal and full-owned evidence remains intact.
`RESULT.json` additionally identifies the acceptance class as
`CURRENT_P1_ENVIRONMENT_INTEGRATION_OF_EXISTING_PROOF_SOURCES`, binds current
normal/audit receipts and target artifacts, and records that zero new mathematical
proofs were developed. A successful group is not a claim that all of P1 or P1.5
is complete.
