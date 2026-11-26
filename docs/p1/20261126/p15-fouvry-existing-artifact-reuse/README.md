# Existing Fouvry artifacts: fixed receiver compatibility check

This directory prepares a diagnostic for the five existing native `goldbach`
artifacts needed by the P1 P3 integration. It contains no proof implementation,
source installer, artifact transfer, trace editor, or acceptance runner.

The first actual receiver query attempt returned **HOLD**. Its read-only
namespace probe passed, but the first stock dependency-hash query returned no
hash. The remaining frontier comparisons and CompleteWeil readiness remain
unresolved; no cache adoption or Lean acceptance follows.

## Actual receiver observation — 2026-11-26

[ACTUAL_RECEIVER_OBSERVATION.json](ACTUAL_RECEIVER_OBSERVATION.json) preserves
the bounded stdout summary and collection metadata for
`job_83042a34ac5d43b3b1303c1046ac680c`, source commit
`fd9634e90aad5a537337457e33cb538a1187038a`. The job exited 3 after 5.145 seconds;
its bounded output was fully collected without truncation. The original
4765-byte collected JSON has SHA256
`088d52bb003ddfb91d05c8b9e68f2aec353fa3de4ffaea09a63de397f0712516`.
Its fields are retained unchanged; the observation also records the subsequent
fixed short-log read below.

- The existing `bwrap` probe exited zero. It verified all 14 protected paths
  were read-only and all writable mounts stayed inside the owned attempt.
- The first frontier, `LiLiuPrereqFouvryCompletion`, had stock query exit code
  134, empty `Built`/`Failed` module lists, and no receiver `depHash`. Its donor
  hash therefore has neither a confirmed match nor a confirmed mismatch.
  StepanovHasse, StepanovNonzero and HarcosPowerSum were not queried.
- The three direct native parents listed below now have observed source bytes
  matching fixed goldbach revision `09b97db5764ade1246bfb77206baa1b124760958`.
  Each parent's `.olean` and `.trace` is absent. Their stock readiness was not
  tested.
- The fixed source/artifact/configuration/runtime snapshots have identical
  before/after SHA256
  `22071b9bdea67a1a5b24da6105f4e91d50f879128c85083e41252b08fec37cf3`.
  Repository Git metadata and frozen diagnostic inputs were also unchanged.

The fixed 130-byte error log reports **permission denied (error code 13) for
`/dev/urandom`** while the Lake query reads that path. Its SHA256 is
`77de51b46a9bab1b1c8fd81376652413f006e42ea43fd1f394ac435bd332c136`.
The separate bounded read, `job_50ac0556bea64b979d61125614c322a6`, succeeded
with exit 0, runtime 0.0488886833190918 seconds, and 388 output bytes through EOF.
The exact two-line diagnostic and collection metadata are retained in the
observation. This establishes the reported access denial only; its underlying
cause is not attributed further. No namespace, guard, checker or fixed binding
was changed, and no query was retried. No proof compilation, cache transfer or
cache adoption was
requested, and no owner was accepted. The full 17607-byte public result remains
in the cloud; the bounded observation retains only that receipt's path, size and
hash. No private audit
inventory or archive was read or exported for this documentation update.

## Restored evidence

All three earlier observations were recovered from local files. Their task
outputs were fully read without truncation. No replacement remote probe was
submitted during restoration.

| Saved observation | Task | SHA256 |
| --- | --- | --- |
| `p1-two-external-readonly-observation.json` | `job_0a5926d761e6400caa6cd37edec7ac6d` | `8eeb7999180865f89a7a447e38e7b51d17d39fde72551386cbad508b89abcb45` |
| `p1-fouvry-frontier-readonly-observation.json` | `job_665af0a251114cbcb9300b4b50a51dbf` | `fbcc42570c6a47e7e5f50c49ea94a59b6a93839ac428aeca25cfba6052bd3e04` |
| `p3-fouvry-frontier-readonly-observation.json` | `c978a52df00846338905263bfe9977b3` | `7f7070713a4cf8ff6765335e88f9840ed3092fc6bfa8392da450427e7037ae90` |

The saved files live in the task's `p15_analysis/resume` scratch directory.
`EVIDENCE_BINDINGS.json` records their byte counts, hashes, task identities,
read-completion receipts, and the relevant public source/artifact identities.
It does not copy private runtime inventories, declaration types, or replay logs.

The original failing P1 integration is
`job_41c06d666c6642889cc27d82ee281eb7`, source commit
`418ad4b9a5f2d992871062258a2eefd7fdf4b9ee`. It accepted
`ImbalancedChen.Part3BrunWeights`; the next owner,
`ImbalancedChen.Part3CompletedReciprocalWeil`, stopped at direct-import stock
readiness, before its normal compilation. This diagnostic never recompiles
BrunWeights or invokes a normal/kernel/full-owned audit.

## Fixed donor and receiver

The donor is the existing P3 package:

```
/workspace/goldbach-p3/.lake/packages/goldbach
```

The receiver remains:

```
/workspace/blue-member-build/.lake/packages/goldbach
```

For every module below, the source path is the package directory followed by
`MathlibNt/AnalyticNumberTheory/LargeSieve/<name>.lean`; the object and trace paths
are `.lake/build/lib/lean/MathlibNt/AnalyticNumberTheory/LargeSieve/<name>.olean`
and `<name>.trace` below that same package directory.

| Module name | Existing P3 `.olean` SHA256 | Original real-trace `depHash` |
| --- | --- | --- |
| `LiLiuPrereqFouvryCompletion` | `09e0fd8e30ecdcd52b69561357f73634b17e3dec498e02b29786197b17ca0686` | `518df5326da5a557` |
| `LiLiuPrereqFouvryStepanovHasse` | `1553a443a11240ee9787c12caabba576c9977d2327624c2c82f2847e46f2e296` | `fb9e3de88be5495a` |
| `LiLiuPrereqFouvryStepanovNonzero` | `f4d4b2e12a8f59c1f95d75307ff1d1edebd3b23fc2c1f60bae2c64349319d07f` | `d0194d43efb13a1b` |
| `LiLiuPrereqFouvryHarcosPowerSum` | `88025f1b927501e807566ef29f488f9adb4a391849d655b8c6a86bcf9eafc4d4` | `77f309b3830d4a18` |
| `LiLiuPrereqFouvryCompleteWeil` | `664550a19839324a39d009bdd3f6b0f82849b78f2b40a0a6d74074211b2d017e` | `1fd42a4969ab5be7` |

The retained observations found identical P1/P3 source bytes for all five.
Each donor has `.olean`, `.ilean`, `.c`, genuine hash sidecars, and a real Lake
trace. The traces record `m=false`; the inspected `.olean.private`,
`.olean.server`, and `.ir` files are absent. Full paths and SHA256 identities,
including the trace and companion outputs, are in `EVIDENCE_BINDINGS.json`.
These are identities of existing artifacts, not new independent kernel audits.

Both native packages have identical source configuration:

- `lean-toolchain`: `62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef`.
- `lakefile.toml`: `fb01f3330623d8a6aa20e81e86b93da41df1272fd85f5528da6c9631e0e9822f`.
- `lake-manifest.json`: `d360c103a90b63fd6c53650c2cbe0b11fd10d103f248e88ff8352f02fb2ce0ab`.
- `lakefile.lean`: absent.
- Fixed goldbach revision: `09b97db5764ade1246bfb77206baa1b124760958`.
- Fixed mathlib revision: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

The five donor traces identify `Package.id?: (some goldbach)` and
`Module.leanArgs: #[]`. The P1 root package's existing `moreLeanArgs` are not
substituted into this native package's context. The query is run from the
unchanged P1 project, so stock Lake resolves its actual native-package inputs.
Matching configuration alone does not establish matching dependency hashes.

`LiLiuPrereqFouvryArithmeticPoisson` is preserved. Its recorded receiver `.olean`
is `40e152107eeca1d743f8bc9edb826e13014eae42c29a685925f917c1d5a9345a`,
and its `.trace` is
`2ae0fdbbd2bc6d9cb91ee0d46078d6ac37b4a27edb2bc146ebda7903b4504dec`.
The diagnostic checks all of its previously observed companion outputs and
never replaces any of them.

## What the script does

There is no arbitrary module, package, configuration, or cache-root argument.
The scope is fixed to four frontier modules, CompleteWeil, its three direct
native parents, and the preserved ArithmeticPoisson.

Metadata mode checks the six already pinned sources and their literal imports,
the existing project/native configuration, the immutable runtime review, and
the four protected P1 source roots. It fingerprints the fixed nine modules'
source and artifact paths, including missing outputs and possible extra parts.
It reads only bounded public fields from their existing traces.

CompleteWeil's direct native parents are fixed as:

1. `LiLiuPrereqFouvryOddPrimePower`.
2. `LiLiuPrereqFouvryTwoPower`.
3. `LiLiuPrereqFouvryLocalGlobalBridge`.

Their source hashes were not collected by the earlier bounded probes. The
script therefore also tries the three exact Git paths at the fixed goldbach
revision, without fetching anything. If the local Git object is unavailable,
or the installed bytes differ, the source identity remains explicitly
unresolved. Observed working-tree bytes are never promoted to an accepted
source pin. This uncertainty does not fabricate a failure or success for the
independent four frontier queries.

All Git object reads explicitly use `git --no-lazy-fetch`; the inherited helper
environment also sets `GIT_NO_LAZY_FETCH=1` and `GIT_OPTIONAL_LOCKS=0`. A partial
clone therefore cannot silently fetch missing objects and write its object
store. A Git version without the explicit option holds before the checks,
rather than relying on an environment variable it might ignore.

Query mode uses this fixed command for at most four frontiers, stopping when a
mandatory query condition fails:

```
lake --no-build query +MathlibNt.AnalyticNumberTheory.LargeSieve.<fixed-name>:depHash
```

The calculation is stock Lake's `depHash` facet. No replacement hash algorithm
is implemented. The earlier successful P1 use of this API is recorded in
`reindex-current-dephash-query.json`, SHA256
`bdcfe7538a22ce12759f1cb4bdec5ad560df2f8698f094e146a534d5e5c79bff`,
task `job_c2cd8be0074c42d4a623cc17ea8e13c0`.

### Preventing stock cache side effects

`--no-build` is not itself a filesystem write prohibition. In the pinned Lean
4.33 sources, `Lake.Build.Common.fetchFileHash` can create a missing `.hash`,
and `Lake.Build.Module.recBuildLean`/`fetchCore` can restore cached artifacts.
Consequently, this script will not run a bare query in the writable receiver.

It uses `/usr/bin/bwrap` only if that tool is already installed and executable.
It rejects setuid/setgid binaries and file capabilities, records the executable
fingerprint, and neither installs tools nor requests privilege escalation.
The namespace keeps the original absolute paths. All of `/` is read-only;
only this attempt's new evidence directory, including its own `tmp`, is
writable. A private PID namespace and a fresh read-only `/proc` prevent host
process root paths from exposing an alternate writable view. Capabilities are
dropped, and the namespace has no network access.

A small Python probe first checks the actual namespace mount table, verifies
that every writable mount is inside the owned attempt, verifies the protected
paths are read-only, and writes only its own new temporary marker. No existing
project or cache file is used as a write probe. If the installed bwrap/kernel
cannot construct this view, the result is HOLD before Lake is invoked.

The worker is serialized by the unchanged lane 0 serializer. Each namespace
command remains inside the original lane 0 guard, with the same runtime state
and resource policy. No guard, serializer, limit, configuration, or original
trace is changed. The helper is loaded from the published phase1 driver at
`d20acdf13882e17d97833064f5e7c54f3192b03c`, SHA256
`f260f575ed6f8a7998fd901d42f0f1cd87115c879c0dc3b2c10f04a7f9b35313`;
its pinned Batch13/tooling APIs remain unchanged.

If stock Lake tries to fill a missing sidecar or restore an existing cache path,
the read-only view denies the write. The query then holds; there is no fallback
to a writable query, no trace synthesis, and no automatic repair.

## Invocation after review and publication

Use the full commit that publishes this directory. The script verifies its own
bytes and the fixed binding manifest against that commit before it proceeds.

Metadata only:

```bash
python3 -B /workspace/goldbach-formalization/docs/p1/20261126/p15-fouvry-existing-artifact-reuse/check_receiver.py --source-commit <full-published-commit>
```

Metadata and the optional four strictly read-only stock queries:

```bash
python3 -B /workspace/goldbach-formalization/docs/p1/20261126/p15-fouvry-existing-artifact-reuse/check_receiver.py --source-commit <full-published-commit> --query
```

The only new files are this attempt's evidence, query logs, and owned temporary
marker beneath:

```
/workspace/p1-complete-proof/20261126-p15-fouvry-existing-artifact-reuse-v1/<commit>/attempt-NNNNN/
```

The existing serializer uses its existing lock as usual. The script fingerprints
the fixed source/artifact/configuration/runtime inputs before and after, checks
the repository Git metadata and frozen diagnostic inputs, and leaves all
historical attempts untouched.

## Result interpretation

Stdout contains a bounded public summary: hashes, presence flags, source-identity
states, namespace flags, query exit codes, and compatibility results. The full
public fingerprint receipt is `PUBLIC_FINAL_RESULT.json`. Child replay logs
remain in the owned remote evidence directory and are referenced only by their
hash and byte count; no raw log or private declaration type is relayed.

- `METADATA_RECORDED_COMPATIBILITY_UNRESOLVED`: metadata mode completed. No stock
  dependency-hash query was run.
- `FOUR_FRONTIER_DEP_HASHES_MATCH_DONOR`: all four guarded, read-only queries
  exited zero, produced an unambiguous 16-hex hash matching the original donor
  trace, reported no built/failed/restored artifacts, and preserved the fixed
  inputs. This is only the four frontier dependency-hash comparison.
- `FRONTIER_DEP_HASH_MISMATCH`: the four queries completed, and at least one
  actual receiver hash differs. Exact expected/observed hashes are retained;
  nothing is rewritten or recompiled.
- `HOLD`: a mandatory pin, namespace, query, or unchanged-input condition could
  not be established. The public `failure_code` identifies the condition.

Exit 0 means the requested diagnostic completed, including a possible reported
hash mismatch. Exit 3 means HOLD. Neither exit code is Lean acceptance.
The final result is forced to HOLD if the serialized worker does not exit zero,
even if that worker wrote an intermediate success record before exiting.

Every result retains `overall_ready_for_cache_adoption=false` and
`complete_weil_native_parent_stock_readiness=NOT_TESTED`. A four-frontier match
does not establish CompleteWeil's complete native transitive readiness, prove
that five bundles suffice, or authorize a transfer. Any later reuse must retain
the genuine donor trace and all existing valid receiver artifacts and obtain
the remaining actual stock readiness evidence. The immutable `P3_REUSE.json`,
its historical object identities, and all existing P1 acceptance drivers are
unchanged.
