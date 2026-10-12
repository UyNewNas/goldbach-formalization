# GitHub Actions observation: 2026-10-12 04:24:32 UTC

This record freezes a read-only observation of two GitHub Actions runs at
`db97d0fe03250f4d9a8aea34b23e9c20f67010b8`. It is not a live CI status page.
The timestamp is the recorded end of the observation session; requests were
made during that session, and the final core run/jobs/artifact queries
immediately preceded it. No further GitHub queries were made to prepare these
files.

The Part 5 proof baseline remains
`1a80c1bcce67886f699d097fc37fd245cd3620bf`.
Neither this observation nor the historical reference field in the VE report
changes that baseline.

[snapshot.json](snapshot.json) retains the selected API run/job fields, the
actual job step arrays, artifact metadata, all 20 compared source hashes, and
the scope analysis. It does not claim to reproduce every field of the original
run payloads.

## Attempts and observed execution

| Workflow | Attempt 1 | Attempt 2 at this observation |
|---|---|---|
| [Lean core verification, run 38200419493](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38200419493) | Job `114652364056`: failure, runner `0`, no steps; 03:36:31–03:36:33Z. | Job `114657115566`, runner `1000012588`: build in progress since 04:01:47Z; bundled root leanchecker and root axiom audit pending. |
| [Variable envelope verification, run 38200419496](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38200419496) | Job `114652364058`: failure, runner `0`, no steps; 03:36:31–03:36:33Z. | Job `114657112572`, runner `1000012587`: success. The actual verification step ran 04:01:27–04:02:53Z; the job completed at 04:02:57Z. |

Both latest runs report `run_attempt = 2`, the exact head above, and a
`run_started_at` of `2026-10-12T03:59:42Z`.
The API reports `triggering_actor.login = UyNewNas`.
This review did not trigger or rerun either workflow.

The earlier no-runner/no-step reports describe attempt 1. They do not describe
the later attempt 2. An attempt 1 job with no steps supplies no Lean diagnostic.

## Actual VE acceptance and its scope

The completed VE job log and its downloaded artifact record actual builds,
regression checks, eight bundled kernel replays and a transitive axiom audit
of every declaration in the specified modules. The artifact report is
`PASSED`; all 16 recorded stages have exit code 0.

| Module | Inventoried declarations |
|---|---:|
| `ImbalancedChen.VariableEnvelope` | 42 |
| `ImbalancedChen.VariableEnvelopeConsequences` | 30 |
| `ImbalancedChen.VariableEnvelopeRegularity` | 31 |
| `ImbalancedChen.VariableEnvelopeScaled` | 31 |
| `ImbalancedChen.VariableEnvelopeBoxes` | 76 |
| `ImbalancedChen.VariableEnvelopeCertificates` | 74 |
| `verification.VariableEnvelopeBoundary` | 0 |
| `verification.VariableEnvelopeBoxesBoundary` | 74 |
| **Total** | **358** |

The first boundary module still has an actual build and kernel replay; its
declaration count is zero. The declaration inventory's transitive axiom set
is exactly `Classical.choice`, `Quot.sound`, and `propext`.

The actual Lean version printed in the artifact is `4.33.0-rc1), commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`.
The six principal modules are named explicitly by the
[fixed VE verifier](https://github.com/UyNewNas/goldbach-formalization/blob/db97d0fe03250f4d9a8aea34b23e9c20f67010b8/verification/verify_variable_envelope_boxes.py);
the two boundary modules are built separately.
This workflow does not import the project root.

The report limits the mathematical scope to the complete three-variable VE
on `0 <= z <= y <= x <= 25/128`. It does not establish the extended
`x >= mu` expression or full numerical certificates.
Its `base_commit = 7ba701070c5481acf9de1adb4489fd8016e08089` is the VE
runner's historical reference field, not a replacement Part 5 proof baseline.

## Artifact and source identity

[Artifact 11726157267: variable-envelope-38200419496-2](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38200419496/artifacts/11726157267)

- ZIP size: **43,198 bytes**.
- ZIP SHA256: `ff2219405bf98aa1a9402017dd30e236142a58cb55da1852fd41f947a2632f0c`.
- Created: `2026-10-12T04:02:54Z`.
- Scheduled expiry reported by GitHub: `2026-11-11T04:02:53Z`.
- The artifact was not expired at observation.
- The downloaded ZIP digest matched the API digest.
- All **20** source hashes in its report independently matched the bytes at
  the fixed head; there were no mismatches.
- The report's checked-out head matched the fixed head and its working-tree
  status was empty.

The ZIP contains 27 log, report, declaration-inventory and theorem-type files.
Its entry list is retained in the JSON record. It contains no `.olean`,
`.ilean`, `.o`, `.a` or `.so` files and no Lake cache.

This artifact is reusable as source-identical VE verification evidence.
It supplies no compiled S1 or Part 5 objects. Large VE logs are not duplicated
in this repository record; they remain in the identified artifact.

## Core coverage from the fixed source

The following is a **static source analysis**, not a compiler-generated
coverage report and not evidence that the in-progress build has succeeded.

The [fixed package configuration](https://github.com/UyNewNas/goldbach-formalization/blob/db97d0fe03250f4d9a8aea34b23e9c20f67010b8/lakefile.toml)
sets `defaultTargets = ["ImbalancedChen"]`.
The [fixed core workflow](https://github.com/UyNewNas/goldbach-formalization/blob/db97d0fe03250f4d9a8aea34b23e9c20f67010b8/.github/workflows/lean.yml)
sets empty `BUILD_ARGS`.
The [pinned lean-action build script](https://github.com/leanprover/lean-action/blob/f061402b660e0c34644504b324e830f2991d4865/scripts/lake_build.sh)
executes `lake build $BUILD_ARGS`.
The pinned Lean distribution's `Lake/Config/LeanLibConfig.lean` defaults
`roots` to `#[name]` and `globs` to `roots.map Glob.one`.

A read-only traversal of project source at the fixed head and goldbach source
at `09b97db5764ade1246bfb77206baa1b124760958` found **253 ImbalancedChen
modules**, including the root, and **753 MathlibNt modules** in the root import
closure, with no missing source modules. These counts exclude Mathlib and
Lean package modules.

The closure contains the baseline
`CurrentChenPointwise`, `CurrentChenPairedDeletion` and
`CurrentChenSummedBridge` modules. It excludes these existing Part 5 leaves:

- `ImbalancedChen.CurrentChenBuchstabRefinement`.
- `ImbalancedChen.CurrentChenMeanLedger`.
- `ImbalancedChen.CurrentChenLowerScale`.

`CurrentChenInitialSource` and `CurrentChenInitialMean` do not yet exist
at this fixed commit. The root closure also excludes the pinned upstream:

- `MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier`.
- `MathlibNt.SieveTheory.LiLiuGoldbachS1BetaFixedNormalizedLower`.
- `MathlibNt.SieveTheory.LiLiuGoldbachBadBound`.

The only root-closure module name containing `S1` or `Buchstab` is
`MathlibNt.SieveTheory.LiLiuGoldbachBuchstab`. That module is not the
Part 5 `CurrentChenBuchstabRefinement` leaf or its 11/20 theorem.

A future success of this unchanged core workflow would not itself verify
these excluded leaves or the actual S1 lower supplier.

## Availability and acceptance limits at observation

Core had **zero artifacts**. Its optional Lake cache save step was pending.
The successful cache-restore action step alone does not establish that a
cache was found. The core job-log download returned `BlobNotFound` (404)
while the job was still running; this is not evidence of a Lean failure.
The connector rejected the repository Actions cache-list endpoint as
unsupported (400), so no claim is made about the repository's other cache
entries. No alternative route or cache mutation was attempted.

These two runs establish no new acceptance for the Part 5 new leaves, the
actual S1 lower supplier, the complete adopted-mask Chen mean, or final
`hLower`. They provide no immediately reusable S1/Part 5 compilation objects.

The independent, source-identical Buchstab three-gate receipt in
[../buchstab/receipt.json](../buchstab/receipt.json) is unchanged. Its acceptance
does not come from either workflow observed here.

No Lean or Lake command was executed for this review. No workflow was
triggered or rerun, and no source or local proof-validation queue was changed.
The only files prepared by the recording step are this scope note and
`snapshot.json`.
