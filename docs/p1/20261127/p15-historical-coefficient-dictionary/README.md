# Historical coefficient dictionary — independent whole-source probe

## Frozen candidate and current status

The candidate is the complete `P1OriginalHistoricalCoefficientDictionary.lean`
published at AK `d4f88a20262af7d54ed0e6e58dfc533496c595e3`:

`docs/source-only/20261127/p1-historical-coefficient-dictionary/P1OriginalHistoricalCoefficientDictionary.lean`

It remains **9079 bytes**, SHA256
`b90556b05b152cea39fd72eb55428986105ad86a4926e2badf50175927c47409`.
This package does not edit it. It adds a separately scoped no-output probe,
an exact-publication stager, provenance locators and local boundary checks.
No cloud command, Lean command, kernel command, source installation or Git write
was executed by this package's author. There is no actual probe result yet.
The root coordinator submits the published stager and probe.

The frozen probe is **26465 bytes**, SHA256
`93f5e3e93eaf6948ae63a072b65cae98bf90cd76bfe235b536499eaf3cecb106`.
The stager pins those exact bytes. A future successful whole-source probe is
still distinct from normal, kernel and full-owned-declaration acceptance.
P1.5 remains OPEN. Neither this candidate nor its probe imports or assumes a
new Geometry acceptance.

## Actual dependency and evidence scopes

The candidate directly imports `P1Full87TrueDUnitBound`,
`P1OriginalHistoricalMiddlePointwiseData`, and the external module
`Mathlib.Data.Complex.Basic`. Its project closure is exactly **288 modules**.
The new owner would make 289 project sources if installed for later formal
acceptance. The probe does not install that source.

The 288-module closure is exactly the initial4 original accepted four-owner
closure. All 288 source SHA256 values and project-import lists match the original
initial4 graph; the symmetric difference is empty. This is an equality of the
actual committed graph and source identities, not a conclusion from module
existence. The graph is separate from AG's 144-module selected scope: **180** of
the dictionary's dependencies lie outside AG144.

| Dependency class | Count | Original evidence used |
| --- | ---: | --- |
| Accepted supplier | 4 | Original initial4 normal, kernel and full-owned receipts |
| Fixed dependency | 177 | Delta's original accepted normal dependency context |
| Fixed dependency | 60 | SingletonPointwise's original accepted normal dependency context |
| Fixed dependency | 47 | Atlas10 HBDyadicPartition's original accepted normal dependency context |
| P3 HOLD, prior correction targets, observation-only or unclassified | 0 | None admitted |

The four accepted suppliers are:

* `ImbalancedChen.P1Full87TrueDPolicyDelta`
* `ImbalancedChen.P1Full87TrueDUnitBound`
* `ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData`
* `ImbalancedChen.P1OriginalSingletonPointwiseData`

The HBDyadicPartition evidence witness has its own **58-source** closure,
including **11 modules outside D288**. All 58 are already inside the original
AG144 scope. The probe retains a separate witness scope and validates that
owner using the unchanged original reader with `validate_live=True`. It does
not add any of those 11 modules to the dictionary import graph. The dictionary's
47 relevant fixed pins still come from the manifest-assigned witness's original
normal receipt through `fixed_dependency_pins`.

The complete per-module source list and the separate 58/11 lists are in
`DEPENDENCY_SCOPE.json`. `ORIGINAL_EVIDENCE_BINDINGS.json` partitions all 284
fixed modules by their actual original witness and records the five owners'
normal paths and all published receipt fingerprints.

## Original identities and reusable readers

The source inventory is the frozen AG manifest:

* Commit: `63ad8bf4c52caed9f4e199834ae1d2b0b18f971b`.
* Path: `docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json`.
* 369103 bytes; SHA256 `21c0b14701a2123edab7353aa27dbb9c950427a805d75aaa3562c6033eb137f9`.

Original initial4 evidence retains commit
`d20acdf13882e17d97833064f5e7c54f3192b03c` and job
`job_1ed0e0c8d4ee466f8444aff044abe510`. Its original root is
`/workspace/p1-complete-proof/20261125-p15-singleton-proper-power-v1`.
Original atlas10 evidence retains commit
`418ad4b9a5f2d992871062258a2eefd7fdf4b9ee` and job
`job_5f42ad18fde84377987c244daf0b5bfc`. Its original root is
`/workspace/p1-complete-proof/20261125-p15-current-context-integration-v1/atlas10`.

For either group, the normal receipt has the exact form:

`<original-root>/<original-commit>/<module>/normal/<module>/NORMAL_PASS.json`.

The original run is `<original-root>/<original-commit>/runs/attempt-00000`.
The audit is the unique original 20-hex subdirectory of the owner's `audits`
directory. Its identity is discovered and validated by the original reader;
this package does not invent an audit ID or rebind a receipt to the new
publication. Complete path and fingerprint bindings are in the locator JSON.

The immutable AG driver is 343325 bytes with SHA256
`0440906dfc3caa894ff7226e53ad42be54adda1d5879bd1a72cad578a3b3612d`.
The relevant unchanged APIs are:

| Function | What it actually checks |
| --- | --- |
| `historical_group` | Original committed graph/source, public receipt, job/owner identity, retained driver and original result/context/Git files |
| `retained_owner(..., validate_live=True)` | Original normal context and complete kernel/full-owned audit, using the original accepting commit |
| `fixed_dependency_pins` | Source identity and original `.olean`/`.trace` values from the assigned witness's normal dependency context |
| `snapshot` | Actual source identity, all retained expected pins, all 21 artifact slots per protected module, runtime/configuration and retained evidence fingerprints |

The latter calls use the original `normal_valid` and `audit_valid` API at
`4cea0407c1258eaddd7d4952cffa4aea67310422`, file
`docs/p1/20261125/batch13-repairs/run_repairs.py`, SHA256
`95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea`.
This is read-only validation of existing commands and logs, not replay of those
Lean/kernel commands. No normal object fingerprint is guessed from a module
name or substituted by an observation-only entry.

The old `source_manifest`/`preflight` enforce the old 21-owner whitelist. The
probe calls `source_manifest` with the original AG selection, keeps its AG144
binding under its original name, and creates an independent read-only D288 spec
with no selected compilation owner. It never passes the new owner into the old
whitelist or changes the old driver or manifest.

## Execution and preservation

`stage_dictionary.py PUBLICATION_COMMIT` fetches the exact publication object
without checkout, pins the probe and AK Lean bytes, and writes only a separate
published entrypoint and staging receipt. Existing different bytes and symlink
paths are rejected. HEAD, worktree diff, index diff and status must remain equal.

The published probe is then run with:

```text
python3 -B /workspace/p1-complete-proof/20261127-p15-historical-coefficient-dictionary-probe-v1/PUBLICATION_COMMIT/published-entrypoints/probe_dictionary.py --publication PUBLICATION_COMMIT
```

Its sequence is:

1. Load the immutable AI reader and original committed inputs, with the complete
   AK Lean file and exact three-import list.
2. Allocate a fresh probe attempt. Inside its failure-recording `try/finally`,
   call immutable `base.check(c)` and record full preservation observations.
3. Independently revalidate the four original initial4 suppliers, read all 284
   original fixed pins, compare actual cached artifacts, and validate the
   separate 58-source atlas witness. No candidate Lean command is allowed before
   all of this succeeds.
4. Check readiness of all three direct imports using the original guard and
   serializer with `lake --no-build build`. Any build, failure, or missing cache
   stops the attempt.
5. Submit the complete unchanged candidate once through the original serializer
   and guard using `lake --no-build env lean PROBE.lean`, without an output flag.
6. Re-read the original AI acceptance and compare all protected observations and
   acceptance-backed snapshots. Save the actual result regardless of success.

The D288 scope protects **6048 artifact slots**, including every one of the 180
dependencies outside AG144. The separate witness protects 1218 slots. Existing
AI/AE/AG protections remain intact through `base.check(c)`. The union of the
dictionary and the old 160-module artifact watch has 340 distinct project
modules; the witness adds no new module to that union. Five complete original
supplier/witness evidence directories, the original AI evidence/install trees,
runtime/configuration, and Git metadata are also preserved.

The new owner must have no canonical source, no artifact in any of its 21 slots,
and no started acceptance history. The standalone probe may not emit any
compiler artifact. A successful Lean exit with changed protected state is a
failed probe.

The raw preservation observations are explicitly labelled as observations, not
acceptance. If the original dependency verification fails after attempt
allocation, the `finally` block still writes the after observation and failure
`ACTUAL_DICTIONARY_PROBE_RESULT.json`. Such a result has no completed dependency
acceptance, no candidate Lean command, and no new acceptance. Failures in loading
the pinned original entrypoint itself, before an attempt can be allocated, emit
`DICTIONARY_PROBE_HELD` in the job log.

## Local verification and remaining live work

The initial new boundary suite passed 19 checks. After the preparation-failure
review, one new injection check was added and only the six directly affected
run/failure/stager-pin checks were executed again; all six passed. The current
test file therefore contains 20 cases, but there was no single 20-case run on
the final source hash. `LOCAL_BOUNDARY_VERIFICATION.json` and `TEST_RESULTS.log`
retain that distinction. These are Python harness checks, not Lean results.

Independent source review of the earlier probe body found no API argument,
scope, or false-acceptance issue in the D288/W58 organization. Its concrete
preparation-result concern is addressed by the final `try/finally` structure and
the new injection check. The root coordinator reviews and submits the final
published bytes. Actual cloud availability, original live receipt/cache
validation and candidate Lean typechecking remain to be observed in that run.
