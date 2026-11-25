# Batch15: fourteen failed owners in three bounded groups

`run_repairs.py` is a scope adaptation of the published Batch14 thin caller
at commit `73b740f11ff5aa04b980485f6700deeb99291291`, whose SHA256 is
`8136e7e18eaef0686031ac59d7d7b1e70b68acbb5fb195886a5aa29ebefdbd83`.
It installs and runs only the chosen repair group from root's
`SOURCE_UPDATES.json`, schema `p1_batch15_failed_fourteen_repairs_v1`.
The explicit source commit must contain that manifest and the full reviewed
postimage. This packet does not establish new target acceptance.

## Fixed groups and preimages

All target names in the following table have prefix `ImbalancedChen.` and
retain this order within their group.

| Group | Targets, in order | Preimage commit | Source union |
| --- | --- | --- | ---: |
| `wire-five` | `P1ActualVariableFifthPositiveCellLimit`; `P1ActualVariableFifthGlobalSourceAssembly`; `P1OriginalFifthRawBoxSelectorEquivalence`; `P1OriginalFifthMiddleShellBinMoment`; `P1OriginalOld15Majorant` | `220c14630ffd266f824bdbf0977147ecb740c0dd` | 271 |
| `ordinary-five` | `P1OriginalVariableFourthActiveOnly`; `P5ActualHBMediumRoleSupports`; `P4BCompactSmoothMassPrecision`; `P2OriginalAdaptiveSourceSplit`; `P2OriginalLowerCompactStartCapConstructor` | `220c14630ffd266f824bdbf0977147ecb740c0dd` | 365 |
| `interiors-four` | `P4AOriginalFull87H3Interiors`; `P4AOriginalFull87SeedNineFiftyInteriors`; `P4AOriginalFull87H5H7Interiors`; `P4AOriginalFull87DescAscPairInteriors` | `4f7a975211bdbdccc76adc14734aa2de4a13b6ad` | 219 |

The manifest must list exactly these 14 owners and three groups. The caller
checks every module/path/group tuple, the exact Git preimage hash at its own
preimage commit, the published postimage hash, and unchanged imports. Before
any source write, every file in the selected group must be a regular,
non-symlink file containing either that preimage or the exact postimage.
The unchanged Batch5 source installer then handles backups and exact no-ops.

Every source in the selected group's complete import closure must match the
chosen source commit. The full sorted source-map fingerprint and module count
must agree with the manifest. None of the 14 candidates may depend on another
candidate. The four protected P1 root source hashes remain checked throughout.
No source from either unselected group is installed by that invocation.

The already successful symbolic pair, PrefixBinding, MovingHarmonicEnvelope,
AscendingAllInteriors and other prior accepted owners are not scheduled as
targets. Accepted dependency objects are reused behind the existing no-build
gate; the normal receipt must show that only the selected owner was actually
built. Each audit plan selects only this invocation's successful normals.

## Unchanged validation engine

The generic API remains:

```text
commit 4cea0407c1258eaddd7d4952cffa4aea67310422
docs/p1/20261125/batch13-repairs/run_repairs.py
SHA256 95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea
```

The caller loads this exact Git object and calls `preflight_sources`,
`normal_one` and `audit` with the explicit current source commit, project,
group receipt root and full source map. It does not call the API's old fixed
five-owner input function, patch its constants, or copy its validators.
Batch5/6 helpers, Batch10 pure utilities, e9, serializer and guards retain
their original pins and options.

The helper source anchor is explicitly fixed to source220. It is independent
of `interiors-four`'s newer preimage commit. This separation avoids treating
the revised interior preimage as a request to change the tools.

One original lane-0 serializer runs the selected group sequentially.
Independent failures preserve logs while other selected owners may continue.
Every successful normal is durable before audit. The original normal
validator checks exact current source/dependency/object/trace/configuration/
runtime bindings, command/log provenance and five output artifacts before
reuse. A ready target without the required provenance is held instead of
being rebuilt. The original e9 validator reuses complete audits and holds
partial audit directories for inspection.

Whole-group source, runtime and configuration checks run before each normal,
before audit and after audit. A final context mismatch prevents a completed
group claim. The original dirty source-Git state must remain unchanged.

## Separate source and runtime configuration

The manifest carries both exact three-file maps. Git source configuration is
checked against the chosen source commit. Actual runtime configuration is
checked against the pinned existing environment:

| Evidence | SHA256 |
| --- | --- |
| `../runtime-configuration/ACTUAL_CONFIGURATION.json` | `df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614` |
| `../runtime-configuration/review.json` | `34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880` |

Runtime mode requires the existing 1823-byte `lakefile.toml`, SHA256
`e696bda5c7f8478793603a3593b691a29df4e962cb9b7d3d2a358a3cbb546b48`,
the unchanged toolchain/manifest files, and the exact five runtime artifacts
from the historical review. `lakefile.lean` must be absent. No actual config,
guard, serializer, heartbeat, thread or memory setting is changed.

`--config-basis runtime` is the default for cloud checks and runs.
`--config-basis source` is allowed only for `--check` on a non-cloud project.
It reads the source configuration and published evidence without reading
cloud runtime files, and reports `SOURCE_CONFIG_ONLY_NOT_CLOUD_READY`.
Neither check mode performs a Lean/Lake invocation or claims acceptance.

## Interface and durable roots

```text
run_repairs.py --source-commit FULL_SHA
              --group wire-five|ordinary-five|interiors-four
              (--check | --run)
              [--config-basis runtime|source]
```

Receipt roots are separate by explicit source commit and selected group:

```text
/workspace/p1-complete-proof/20261125-batch15-repairs-v1/<source_commit>/<group>
```

The frozen binding records the driver/input hashes, group scope, source and
runtime configuration, and runtime fingerprints. Git configuration bytes are
stored separately under `inputs/source-configuration/`. Keep the source
commit and caller bytes identical when resuming a root.

After root publishes the reviewed source snapshot, set `BATCH15_SOURCE_COMMIT`
to its full lowercase SHA. A local source-only check is:

```bash
python3 -B docs/p1/20261125/batch15-repairs/run_repairs.py \
  --source-commit "$BATCH15_SOURCE_COMMIT" --group wire-five \
  --check --config-basis source \
  --source-repo /workspace/scratch/cba105ac8c38/goldbach-p1 \
  --project /workspace/scratch/cba105ac8c38/goldbach-p1
```

Repeat the check for the other two groups. Root schedules actual runtime
checks and execution separately in the existing compiler environment:

```bash
python3 -B docs/p1/20261125/batch15-repairs/run_repairs.py \
  --source-commit "$BATCH15_SOURCE_COMMIT" --group wire-five \
  --check --config-basis runtime

python3 -B docs/p1/20261125/batch15-repairs/run_repairs.py \
  --source-commit "$BATCH15_SOURCE_COMMIT" --group wire-five \
  --run --config-basis runtime
```

Use a distinct invocation for `ordinary-five` and `interiors-four`. Execution
cannot use local project/repository overrides. No invocation schedules all
three groups, the successful symbolic pair, or a complete P1 closure build.

## Local verification record

The code was derived from the exact approved Batch14 Git object. After
normalizing the intentional scope/schema/event-label changes and the explicit
helper anchor, all eight function ASTs match that published thin caller.
Python syntax compilation passed using temporary bytecode outside the repo.
Current source graphs independently confirm 271, 365 and 219 modules and no
dependencies among the 14 candidate owners.

Actual CLI source checks await a published source commit containing root's
completed Batch15 manifest and repair payloads. That gate is not claimed by
the static checks above. No Lean/Lake, cloud task, source installation, Git
commit or publication was performed by this caller's author. The new caller
never claims whole P1 completion.
