# Five ordinary P1 dependency candidates

This packet schedules exactly the five existing modules below for a future
guarded normal and full-owned audit run. All formal sources remain unchanged
at source commit `220c14630ffd266f824bdbf0977147ecb740c0dd`.
The P2, P4 and P5 names here are actual P1 dependencies from the existing
53-candidate inventory; the scope does not extend to their separate projects.

The packet itself provides source and prior-parent evidence bindings. It does
not establish current compiler readiness, new target acceptance, or complete
P1 acceptance. No Lean, Lake, compiler job, source installation, or Git
publication was performed while preparing it.

## Exact scope and source bindings

All module names in the following table have prefix `ImbalancedChen.`.
The inventory pointers were checked against
`docs/p1/20261125/next-frontier/INVENTORY.json`, SHA256
`b7d88481a3c92de7369150fd40f1f88f2f770110cf12c72a08b432976d630a07`.

| Order | Candidate | Inventory pointer | Source closure modules | Existing direct parent |
| --- | --- | --- | ---: | --- |
| 1 | `P1OriginalVariableFourthActiveOnly` | `/candidates/17` | 227 | `P1OriginalVariableFourthFullSourceActivation` |
| 2 | `P5ActualHBMediumRoleSupports` | `/candidates/43` | 58 | `P5ActualHBMediumBranchPartition` |
| 3 | `P4BCompactSmoothMassPrecision` | `/candidates/42` | 118 | `P4BSmoothMassParameterOrder` |
| 4 | `P2OriginalAdaptiveSourceSplit` | `/candidates/20` | 37 | `P2OriginalInitialClosedTree` |
| 5 | `P2OriginalLowerCompactStartCapConstructor` | `/candidates/22` | 138 | `P2OriginalLowerBufferedAffineBoxes` |

The candidates are pairwise import-incomparable. Their union contains **365
project modules**. Every source byte and all three project configuration files
match source220, the observed checkout commit
`9266746988135ae39c995c3edd68ded3a952baf6`, and the local project tree used for
the check. None of the four separately repaired Batch11 owners or the two
held OrderedThird source variants is in this closure.

`CANDIDATES.json` contains the complete 365-module source SHA256 map, exact
candidate Git blobs and imports, every direct parent's full closure, separate
source and runtime configuration bindings, and the historical evidence pointers. Its
SHA256 is
`bcf758d858193e72dff1ff2ef77313b23abbffb17f38a601ddd51c0281ac363d`.
The complete source-map fingerprint is
`a0b31dbad35260a6e05e784ba02e0b21fd3502c8a2197792577639571b058dae`.
The JSON records the precise fingerprint recipe.

The proof bodies are symbolic: exact fallback cancellation, induction on HB
roles and supports, compact finite-subcover precision, the literal source
split integral identity, and compact-start cap construction. These are source
classifications, not measured compiler-time or memory guarantees. Existing
comments marking the formal sources uncompiled are retained byte for byte;
the new manifest does not promote them to accepted targets.

## Reuse the five accepted direct parents

Every direct parent is an actual owned target of the published Batch10
normal/kernel/full-owned result, rather than a dependency-only entry. The
archive is:

```text
docs/p1/20261125/batch10-accepted-evidence/verification.tar.xz
SHA256 49432bc69a385bfea32fc0a69990726ca4ebc5702da79019d296312c0382ec97
```

All lane paths below have archive prefix
`20261125-batch10-audits-v1/receipts/` and receipt filename
`VALIDATION_RESULTS.json`.

| Parent | Receipt lane | Whole parent source closure matched | Owned declarations |
| --- | --- | ---: | ---: |
| `P1OriginalVariableFourthFullSourceActivation` | `chunk-000/lane-1` | 226 / 226 | 36 |
| `P5ActualHBMediumBranchPartition` | `chunk-008/lane-1` | 57 / 57 | 33 |
| `P4BSmoothMassParameterOrder` | `chunk-008/lane-0` | 117 / 117 | 9 |
| `P2OriginalInitialClosedTree` | `chunk-001/lane-0` | 36 / 36 | 24 |
| `P2OriginalLowerBufferedAffineBoxes` | `chunk-001/lane-0` | 137 / 137 | 38 |

The manifest pins the exact receipt, `OWNED_EXPORTS.json`, and raw full-owned
log hashes. The per-parent records retain the recorded source plus five
output fingerprints, original runtime-state path/hash, normal and kernel
evidence pointers, and the full source context. All complete parent source
contexts match the archived result and source220. The inventory agent also
independently checked these five receipt scopes and closure matches.

At execution, a parent source/output or recorded runtime-state mismatch
holds that candidate for inspection. The caller does not build, kernel-check,
or audit any accepted parent. The unchanged normal API then runs its direct
dependency `lake --no-build build` gate before attempting the candidate.
Fresh runtime artifact comparisons have not been performed by this local
packet preparation.

## Source configuration and accepted runtime configuration

The cloud project's existing `lakefile.toml` has 1823 bytes and SHA256
`e696bda5c7f8478793603a3593b691a29df4e962cb9b7d3d2a358a3cbb546b48`.
The Git source file has 394 bytes and SHA256
`b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254`.
The existing cloud file includes its established `moreLeanArgs` and
compatibility library declarations. `lean-toolchain` and `lake-manifest.json`
match the source configuration; `lakefile.lean` is absent.

Both exact configuration maps remain in the catalog. The caller pins and
freezes these two evidence files from the catalog commit:

| Evidence | SHA256 |
| --- | --- |
| `docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json` | `df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614` |
| `docs/p1/20261125/runtime-configuration/review.json` | `34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880` |

The historical review binds all 71 Batch10 and all four Batch11 accepted
normal receipts, and the three new Batch13 normal receipts, to this same
runtime configuration. It also records their unchanged two runtime-state
files, guard, serializer and audit template. Default `--config-basis runtime`
checks the live three-config map and all five runtime artifacts against
those exact accepted fingerprints. Runtime hashes and configuration are
checked again before each target and before and after audit.

`--config-basis source` is allowed only for `--check` on a non-cloud project.
It checks Git source configuration, reads the pinned evidence, and prints
`SOURCE_CONFIG_ONLY_NOT_CLOUD_READY`; it does not read cloud runtime files
or establish cloud readiness. No configuration, guard, serializer or resource
limit is changed by this packet. Git configuration bytes are frozen under
`inputs/source-configuration/` so they remain distinct from runtime evidence.

## Thin caller and unchanged validators

`run_candidates.py` adapts the published Wire orchestration layer. The
normal/context/normal-reuse/full-owned validators are loaded unchanged from
`retry_four.py` at
`9246927b8faebca3c06e4a5a47e733b5f13536db`, SHA256
`290228a30d7a773a52a27241d6d3fbf18efb3d5e3fd9b30c8f0db4d670e5717e`.
The existing generic audit caller is loaded unchanged from the Batch12
`run_candidates.py` at
`afe0ca6653f4eba9c258ecb8a743d0b45edd10c6`, SHA256
`8fc871e44e4702b01005aa179170cd172b50537f7aaa98e6bbdde4253ef2ac47`.

Those APIs retain the pinned Batch5 helper, Batch6 operations, Batch10 pure
primitives, e9 auditor, existing lane-0 serializer and resource guard. No
historical constant is patched, and no validation engine is copied into this
packet. The source anchor and candidate scope are checked independently of
the earlier four-repair manifest.

The new durable root is:

```text
/workspace/p1-complete-proof/20261125-ordinary-five-v1
```

Its immutable binding records the source, tool and catalog commits, driver
and input hashes, exact candidate scope, configuration, and existing runtime.
Successful normal results retain their durable receipt before auditing.
Independent normal failures preserve logs and do not prevent attempts for
the other four owners. The generic audit selects only successful normals.
Completed normal and audit receipts are revalidated before reuse; an already
ready target without matching normal provenance holds instead of being
rebuilt. Partial audit directories remain held for inspection.

Execution preserves the original dirty source Git state. No project source
installation is available in this caller. The five-owner result never claims
whole P1 completion.

## Read-only check and future execution

Before publication, the read-only check may use the local catalog, whose
exact SHA256 is still enforced. For this checkout:

```bash
python3 -B docs/p1/20261125/next-frontier/ordinary-five/run_candidates.py \
  --check --config-basis source \
  --source-repo /workspace/scratch/cba105ac8c38/goldbach-p1 \
  --project /workspace/scratch/cba105ac8c38/goldbach-p1
```

After root publishes the reviewed packet, set `ORDINARY_FIVE_COMMIT` to that
full commit SHA. The catalog will then be read from its exact Git object:

```bash
python3 -B docs/p1/20261125/next-frontier/ordinary-five/run_candidates.py \
  --catalog-commit "$ORDINARY_FIVE_COMMIT" --check --config-basis runtime
```

Only root schedules actual execution in the existing compiler environment:

```bash
python3 -B docs/p1/20261125/next-frontier/ordinary-five/run_candidates.py \
  --catalog-commit "$ORDINARY_FIVE_COMMIT" --run --config-basis runtime
```

`--run` requires a full catalog commit and the existing cloud paths
`/workspace/goldbach-formalization` and `/workspace/blue-member-build`.
It cannot execute using the unpublished local-catalog fallback. Keep the
same catalog commit and caller bytes when resuming the same durable root.

## Local verification performed

- `py_compile` succeeded, with temporary bytecode outside the repository.
- The actual local `--check --config-basis source` exited 0 with
  `SOURCE_CONFIG_ONLY_NOT_CLOUD_READY`, exactly five targets and
  365 source modules, and separate source/runtime configuration fingerprints.
- Default runtime-basis checking rejected the local source-only configuration.
- Source-basis `--run` and cloud-project source-basis `--check` were rejected
  before project or runtime access.
- Candidate index/hash/import identity, the complete source map, all five
  parent source contexts, and the archived full-owned evidence identities
  were checked while constructing the manifest.

These checks establish the bounded caller's local source bindings. They do
not constitute a Lean compilation, runtime stock gate, kernel replay, new
full-owned acceptance, or publication.
