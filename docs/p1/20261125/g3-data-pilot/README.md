# G3 Data-only pilot

This bounded caller validates only
`ImbalancedChen.P4AOriginalNewFifthArchiveData`. It performs no source or fixture
installation and does not rebuild or repeat the accepted Reader audit. It does
not claim the 94 downstream Checked modules, their numerical contracts, or P1
completion.

## Fixed inputs and existing evidence

The source snapshot is
`220c14630ffd266f824bdbf0977147ecb740c0dd`. The caller requires all 68 project
sources in the Data closure to match that snapshot. Data's only direct project
import is `ImbalancedChen.P4AOriginalNewFifthArchiveReader`.

| Input | SHA256 |
| --- | --- |
| Data source | `5fc51f4622c04ff0d2ce69d87e19d7b0a1cb20ccd48295309e24aab6a4879df4` |
| Reader source | `59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6` |
| `g3-reuse/G3_REUSE_INVENTORY.json` | `c89fd6388cfb269ebe74bad97e62454a8ad36fc317d7e5685253f4c13785047e` |
| Batch5 `AUDIT24_VALIDATION_RESULTS.json` | `18a4660cae2ce1f0fa2d233f84be244f46b7a9522bd46f7289c89e50d72adcd1` |
| Published `retry_four.py` | `290228a30d7a773a52a27241d6d3fbf18efb3d5e3fd9b30c8f0db4d670e5717e` |
| Published `run_candidates.py` | `8fc871e44e4702b01005aa179170cd172b50537f7aaa98e6bbdde4253ef2ac47` |

Both reusable callers are read from Git commit
`afe0ca6653f4eba9c258ecb8a743d0b45edd10c6`; their source/install entry points are
not called. The Batch5 helper, Batch6 command recorder, Batch10 snapshot/runtime
primitives, and e9 auditor retain their published hashes. The existing lane-0
guard and serializer apply their unchanged runtime options.

The 94 literal include pairs must match the ordered C0000–C0046 and F0000–F0046
paths in Data. All 188 files are resolved relative to the Data source directory
and checked against the inventory's exact size and SHA256: 423,244,864 bytes in
total. The Reader's current source and five output artifacts must match the
published accepted Batch5 receipt. Its complete 67-module source closure must
also match that receipt and the fixed source snapshot.

## Commands and receipts

Use the existing cloud source checkout and project. Run these as separate tasks:

```bash
python3 -B docs/p1/20261125/g3-data-pilot/run_pilot.py --check
python3 -B docs/p1/20261125/g3-data-pilot/run_pilot.py --normal
python3 -B docs/p1/20261125/g3-data-pilot/run_pilot.py --audit
```

`--check` performs the source, fixture, and accepted Reader comparisons without
writing receipts or invoking Lean/Lake. It reports input compatibility, not Data
acceptance. `--source-repo` and `--project` overrides are available only for this
read-only mode; execution is restricted to `/workspace/goldbach-formalization`
and `/workspace/blue-member-build`.

Normal and audit receipts are stored under
`/workspace/p1-complete-proof/20261125-g3-data-pilot-v1`. Each command uses a fresh
attempt directory and one existing serialized lane-0 worker. The original dirty
source Git state is recorded before and after and must remain unchanged.

`--normal` calls the unchanged `normal_one` for Data alone. Direct-dependency and
target readiness use `--no-build`. A fresh normal pass requires the actual build
log to contain exactly the Data target, matching dependency source/object/trace,
configuration, and runtime fingerprints, and a durable source-plus-five-output
snapshot. The normal receipt is saved before any separate audit command.

The Reader reads NPY bytes during elaboration without adding those files to
Lake's input trace. For that reason, the caller also writes immutable
`FIXTURES_BEFORE.json`, `FIXTURES_AFTER.json`, and
`normal/ImbalancedChen.P4AOriginalNewFifthArchiveData/FIXTURE_BOUND_NORMAL.json`.
The companion binds both full fixture/Reader measurements to the generic normal
receipt's SHA256 and Data's source-plus-five-output snapshot. Checkpoint times
must enclose the actual normal command. The generic dependency context remains
unchanged so the published normal and audit validators retain their exact
meaning.

Normal reuse and every audit require a matching companion, current fixtures,
accepted Reader evidence, normal command/log, and normal dependency/output
bindings. A generic `NORMAL_PASS.json` without the companion is held for
inspection; the caller neither retroactively certifies its fixtures nor rebuilds
it. A ready target without durable normal provenance is likewise held by the
unchanged normal primitive. Failed commands retain their complete logs. If a
failure or interruption leaves a normal receipt without the companion, the same
hold applies on restart.

`--audit` never invokes the normal builder. It reuses the published one-lane e9
plan/validation procedure for the single Data owner, including kernel checking
and all environment-owned declarations. It checks the fixture-bound normal
before and after, and writes `FIXTURE_BOUND_AUDIT.json` in the audit attempt,
binding the current fixture measurements, normal companion, accepted e9 results,
and Data outputs. Completed e9 receipts are validated and reused; partial audit
directories are preserved and held for inspection. No empty lane is invoked.

The final statuses distinguish `NORMAL_WITH_FIXTURES_AUDIT_PENDING` from
`DATA_OWNER_ACCEPTED_WITH_FIXTURES`; failure or stale evidence is
`HELD_OR_FAILED`. None of these statuses accepts downstream Checked modules or
the complete P1 proof.

## Local verification boundary

Python syntax and the pinned Git/source/schema checks passed locally: 68 Data
closure modules, 67 Reader closure modules, 94 include pairs, and 188 inventory
entries with the expected total size. The local checkout does not contain the
cloud's installed NPY files or accepted Reader artifacts, so the complete live
`--check`, normal build, kernel check, and full-owned audit remain cloud work.
Three isolated control-flow checks also confirmed that an orphan generic normal,
a dangling companion path, and an audit without a fixture-bound normal each hold
before any normal-builder call.
No Lean invocation or fixture/source installation was performed while creating
this caller.
