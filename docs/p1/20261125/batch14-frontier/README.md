# Batch14: two symbolic repairs and four existing interior candidates

This packet runs the six manifest owners in two explicit groups. The source
manifest is `SOURCE_UPDATES.json`, schema
`p1_batch14_two_repairs_four_interiors_v1`. Actual normal, kernel and full-owned
acceptance remains pending for these source candidates. The new caller does
not schedule PrefixBinding, MovingHarmonicEnvelope or AscendingAllInteriors.

## Bounded source scope

All modules below have prefix `ImbalancedChen.`. The required
`--source-commit` supplies the complete reviewed postimage and manifest.

| Group | Targets | Allowed preimage commit | Complete union |
| --- | --- | --- | ---: |
| `symbolic-two` | `P4AOriginalFull87HistoryCore`, `Part3ActualWResidualCompletion` | `c257b7ade3b82d8f3ae126ffb1ca999871e9cd57` | 254 modules |
| `interiors-four` | `P4AOriginalFull87H3Interiors`, `P4AOriginalFull87SeedNineFiftyInteriors`, `P4AOriginalFull87H5H7Interiors`, `P4AOriginalFull87DescAscPairInteriors` | `220c14630ffd266f824bdbf0977147ecb740c0dd` | 219 modules |

The first two changes follow their actual Batch13 diagnostics. HistoryCore
states the reducible reciprocal-width function explicitly before applying
the already elaborated limit expression. ResidualCompletion states the
zero-index `shifted_cons` inequality explicitly before simplifying `mul_one`.
Their definitions, imports, theorem headers and options remain unchanged.
`ACTUAL_FAILURES.json` records the source diagnostics.

The four interiors reuse the published candidates from commit
`9266746988135ae39c995c3edd68ded3a952baf6`, reviewed in
`docs/p1/20261125/full87-other-interiors/REPAIRS.json`. Their expression changes
are kernel reduction for finite decisions, explicit `Fin 8` binders, and
explicit rational-to-real order transport. No new formal source edit was
made for this caller. The successful Ascending pilot supports trying the
same reviewed expression method; it does not accept these four owners or
provide their target-specific diagnostics.

Every manifest preimage is checked against its own exact Git object. Every
postimage is checked against the selected full source commit. The caller
checks all six paths, hashes and unchanged imports, then preflights only
the selected group's two or four project targets. Each target must be a
regular, non-symlink file with the recorded preimage or exact postimage.
Unknown bytes hold before source installation.

The full selected-group import graph must match the chosen source commit,
including every non-target source. Its sorted source-map SHA256 must equal
the manifest's group fingerprint. None of the six candidates is another
candidate's dependency. The source installer is the unchanged Batch5 helper;
it can replace only the selected group's manifest paths and preserves
backups. Four protected root sources are checked throughout execution.

## Reused normal and audit engine

The caller loads the published generic APIs from:

```text
commit 4cea0407c1258eaddd7d4952cffa4aea67310422
docs/p1/20261125/batch13-repairs/run_repairs.py
SHA256 95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea
```

It calls that module's `preflight_sources`, `normal_one` and `audit`
functions with the explicit source commit, project, receipt root and selected
source map. It does not invoke the module's fixed original five-owner inputs
or patch its constants. The original pinned Batch5 helper, Batch6 operations,
Batch10 pure primitives and e9 auditor are loaded unchanged from source220.
The original serializer runs one lane-0 worker per group with unchanged guards
and resource limits.

Each successful normal result is durable before audit. The existing normal
validator binds the target source, complete dependency sources, dependency
objects and traces, configuration, runtime, actual target build log and
current five outputs. Resuming revalidates that receipt and reuses it. A
ready target without matching normal provenance is held instead of rebuilt.
Independent target failures preserve logs while other group owners may
continue. Only successful normals enter the original e9 audit plan.

Completed audit receipts are checked by the original generic validator before
reuse. Partial audit directories remain held for inspection; this caller
does not overwrite or resume the non-resumable e9 lane internally. Source,
configuration and runtime checks occur before each normal, before audit and
after audit. A final context mismatch prevents the group result from claiming
completion, even if earlier audit artifacts exist.

The durable root is separate for each source commit and group:

```text
/workspace/p1-complete-proof/20261125-batch14-frontier-v1/<source_commit>/<group>
```

Its frozen binding includes the complete input pins, driver hash, source and
runtime configuration maps, runtime fingerprints and exact owner scope.
Original dirty source-Git state is recorded and must remain unchanged.
The result never claims whole P1 completion.

## Source configuration and actual accepted runtime

Git source configuration and the existing cloud runtime configuration are
bound separately. The cloud `lakefile.toml` is 1823 bytes, SHA256
`e696bda5c7f8478793603a3593b691a29df4e962cb9b7d3d2a358a3cbb546b48`;
the Git source file is 394 bytes, SHA256
`b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254`.
The other two configuration files match. `lakefile.lean` must be absent.
The caller preserves all actual configuration bytes and resource limits.

These exact evidence files must be present at the selected source commit:

| Evidence | SHA256 |
| --- | --- |
| `docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json` | `df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614` |
| `docs/p1/20261125/runtime-configuration/review.json` | `34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880` |

The historical review verifies the same configuration and five runtime
artifact fingerprints across all 71 Batch10 and four Batch11 accepted normal
receipts, and the three new Batch13 normal receipts. The caller checks both
manifest maps against that evidence. Default `--config-basis runtime` requires
the live project and unchanged guard, serializer, two runtime-state files and
audit template to match those accepted fingerprints. Evidence is frozen in
the receipt root; Git configuration bytes are separately frozen under
`inputs/source-configuration/`.

`--config-basis source` is allowed only for a non-cloud `--check`. It verifies
the source configuration without reading cloud runtime files and reports
`SOURCE_CONFIG_ONLY_NOT_CLOUD_READY`. This mode cannot install, build or audit.
Neither check mode claims compiled readiness or acceptance.

## Commands and verification boundary

After the reviewed files are available in one commit, use its full lowercase
SHA as `BATCH14_COMMIT`. Root can use an unpublished temporary commit object
for the same local source check before publication:

```bash
python3 -B docs/p1/20261125/batch14-frontier/run_candidates.py \
  --source-commit "$BATCH14_COMMIT" --group symbolic-two \
  --check --config-basis source \
  --source-repo /workspace/scratch/cba105ac8c38/goldbach-p1 \
  --project /workspace/scratch/cba105ac8c38/goldbach-p1
```

Repeat with `--group interiors-four` for its separate source check. Runtime
checks and execution use only the existing cloud paths and actual runtime
configuration:

```bash
python3 -B docs/p1/20261125/batch14-frontier/run_candidates.py \
  --source-commit "$BATCH14_COMMIT" --group symbolic-two \
  --check --config-basis runtime

python3 -B docs/p1/20261125/batch14-frontier/run_candidates.py \
  --source-commit "$BATCH14_COMMIT" --group symbolic-two \
  --run --config-basis runtime
```

Use a separate task with `--group interiors-four`; the two receipt roots do
not overlap. Keep the same source commit and caller bytes when resuming.
Local path overrides are allowed only for `--check`.

Local verification completed against published source commit
`4f7a975211bdbdccc76adc14734aa2de4a13b6ad`:

- `py_compile` passed, with temporary bytecode outside the repository.
- Both actual CLI `--check --config-basis source` commands exited 0 with
  `SOURCE_CONFIG_ONLY_NOT_CLOUD_READY`, respectively 254 and 219 source
  modules, and manifest SHA256
  `21fc05bc449d6b5d023de6448955fc5ac4058b4a563053f26e380bf5f6d93bf7`.
- Source-basis execution and source-basis checks on the cloud project were
  rejected before project or runtime access.
- Independent review repeated both CLI checks, checked all six preimage and
  postimage bindings, and confirmed the three already successful Batch13
  owners are absent even from these groups' dependency closures.

These are static orchestration checks, not a Lean compilation, no-build gate,
kernel replay or full-owned acceptance. No compiler job or Git publication
was performed by the caller author.
