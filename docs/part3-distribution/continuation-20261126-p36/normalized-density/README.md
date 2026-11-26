# Normalized density increment evidence

## Accepted scope

All three new owners passed their original strict compilation, exact independent
kernel replay and complete defining-module/type/transitive-axiom inventory.
The three recovered archives also passed local evidence verification without
rerunning Lean. See [ACCEPTANCE.json](ACCEPTANCE.json) and the
[mathematical explanation](MATHEMATICAL_SCOPE.md).

| New owner | Explicit mathematical theorems | Complete theorem records | Evidence |
| --- | ---: | ---: | --- |
| `P3OriginalU5RoundedPairDensity` | 3 | 5 | [Local verification](accepted-rounded-pair-density/LOCAL_VERIFICATION.json) |
| `P3OriginalU5NormalizedDensityReserve` | 2 | 11 | [Local verification](accepted-normalized-row/LOCAL_VERIFICATION.json) |
| `P3OriginalU5PairNormalizedDensityReserve` | 2 | 10 | [Local verification](accepted-pair-normalized/LOCAL_VERIFICATION.json) |

The increment contributes 3 owners and 26 complete records: 7 explicit
mathematical theorems and 19 Lean-generated equations or proof/simplifier
helpers. Together with the unchanged accepted four groups, the total is
27 owners and 414 unique declaration names (317 theorem records and 97
definitions). Two generated equations in the rounded-pair owner retain the
existing Plateau namespace; the original audit identifies their defining
module, which is what the count uses.

The [independent inventory and terminal crosscheck](validation/INVENTORY_AND_TERMINAL_CROSSCHECK.json)
compares every archived declaration with its original audit log, checks
uniqueness across all seven groups, and matches each new run's original
command-end records against its archive. Its nine owned gate records also
match the archived command-log bytes and hashes. The original row singleton
passed before a later independent candidate failed in the same outer task;
the exact successful singleton, not the failed outer task as a whole, is the
accepted scope.

The entire P3.6 node remains open: `whole_p36_closed=false` and
`currentVerified=false`. The actual positive signed main term, required
sparse/query-family mass, physical common-Q/complement payment, full high-rank
(S)/(F), and same-rho PP with the exact-mean correction remain outstanding.
This increment is not eligible for the overall closed-nodes PR.

## Export and verification

Export one owner at a time from its original completed `VERIFIED_OWNED`
run. Use the original runtime checkout, and provide the Git commit
and SHA-256 of the reviewed source. A later checkout is usable when
all project files in the original run still agree with that commit.

```sh
python3 export_verified_increment.py export \
  --project "$project" --report "$original_report" \
  --source-commit "$source_commit" --owner "$owner" \
  --source-sha256 "$source_sha256" --output-dir "$new_output"
```

The export prints the receipt and archive SHA-256 values. Keep that output
with the original successful task terminal. A failed or unfinished report
is rejected before an acceptance receipt can be created.

Pass `--report-sha256` whenever the original terminal prints the report
digest. When the terminal records only the path, the receipt labels the
report identity accordingly and records the digest measured at export.
When the original wrapper preserves both runtime tool measurements, pass
its file and independently recovered hash through `--runtime-binding`
and `--runtime-binding-sha256`, together with `--report-sha256`.
Retry an interrupted export with a new, unused `--output-dir`.

After transferring `RECEIPT.json` and `evidence.tar.xz`, check the receipt
against its digest from the original export output.

```sh
python3 export_verified_increment.py verify \
  --project "$local_project" --receipt "$recovered/RECEIPT.json" \
  --archive "$recovered/evidence.tar.xz" --receipt-sha256 "$exported_receipt_sha256" \
  --source-commit "$source_commit" --owner "$owner" --source-sha256 "$source_sha256"
```

Both modes reuse the original audit renderer and inventory validator.
The tar preserves the original report, command logs, audit source,
declarations, owned object facets, and exact project sources in that run's
dependency graph. It includes the verifier configuration and original
source selection when supplied. Each reused module must link to the
original successful compile record and matching command log in an earlier
run. Those complete prior reports are archived once per run. The original
compile, replay and audit order is checked against the dependency graph.

The [P1 lineage diagnostic](attempts/lineage-diagnostic.json) identifies
16 exact earlier reports written by three older runner versions. Each
exception binds the original report path, full report SHA-256, and writer
SHA-256. The verifier checks these against the full archived reports and
still requires each reused compile stage to succeed with the original
command, matching inputs, objects and log. Receipts identify the historical
writer and report status. The accepted credit is for the new singleton
owner, and the earlier reports supply only reused successful dependency
compile stages.

The writer source at `verification/p36/compile_p36_local.py` was checked
in the following Git commits. The input-key construction, key digest,
compile command, and object and reuse check implementations agreed across
all four versions.

| Runner SHA-256 prefix | Source commit |
| --- | --- |
| `229fbe9720e6` | `edc2e68c360bf66bd33e4a3a5211cafd6d95f218` |
| `3ca5c1e97132` | `d90a01b0a388893dcf71bab0acf5bde259b93050` |
| `895a8bc67d6c` | `e4ad395e4901628d85a27d17d0f87a16ea943433` |
| `be263af86651` | `a65747d928f5d8110933ac14cb525e236680e189` |

The receipt distinguishes report-recorded hashes, independent before/after
measurements available from the original wrapper, and additional inputs
hashed at export. The raw runner records the replay command and its
success and checks checker and audit-helper stability in memory. Its bare
report does not serialize the runtime checker or helper digests. Without
the separate wrapper artifact, those original runtime digests are marked
unknown. The excerpt-free archive lets local verification rederive reuse
from the retained reports and command logs, reconstruct dependency
signatures, and check every archived payload. Dependency objects outside
the owned payloads are represented by hashes that the exporter rechecks.

The exporter pins the two archive helper files before importing them.
The helpers are export-time tooling and can be copied into the compiler
checkout independently of the frozen proof commit.

The CLI supports the normalized row reserve, the rounded pair density,
and the pair-normalized density reserve. Each receipt applies to its
single original owner. Export and local verification use existing evidence
and perform zero Lean runs.

Run the historical evidence and tamper tests from the repository root.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s docs/part3-distribution/continuation-20261126-p36/normalized-density \
  -p 'test_*.py' -v
```

The final reviewed exporter passed all nineteen tests (15.677 seconds); see
[evidence-tool test results](evidence-tool-reviews/TEST_RESULTS.json). The historical classical-six fixture reproduced
all 37,857 snapshot bindings across 10,125 graph modules and passed
archive recovery against the current checkout. Its archived prior log
and state records supply fixture prior reports for 371 reused modules
from eleven earlier runs. Rejection tests exercise missing and failed
historical lineage, command reordering, malformed selection manifests,
escaped package sources, missing native aliases, runtime binding drift,
original terminal hash mismatch, and tampered archive helpers. The 29
existing P3.6 Python tests also passed.

## Restore the frozen source snapshots

The private compiler snapshots preserve source-only attempts separately from
the final integrated working branch. The accepted receipts name their exact
source commit. Fetch the retained bundle once before verifying evidence in a
fresh clone. The durable local ref `refs/p36-evidence/normalized-density-20261126`
keeps the snapshots reachable across later fetches. The commands retain
the current checkout.

```sh
git bundle verify docs/part3-distribution/continuation-20261126-p36/normalized-density/source-snapshots/normalized-density-source.bundle
git fetch docs/part3-distribution/continuation-20261126-p36/normalized-density/source-snapshots/normalized-density-source.bundle refs/heads/compile/p36-normalized-density-20261126:refs/p36-evidence/normalized-density-20261126
```

The prerequisite, full snapshot IDs, bundle size and SHA-256 are recorded
in [BUNDLE.json](source-snapshots/BUNDLE.json). The bundle preserves failed
proof-expression attempts for provenance; it grants no formal acceptance.
The final integrated source bytes must agree with the owner and its actual
frozen dependency graph during local evidence verification.

The original row and first total run share one outer compiler task. The
row's own report completed as `VERIFIED_OWNED`; that outer task later failed
because the next, separate total run found an unreachable trailing tactic.
The repaired total has its own covering run. Acceptance is assessed from
each exact original singleton report and its corresponding stages.
