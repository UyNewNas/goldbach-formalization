# Admission and W-layer group evidence

This adapter pins the previous exporter at SHA-256
`003d628292e0b1d067e9f87d3aad6b2c6f2a64db5b117e06cbe6bbf37743fcf5`
before executing its source bytes. It calls that exporter's existing
group-capable validation and packaging functions. The original
strict compile, replay and inventory checks, source/import/object
bindings, and historical lineage checks apply to all eight owners.
The adapter leaves the previous single-owner CLI and receipt format
intact.

## RootQ dependency provenance

The group adds one exact report pin to the loaded exporter. It binds the
original absolute report path, full report SHA-256, and writer SHA-256
from the independent [P1 readout](validation/ROOT_Q_LEGACY_READOUT.jsonl).
The historical writer is the already reviewed runner at Git commit
`e4ad395e4901628d85a27d17d0f87a16ea943433`. This pin applies only to
`ImbalancedChen.P2OriginalU5RootQ`'s successful dependency compile. That
stage exited zero without the owned strict flag, and the original report
retains its overall `FAILED` status. The previous exporter still reads
the complete original report and checks the compile stage, inputs,
object facets and log. Group export and verification bind the pin and
whether the archive used it. The existing pins and validation functions
are preserved.

## Original run inputs

Supply a UTF-8 JSON document with one `sources` array, in the exact order
of `OWNERS` in the adapter. Each entry has `module` (the dotted name),
`selected_path` (the project-relative Lean file), and
`selected_sha256` (the frozen source file digest). Use this same file as
the original runner's `--source-manifest`. Its raw SHA-256 is an independent
input to both export and local verification.

The original wrapper captures the following fields in a separate JSON
file and seals its SHA-256 in the original task output.

| Field | Value |
| --- | --- |
| `owners` | Exact, ordered eight-element owner list |
| `source_commit` | Exact frozen Git commit |
| `status`, `exit_code` | `VERIFIED_OWNED` and integer zero |
| `report`, `report_sha256` | Original absolute report path and SHA-256 |
| `source_manifest` | Object containing the original absolute `path` and `sha256` |
| `runtime_tool_sha256_before`, `runtime_tool_sha256_after` | Equal maps of the six original absolute file paths to their measured SHA-256 values |

The six paths are the original `lean`, `leanchecker`,
`verification/p36/compile_p36_local.py`,
`verification/verify_part3_continuation.py`,
`verification/verify_part3_distribution.py`, and
`verification/Part3DistributionAudit.lean`.

## Export and local verification

```sh
python3 export_group_evidence.py export \
  --project "$project" --source-commit "$source_commit" \
  --report "$original_report" --report-sha256 "$original_report_sha256" \
  --owner-manifest "$manifest" --owner-manifest-sha256 "$manifest_sha256" \
  --runtime-binding "$runtime_binding" --runtime-binding-sha256 "$runtime_binding_sha256" \
  --output-dir "$output"
```

Keep the original task's recorded digests and the exporter-printed
`group_receipt_sha256`. Recover `evidence.tar.xz`, `RECEIPT.json`,
`GROUP_RECEIPT.json`, `OWNER_MANIFEST.json`, and
`GROUP_RUNTIME_BINDING.json` together before verifying the group.

```sh
python3 export_group_evidence.py verify \
  --project "$local_project" --source-commit "$source_commit" \
  --evidence-dir "$recovered" --group-receipt-sha256 "$group_receipt_sha256" \
  --owner-manifest-sha256 "$manifest_sha256" \
  --runtime-binding-sha256 "$runtime_binding_sha256"
```

The base receipt keeps its singleton runtime slot empty and explicitly
unknown. The outer group receipt binds the raw base receipt and archive
hashes, the source commit and manifest, the ordered owners and source
digests, and the original group runtime capture. Local verification
rechecks those bindings and calls the pinned exporter on the full archive
and current project. No Lean run is part of packaging or verification.
The group receipt records `whole_p36_closed=false` and `currentVerified=false`.
An interrupted export can be retried with a new output directory.

## Actual eight-owner export and verification

The actual frozen group `8495b3b274a046060faf2ce9020b2588665634c0`
subsequently passed the unchanged original compiler/replay/inventory gate.
Its complete export and local verification passed for 313 declaration records
and 37,452 snapshots. The original report digest is
`dd61e7c35401d96c0cfbc22831411a3d2bc91f05e8e2918b16b1579711ad0529`;
the group receipt digest is
`34a4dded99425bd670e325dba6fbff3461626d64bda092e8f681a75cb6365dab`.

`accepted-group/LOCAL_VERIFICATION.json` records that real check.
`validation/EXPORT_INPUT_CROSSCHECK.json` independently matches the export
inputs against the original MCP terminal capture, including the report and
original runtime binding. `validation/INVENTORY_AND_TERMINAL_CROSSCHECK.json`
also matches the original strict/replay/audit stages and inventories across
all eight accepted groups. The local checks run no Lean compilation.

The exact historical RootQ report was recovered in full and verified under
the added pin; its overall status remains FAILED. Only its successful
RootQ dependency compile stage is consumed, with no additional owned credit.

## Regression fixture limits

The inherited classical-six fixture reuses the actual inventory, graph and logs,
but reconstructs missing prior-report bytes and changes conflicting historical
date paths. It tests the multi-owner validators and replay-omission rejection.
The actual eight-owner export and recovered archive still require their own
complete local verification against independently captured original hashes.
