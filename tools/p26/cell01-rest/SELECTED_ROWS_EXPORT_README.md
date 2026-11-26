# Restricted Cell01 selected-row export

`export_selected_rows.py` is a new, independent Python exporter. The accepted
`export_batch_evidence.py` remains byte-for-byte unchanged (35,205 bytes;
SHA-256 `6d60a4360f8c3f364a0e8b183831d8d50ba09c00db5a75f34fef94e56dde42f0`).
The mechanical diff is `export_selected_rows.diff`.

## Two permitted scenarios

| Scenario | Actual verifier invocation | Required terminal state | Exported rows and steps | Scope |
|---|---|---|---|---|
| `c-prefix-budget-pause` | `--batch C` selecting 98–143 | Sole `PARTIAL.json`, `BUDGET_PAUSE` before the next row; completed exactly 98–106; remaining exactly 107–143 | 9 rows, 27 successful steps | `batch_complete=false` |
| `c-tail-success` | Explicit `--rows 107 108 … 143` | Sole `SUCCESS.json`; selected and completed exactly 107–143 | 37 rows, 111 successful steps | The selected 37-row run is complete |

Both retain `full_C_batch_claimed=false` and
`cross_context_aggregation_performed=false`. A future C summary must join the
two exact, disjoint ranges while preserving their separate execution contexts.
No other row selection, arbitrary failed run, partially accepted row, contradictory
terminal marker, reordered chain, or unaccounted attempt file is accepted.

## Verification preserved and runtime adaptations

The new exporter retains the pinned verifier's `validated_receipt`, complete
owned inventory/type/transitive-axiom parser, 399-supplier inventory, current
source/object hashes, import closures, historical same-SHA recurrence join,
regular tar payloads, full archive readback, and post-export frozen-input checks.
Only selected new owner object bodies enter the archive; old supplier objects
are rehashed in place.

The actual MCP command is parsed as a direct Python invocation and matched to
the frozen legal targets, exact ordinal order, stage, attempt, cache, and runtime
limits. Actual toolchain, Mathlib and package paths come from that command and
must match `RUN.json`. The Mathlib commit is resolved by reading Git metadata;
the exporter does not run Git. Historical receipt argv stay unchanged, and
their compiler identities are compared with the current host's exact binary
bytes. MCP `memory_peak_bytes` (P1) and `peak_memory_bytes` (P3) retain their
original field name and any original `memory_peak_source` text in the report.
The raw MCP receipt is included unchanged. No metrics from separate contexts
are merged.

## Cloud use

Use a raw successful proof MCP task receipt saved as JSON, and a fresh output
directory outside the proof stage. The command performs no Lean invocation,
source generation, Git operation, or network transfer:

```sh
python3 -B export_selected_rows.py \
  --stage /workspace/p26-continuation-59264dd64286/cell01-batch-C-finite-v2 \
  --attempt p1-cell01-batch-C-v2-canonical1 \
  --scenario c-prefix-budget-pause \
  --proof-mcp-receipt /absolute/path/PREFIX_PROOF_MCP_TASK.json \
  --output /absolute/fresh/cloud/prefix-evidence

python3 -B export_selected_rows.py \
  --stage /workspace/p26-continuation-59264dd64286/cell01-rest-finite-v2 \
  --attempt cell01-rows107-143-v2 \
  --scenario c-tail-success \
  --proof-mcp-receipt /absolute/path/TAIL_PROOF_MCP_TASK.json \
  --output /absolute/fresh/cloud/tail-evidence
```

`--check-only` runs the strict audit without writing an evidence archive.
Complete evidence archives remain on the respective cloud host; only the
small `SUMMARY.json` is intended for return. The blocked row001 completed
archive is neither needed nor read.

## Local test boundary

`python -B tools/p26/cell01-rest/test_export_selected_rows.py` runs seven
synthetic test groups. They exercise the two legal selections, illegal
selection/argv cases, hidden incomplete attempt files, host runtime/metric
differences, a real nine-object synthetic archive readback, and byte/AST
preservation of the accepted v1 core. These tests establish exporter behavior,
not mathematical acceptance of any real row. Actual receipt and object audit
results are produced only by running the exporter on the corresponding cloud
stage. No original-floor transport, integral result, or full P2.6 closure is
claimed by this tool package.
