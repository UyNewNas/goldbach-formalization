# Cell01 Batch A: accepted rows 002–049 and independent cloud export

**Status: PASS for the 48 listed finite owners.** Batch A completed normal
compilation, independent kernel replay and complete owned auditing for original
ordinals 2 through 49. The independent exporter then checked all 144 evidence
chains and read back every member of the completed archive. The full archive
remains on P3; it has not been recovered locally.

This checkpoint covers the original finite arithmetic checks and five prefix
floor conditions in those owners. It does not accept an OriginalFloorTransport
or other analytic/integral bridge, another batch, or all P2.6.

## Acceptance and independent checks

| Item | Verified result |
|---|---:|
| Accepted owners | 48 |
| Normal / independent kernel / full owned steps | 48 / 48 / 48 |
| Newly executed / reused steps in this batch | 144 / 0 |
| Complete owned declarations | 14,016 |
| Existing accepted suppliers | 399 |
| Supplier files rehashed in cache and installed stage | 1,596 |
| Exact RUN input-fingerprint inventory | 1,939 files |
| Per-owner project import closure | 400 modules |
| Selected batch project closure | 447 modules |
| New target object bodies in export | 48 |
| Old supplier object bodies in export | 0 |
| Listed archive members / total including manifest | 739 / 740 |
| Watched files unchanged after packing and readback | 2,524 |

The owned audit checks equality of the serialized, environment and printed
declaration inventories, complete types, unsafe/partial/axiom flags, and the
actual transitive axiom sets. Their union is exactly `Classical.choice`,
`Quot.sound`, and `propext`. The actual imported project module inventory is
also checked against each owner's 400-module dependency closure.

The exporter binds `SUCCESS.batch_complete`, selected ordinals, all step
receipts and commands, `ROW_ACCEPTED` chains, source/object/audit bytes,
runtime/search paths, and the exact reviewed driver/helper/verifier/supplier
pins. It reuses the reviewed v2 `validated_receipt` and complete-owned parser;
it does not invoke a compiler, Git, or a network client.

The 399-supplier inventory is checked as the original 398 exact source/object
pairs plus accepted `Geometry01BoundedAccess`. Its three prior receipts and
complete 25-declaration owned inventory are retained separately from the
14,016 newly accepted declarations. The historical P3 row000 records still
state that Recurrence's supplier kernel was pending at that time. Closure is
joined using the separate successful P1 kernel receipt for the same source and
object SHA; historical pending records are not rewritten.

## Original proof task and measurements

Proof task: `8bbfbc9505f54a89935bd7ce1ad7cc7d`, succeeded, exit 0.

| Measurement | Value |
|---|---:|
| MCP whole-proof-task runtime | 1,449.568 seconds |
| MCP-reported whole-proof-task peak RSS | 2,868,711,424 bytes |
| Sum of 144 individual Lean command elapsed times | 1,387.2815586338984 seconds |
| Largest sampled Lean process-tree RSS among those commands | 2,842,529,792 bytes |

The two runtime and two memory measurements have different observation
boundaries. `PROOF_MCP_TASK.json` retains the actual task receipt and command.

Independent audit/export task: `72e04da685e74e0984cf4680b82c2660`, succeeded,
exit 0, 41.914 seconds, MCP-reported peak 128,638,976 bytes. This task ran only
Python evidence checks, compression and archive readback. Its first progress
record was `STRICT_BATCH_AUDIT_PASSED` for 48 targets, 144 steps and 14,016
declarations. `EXPORT_MCP_TASK.json` records the task and authored script pin.

## Cloud artifacts

Cloud directory:

```text
/workspace/p26-continuation-59264dd64286/cell01-batch-A-completed-evidence
```

| Artifact | Bytes | SHA256 |
|---|---:|---|
| `evidence.tar.xz` | 14,548,928 | `0d8e41f8668ce999bd0585fb1a2549b4fe9fb8c12a6f9bc73a128026ec238a5e` |
| `EXPORT_MANIFEST.json` | 320,781 | `441d78db7a639b36ae48e127c60943075a0a4e641396ef2bd5b88d10897728d1` |
| `INDEPENDENT_REVIEW.json` | 191,899 | `994b48ab9622dbc729c1a51366807a48617f6c25bd59d81fdf63db3ecccf220a` |

`SUMMARY.json` in that cloud directory is the small returned summary. Its
structured contents are saved locally as `CLOUD_EXPORT_SUMMARY.json`. The full
review report and all per-declaration evidence are present in the cloud archive.
The blocked row001 completed-evidence archive was neither read nor transferred.

The archive stores regular file payloads, including when source paths are
hardlinked. It includes the authored exporter source, the proof MCP task
receipt, selected sources/audits/objects, all successful command/log/result
chains, complete owned inventories, frozen context records and supplier
provenance manifests. Every member was read back against the manifest before
the final archive was published under its cloud filename.

## Reusable exporter

Repository source: `tools/p26/cell01-rest/export_batch_evidence.py`.

```text
bytes: 35205
sha256: 6d60a4360f8c3f364a0e8b183831d8d50ba09c00db5a75f34fef94e56dde42f0
```

It requires an explicit stage, attempt, batch, actual proof-MCP receipt and a
fresh output directory. It refuses an existing output directory, validates
the current exact object bodies, and never repairs or regenerates missing
proof artifacts. A `--check-only` option performs the audit without writing an
archive. Its reviewed v2 driver pin is
`ca58f8d847826d7d5db8d22637e3264a930defd6b3c63870595fdfe4b60ac27b`.

Future batches need their own successful task receipt and acceptance audit.
This report credits only Batch A and the 48 original ordinals listed above.
