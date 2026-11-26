# Cell05 rows15: private transfer from P1 completed

This is the later, explicitly authorized transfer step after the original recovery recorded in `README.md` and `RECOVERY_RESULT.json`. The original build report and earlier records are preserved unchanged.

## Exact local capsule

- Path outside the repository: `/tmp/p26-row15-transfer-557a12f3bcd7/rows15-provider-v1.tar.xz`
- Size: **2397884 bytes**
- SHA256: **b41f83e3ec17764d06cfbd6b095c7cc499594de0c5060f78327fa0ffd351dfdd**
- Original P1 capsule remains at `/workspace/p26-continuation-557a12f3bcd7/cell05-rows15-capsule-v1/rows15-provider-v1.tar.xz`.

The single read-only P1 task `job_b05cd207f74c4ff0bb1f28340c363f0f` succeeded with exit code 0 in 0.13850164413452148 seconds. It read the fixed capsule and its exact original report, rehashed both, and emitted a bounded transfer stream. It did not rebuild the archive, run Lean, or write any P1 input. The task produced exactly 3199941 stdout bytes without truncation.

## Pagination and local validation

The output was recovered in **98 pages**, continuously from byte 0 through byte 3199941 and EOF. Each page has its original task ID, offset, next offset, byte count, EOF flag, stream label, and decoded-byte SHA256 recorded under `transfer-page-pins/`. The API permits at most 32768 bytes per page; initial requests for a larger page returned an `INVALID_ARGUMENT` schema error. There was no automatic approval rejection and no repeated remote task execution.

All page bodies and the assembled stdout remain in the private directory outside the repository. That directory uses mode 0700 and the capsule uses mode 0600. Repository records contain source code, task metadata, and hashes; they contain no complete capsule base64 or binary payload.

The local verifier checked the fixed capsule and report SHA256 values, matching before/after pins, **267 regular archive members**, all **266 payload member pins**, the four original source anchors, the exact original export manifest, and all **496 original path mappings** against the existing pinned supplier metadata. It used the original `archive_bytes`, `load_plan`, and `row_mapping` helpers. It did not replay the original 45 proof steps or produce any new proof receipt.

`TRANSFER_RESULT.json` records the successful capture and verification. `TRANSFER_MEMBER_PINS.json` records every archive member's size and SHA256. `TRANSFER_SOURCE_AND_RECORD_PINS.json` binds the scripts and task records, including confirmation that the submitted command matches the saved local command bytes. `TRANSFER_LOCAL_VALIDATION.json` preserves the actual successful local validator result.

## Handoff boundary

The capsule is ready for the root agent's separate P2 transfer preparation. **No P2 upload was submitted by this agent.** The original P1 capsule must remain until P2 reception is confirmed. This is solely the Cell05 rows15 capsule; the separate Cell01 route and the previously blocked Cell01 Row001 evidence group are not included. Lean commands and new Lean acceptances remain **0**. The old report's counts of 45 accepted steps and 5147 owned declarations describe the original builder's evidence validation; this transfer adds byte and mapping verification, not new proof credit.
