# Actual final-field attempt004 failure

Task `1847725e973d4e2f866720eac3f6f4d9` tested the existing published source
at `4e69759e3d27495c0e7bccfee23b7a0b42c48ea6`. Normal checking failed; kernel
replay and owned-declaration acceptance were not reached.

`SUMMARY.json` and `TASK_STDOUT.log` retain the observed result. The exact complete
4,809,977-byte result and its logs are stored in `ACTUAL_EVIDENCE.json.xz`, an
XZ-compressed JSON array. Each entry has `name`, `bytes`, `sha256`, and the exact
UTF-8 `content`. Decompress with Python `lzma.decompress` and verify each content
hash before use. The complete result SHA256 is
`c8f52525af889be955ffaa245d40ead84f560fea0de0f04e53ae202afeaab1f2`.

The remaining normal goals equate `rawActive8Items.toArray`,
`rawVertexValuesItems.toArray`, and `rawFaceLedgerItems.toArray` to their existing
typed aliases. This is an elaboration/normalization issue, not an added
mathematical assumption. The subsequent excessive-memory diagnostic is retained.

All accepted dependency receipts retain their original publication and scope.
This failed aggregate is not relabeled as a successful owner.
