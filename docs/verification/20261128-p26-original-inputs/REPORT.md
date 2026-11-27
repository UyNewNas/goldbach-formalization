# Original P2.6 input recovery and authorized publication

All 13 geometry and 13 moment witness files match the byte lengths and SHA256
values in `docs/verification/20261125-p26/ORIGINAL_INPUT_SCALE.json`.
The total original size is 80,189,086 bytes. The archive is 18,600,020 bytes,
with SHA256 `201942a41594e4bc3133b3fe7cc771c20452c6917fc415a427b3477b0ab50a2d`.

The user explicitly authorized publishing these inputs and proof materials to
`UyNewNas/goldbach-formalization`. The separate archive branch is
`artifacts/p26-original13-inputs-201942a4-20261127`, commit
`a2a7146f8de2beb8fc79f09d111f4af023840580`. The remote head was read back, then
the archive was fetched into this environment. Every member was compared with
the existing ledger before restoring missing files under `/workspace/goldbach-research`.
Existing files were checked and preserved. Original CRLF bytes were preserved.

`READBACK.json` records the local verification. Recovery and hash identity make
the original inputs available; they do not grant a mathematical certificate or
complete P2.6. No original input was substituted, rounded or regenerated.
