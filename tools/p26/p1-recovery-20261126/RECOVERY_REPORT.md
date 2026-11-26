# P1 Cell01 recovery inventory, 2026-11-26

The read-only P1 task `job_4e99d82513ec482c81661ef72f3a6e28` succeeded with exit code 0. Its complete, untruncated 412,644-byte output is preserved in `P1_RECOVERY_RESULT.json` (SHA256 `4f55e26b85dca6077be3bca7cbcd0be19506ffadaeadc6973cf43ffc2dea6d54`). `MCP_TASK.json` retains the original task metadata and submitted command; `OUTPUT_READBACK.json` records the contiguous output reads.

## Existing material

All 189 requested objects match their original byte counts and SHA256 identities: 178 canonical suppliers, nine C-prefix finite owners (098–106), the original row000 floor bridge, and generic original-floor transport. All 189 selected source files also match their original pins; the minimal transfer requires exactly 14 of these source bodies. No unexpected sidecars were present. All 12 checked fixed metadata/script/accepted-seal pins match, including the original C-prefix export anchor.

This inspection establishes the availability and identity of the files. It does not independently replace their original proof receipt validation or grant new proof acceptance. The separately authorized, previously reviewed v2 capsule builder performs the required original-chain checks before creating its transport archive.

The deployed family's SOURCE_MANIFEST and SUPPLIER_DELTA were initially reported as PRESENT_UNANCHORED by the probe; their reported complete pins were subsequently compared locally with the frozen request and repository metadata and match exactly. The raw probe output remains unchanged.

## Unknown earlier submissions

At the time of the read-only task, all fixed v1 and v2 capsule builder/request/output paths were absent. Both capsule versions therefore classified as NOT_UPLOADED_NO_ACCEPTANCE. The three pilot adapter files and three prepared-input files were absent, and the pilot stage did not exist. The previously deployed pilot executor and CODE_MANIFEST remained present with their original exact pins.

These facts describe current filesystem effects. They do not establish the historical RPC acceptance state of the earlier unknown submissions. No earlier command was retried. The rejected v1 builder was not reused. The later v2 build has its own explicit authorization, immutable command/submission records, and previously unused fixed v2 paths in the `capsule-v2` subdirectory.

## Boundaries

The inspection ran zero Lean or proof commands and made no remote writes. It accessed no row001 files and exported no old receipt or log bodies. It did not access or modify the separate Cell05 rows15 recovery paths. The C-prefix scope is nine owners and 27 accepted steps; the 45-step Cell05 rows15 capsule is a separate task.

The capsule's next step is exact-byte object/source transport only. It does not represent a new Cell01 owner proof run or full-family success.
