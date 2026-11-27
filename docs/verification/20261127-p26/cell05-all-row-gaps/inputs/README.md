# Original pure suppliers for Cell05 gap proofs

This is an input-preparation checkpoint, not a new Lean acceptance. It supplies exactly two previously checked canonical modules for the planned Cell05 all-56 gap owner. The previous Cell05 Shape checkpoint remains accepted; global P2.6 remains open.

`pure2-original-evidence.tar.xz` is 266236 bytes, SHA-256 `874cf979a761f81d76761b937e76c81d6ee635244e734285280a79e949840960`. Its 17 regular files expand to 6598953 bytes. Sixteen files are exact, unmodified members of the original Cell00 portable archive; `TRANSPORT.json` separately records the selection and transport pins.

Original archive: `cell00-480-suppliers.tar.xz`, 35675620 bytes, SHA-256 `f945d949653f37567a7e66dfbc39a37b854d4114a4ef17b2279221ab8c971a7b`, recovered inside the preserved `p26-cell00-geometry01-checkpoint.tar`. Original MANIFEST, AUDIT, RUNTIME, FULL_SOURCE_CLOSURE, source/object files, and all four normal/kernel result files with their original logs remain unchanged. The extraction verifies all selected bytes and the original prior-receipt pointers in FULL_SOURCE_CLOSURE; a separate complete archive readback matches every member.

| Supplier | Source SHA-256 | Object SHA-256 |
|---|---|---|
| P2OriginalSaving19RowNumericsPure | d39f14310722214e47e5b25c093ec1fb17fe61c3880ab1355867401187cb45e6 | 2cbb204ca34761d5d95e1a024917359fd53f90b0d81a365364d2a4d637fc4304 |
| P2OriginalLogMomentQ96ArithmeticPure | 754f6bc945a37636ec9bc62224e9b842a97d3f2718990b59aa2caa8e9f164424 | f02478d3d572ce8757850d4538db0c08e91e127a07c5d99ff682883ffeea6028 |

Both sources were independently fetched from precise work-branch HEAD `5177b7b9e0617006888e7733416912440e72d41a` and match byte-for-byte, including their Git blob identities. `PURE2_GIT_SOURCE_READBACK.json` preserves those fetched texts and identities. The original normal commands did not explicitly specify trust zero, and this checkpoint does not change that historical fact. It adds no old-supplier owned audit, no proof replay, and no claim about a historical loaded-runtime inventory.

The reviewed new executor must separately validate the actual current P2 runtime and the 128 combined suppliers, including exact agreement for the shared ArchiveSchema and SourceJson objects, before any new proof command. This transport does not itself perform that live validation.
