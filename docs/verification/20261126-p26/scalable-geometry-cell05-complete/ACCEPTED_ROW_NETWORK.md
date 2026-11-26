# Accepted original cell05 row network

P1 task `job_03820698aca949449a3c8543e9bb8652` succeeded with exit 0:
15 new owners passed 15 normal compilations, 15 stock independent kernel
checks, and 15 complete owned-declaration audits. The audits cover 5,147
declarations, including their full types and transitive axiom dependencies.
The task took 937.8954091072083 seconds and reported a maximum memory usage
of 2,979,545,088 bytes. No accepted supplier proof command was replayed.

The frozen v3 source package adds parser and typed-row leaves for original
rows 16 through 55, plus binary composition nodes. Together with the six
previously accepted owners for rows 0 through 15, this covers the exact
original `simplices` array's 56 rows and their typed-row assembly. It does
not yet prove the whole cell05 JSON parse, full geometry decode, the other
field arrays, geometric meaning, or the integral endpoint.

The reviewed exporter validated all 45 accepted chains and wrote 434 listed
members plus `EXPORT_MANIFEST.json`, with only the 15 new object bodies.
Every tar member was read back and all selected input bytes were checked
again after packing. The archive remains on P1:

- Path: `/workspace/p26-continuation-59264dd64286/scalable-geometry-cell05-complete-v3/exports/phase1-p1-cell05-complete-rows-v3-v2-evidence.tar.xz`
- Size: 2,486,324 bytes.
- SHA256: `bb4ee98e403f46f28d5882ff4f20d6b2c1e8e1608c63befc398e06b4668b104d`.
- Manifest: 109,913 bytes, SHA256 `c3b4f6b47352a2b7f8e8ee5ac6f6d9133e615eba62c189914330919818b8c452`.

`CLOUD_EXPORT_SUMMARY.json` contains the small returned export report and
manifest summary. `PROOF_MCP_TASK.json` records the real proof task metadata.
`READBACK_MCP_TASK.json` records a separate read-only inspection that checked
the completed archive's exact size/hash and extracted its root manifest
summary. That inspection performed no Lean command and returned no archive
body. The exporter's MCP identifier was not retained in the response log;
the readback task is explicitly not presented as the export task.

The first summary-inspection attempt selected every filename ending in
`manifest.json` and correctly stopped on several historical manifests.
The corrected inspection names the root `EXPORT_MANIFEST.json` exactly;
neither inspection changed the accepted proof or export artifacts.

The v3 candidate history, the v2 workflow failures, and the original pilot
receipts remain unchanged. The 73 independent field-owner candidates have
their own workflow and acceptance boundary. Full P2.6 remains open.
