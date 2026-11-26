# Cell05 rows15: original supplier capsule recovered on P1

The existing Cell05 rows15 provider was recovered by the already reviewed row capsule builder. All four submitted P1 jobs succeeded with exit code 0. The build task was `job_3efb24ed8cd943dfabdce81a8dd71d68`, with actual runtime 8.471887350082397 seconds and peak memory 195067904 bytes. Its requested limits were 600 seconds, 2048 MiB, and 2 CPU threads.

## Result retained on P1

- Archive: `/workspace/p26-continuation-557a12f3bcd7/cell05-rows15-capsule-v1/rows15-provider-v1.tar.xz`
- Bytes: **2397884**
- SHA256: **b41f83e3ec17764d06cfbd6b095c7cc499594de0c5060f78327fa0ffd351dfdd**
- Exact original report: `BUILD_REPORT_ORIGINAL.json`, 720 bytes, SHA256 `ca950b17e7d8f9508318a9624e037aa9157d28e6c91e757313c63685819c6f7c`.

The original builder rechecked 45 accepted receipt steps and 5147 owned declarations, and produced 267 regular archive members with 496 original absolute path mappings. The archive contains the 15 existing row object bodies and excludes old baseline and fields object bodies. The donor report calls these `new_object_bodies: 15` relative to its supplier baseline; these are recovered existing accepted objects, not newly proved owners.

The builder and deployment wrapper both verified archive member readback. Original evidence inputs and deployed source package bytes remained unchanged. The source package was the reviewed 101404-byte archive with SHA256 `43c3c0a0358a8be6b419a3d30df426df1fe3ee3fcd756e6cd49e9fad931332ef`; all 19 regular members were checked against its exact build manifest before safe deployment. Upload, code, control, and output roots were new task-specific paths. Existing mismatched files and pre-existing output archives are rejected, and original inputs are never overwritten.

## Evidence and scope

`RECOVERY_RESULT.json` links the exact original report, decoded wrapper result, exact 2853-byte stdout, submitted command pins, and original MCP response files. Final task metadata verifies all three source uploads and the build succeeded. The stdout retrieval reached EOF without truncation; its base64 and text bodies agree. Saved `DEPLOYMENT_PLAN.json` retains its initial preparation-time status; actual completion is recorded separately in `RECOVERY_RESULT.json`.

No Lean command or previously passed test was rerun. New Lean acceptances are **0**. No Cell01 path was modified, and no old Cell01 Row001 archive or receipt group was selected. Only the small report and MCP metadata were retrieved; the complete capsule remains on P1. P2 deployment was not performed. This recovery supplies an existing dependency for the remaining Cell05 connections and does not complete Cell05 or P2.6.
