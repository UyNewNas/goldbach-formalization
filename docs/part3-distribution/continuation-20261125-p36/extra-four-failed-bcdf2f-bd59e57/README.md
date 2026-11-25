# First EXTRA4 attempt: preserved failure evidence

Status: **FAILED_NOT_ACCEPTED**. This packet carries no complete owned acceptance and does not close P3.6.

P1 task `job_bcdf2f96240744f2a9236f9da384f25b` ran from 2026-11-25 15:19:42.173 UTC to 15:34:13.257 UTC, exiting with code 1 after 871.084 seconds. It used one CPU, a 12,000 MB allocation and the unchanged strict compilation, official checker and full axiom-inventory gates. The task ended normally when the second source-repair watch expired; it was not killed by its 3,600-second total limit.

The owned group consisted solely of `P5OriginalU5NativeRootCover`, `P3OriginalU5FreshFifthSquareSupplier`, `P3OriginalU5AllSourceSquares` and `P3OriginalU5AllSignedSquares`. Previously accepted MAIN modules were not owned targets.

## Actual stages

Round 1 at `45428d4ef7eac2f19dfd17a3d3a9a4d0903296ce` failed on the original fifth-code expression in FreshFifth. Its exact failed-source blob changed at `bd59e570667c51476c148d520246da75046c90a7`, which the bounded supervisor locked for round 2. Unrelated intervening commits did not trigger a retry.

In round 2, 254 ordinary project dependencies and the one explicitly accepted Tagged object were reused. NativeRootCover passed strict compilation in 12.003 seconds and FreshFifth in 9.778 seconds. AllSource failed in 43.809 seconds with the complete diagnostic retained here; AllSigned was not started. No kernel replay or full axiom audit was invoked for this owned group.

`STAGE_DIAGNOSIS.json` binds these stages to the original final report. `rounds.json` is the exact remote supervisor journal. `FAILURE_LOG_BINDINGS.json` verifies both locally reconstructed diagnostic bodies against the original remote log hashes recorded in that journal. The historical diagnostic metadata is preserved rather than rewritten.

## Packet and transport

`evidence.tar.xz` is the exact 2,098,068-byte archive emitted by the failed task, SHA-256 `735c819580e105f95067a00747660e5becebee9ffa5442f22410823c4ff70dd2`. It contains the final round's report and logs, both rounds' supervisor output and test logs, the supervisor journal, and the executed control scripts. It does not substitute final-round files for earlier files sharing a basename.

The complete task stdout was recovered through 77 contiguous lossless base64 pages: 2,158,189 bytes, SHA-256 `344d2586f7f4c51946b2e151e8c9aa787244269aa504b7cf6f1185ecfe15c0bf`. Binary framing was checked exactly as 60,097 prefix bytes + 2,098,068 archive bytes + 24 suffix bytes. `TRANSPORT_STATUS.json` records all page and archive-member hashes. A successful transport check is not a successful proof check.

The isolated remote state and successful object files remain available for the separately authorized continuation at the subsequent source fix. This packet's original failure status remains unchanged.
