# Cell05 scalable original-geometry pilot: verified scope and performance

**Six new owners passed normal compilation, independent kernel replay, and full owned-declaration audit.** The accepted scope is cell05 rows 0–15 and their two-leaf composition. Complete cell05 parsing/decoding and P2.6 remain open.

## Evidence and result

- P1 verification task: `job_7495828b5cfc44b5a24cc40fffdfda07`, exit 0.
- Exact Lean 4.33.0-rc1 commit: `62eed1db4d67327ec8120be05f1a1b0847d74561`.
- Exact Mathlib commit: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- 18 successful steps: six normal, six independent `leanchecker`, six complete owned audits.
- All 111 listed export members were rehashed locally. Each compiled source and audit is byte-identical to the local candidate.
- The 2,054 inventoried declarations agree between serialized module data, full environment ownership, and printed full types. The transitive axiom union is `Classical.choice`, `Quot.sound`, `propext`; no target declaration is an axiom, unsafe, or partial.
- All nine exact existing suppliers were reused by hardlink. Their source/object identities and independent historical acceptance are pinned; none was recompiled.

The main bundle is [cell05-scalable-completed-evidence.tar.xz](cell05-scalable-completed-evidence.tar.xz), 1,462,880 bytes, SHA-256 `1fb3fd544b39648bbcf8511ac559ce3ccce98e9fc6ccffc2b164e464046da505`. Local verification is in [LOCAL_EVIDENCE_CHECK.json](LOCAL_EVIDENCE_CHECK.json); the task history is in [TASKS.json](TASKS.json).

## Raw05 current-context kernel addendum

Independent review found that raw05's historical kernel receipt used different object bytes for `ArchivePackedLoader` and `PackedChars`, even though their source bytes were identical. The original run's `full_supplier_kernel_closed` flag and the historical raw05 receipt alone were insufficient to establish raw05 compatibility in the actual pilot context.

A separate check now closes that gap. P1 task `job_85307f4c99e34629a9afc5f202e9df35` executed exactly one command: the original pilot checker path with `--verbose ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05`, using the original `cwd` and `LEAN_PATH`. It exited 0 with **3.748644 seconds of kernel command time** and **4.039031 seconds of MCP task wall time**. The measured kernel process-tree RSS was **708,034,560 bytes**; the MCP-reported peak was **736,960,512 bytes**, with its recorded aggregate-RSS/wait4 peak source. No normal compilation or six-owner command was repeated.

The check preserved the original 111 exported files, original archive, all nine supplier source/object/sidecar inventories, complete run context, and runtime binary fingerprints before and after execution. Local verification confirmed `BEFORE.json == AFTER.json`, the exact target replay log, and both historical archive hashes. The original 18 command receipts and original `RUN.json` remain unmodified.

The current supplier-closure claim therefore joins the original evidence with [raw05-current-context-kernel-addendum.tar.xz](raw05-current-context-kernel-addendum.tar.xz), **11,944 bytes**, SHA-256 `a37b3796dbc51f9a2b103bb851d0f8e3a4aaf4ca0860c6f0c1f5e53cce849d67`. [RAW05_CONTEXT_COMPLETION.json](RAW05_CONTEXT_COMPLETION.json) records this join; [RAW05_CONTEXT_LOCAL_CHECK.json](RAW05_CONTEXT_LOCAL_CHECK.json) records the artifact verification. The original six-owner metrics below exclude this separate supplier compatibility check.

## Measured performance

| New owner suffix | Normal (s) | Kernel (s) | Owned audit (s) | Peak RSS (GiB) | Owned declarations |
|---|---:|---:|---:|---:|---:|
| `Input` | 1.609 | 4.151 | 2.236 | 0.826 | 9 |
| `SimplicesBlock000` | 52.345 | 27.384 | 3.492 | 2.634 | 513 |
| `TypedRows000` | 33.504 | 28.321 | 3.127 | 1.923 | 505 |
| `SimplicesBlock001` | 54.855 | 26.873 | 2.513 | 2.637 | 513 |
| `TypedRows001` | 32.726 | 34.395 | 3.430 | 1.949 | 505 |
| `RowsNode000To001` | 1.817 | 3.934 | 2.722 | 1.312 | 9 |

Summed step time: **319.436 s**. MCP task wall time: **319.856 s**. Maximum Lean process-tree RSS: **2,831,249,408 bytes**; the MCP-reported peak was 2,848,432,128 bytes. Its original `memory_peak_source` is `maximum of sampled aggregate RSS and wait4 per-process high-water RSS`. The configured limits were 6 GiB per Lean process tree, 8,192 MB per MCP job, and 900 seconds per step.

These measurements establish feasibility for the tested cell05 leaves. They are not a cross-cell speedup measurement or a total-runtime estimate. Cell12 has a much larger packed input and still needs its independent start/middle/end stress run.

## Exact mathematical boundary

The input owner proves interfaces for the original packed character list, including its exact length 201,042. The two parser leaves prove original `SourceJson.array` transitions over character offsets 104,497 through 131,386. The binary node composes the transitions with the unchanged accumulator order and fuel offsets. The typed leaves and binary node prove `List.mapM decodeGeometryRow` yields the explicit typed row lists.

For each of rows 0–15, the local shape theorem proves its literal `simplexId`, nine distinct vertex IDs, every listed ID below 28, and ten entries in each factor array. The literal vertex bound has not been transported through a complete decoded geometry array. No determinant, geometric volume, coverage, overlap, or integral theorem follows from this pilot.

The original JSON is 201,042 bytes with SHA-256 `e601ac9ceda569646f06a64f4baddcf9cd405cde1e377a323a238ad4e4681b82`. Original `ArchiveGeometryData05`, packed loader, parser, rational decoder, and schema bytes were retained. Its recovered historical normal/kernel/owned evidence, source, object, and original JSON are in [raw05-supplier-evidence.tar.xz](raw05-supplier-evidence.tar.xz), SHA-256 `f4feab458fec447cb09e4d375102e2ecd3218d88d8336302eafc860d112a60c6`.

## Dependency design and next bounded work

Each typed leaf has two direct project imports: its own parser leaf and `ArchiveRationalChars`. Its project transitive closure contains 11 owners and does not contain a whole-array value or preceding typed prefix. The binary composition imports its two typed leaves. All leaf dependencies remain visible in the final closure.

With eight rows per leaf, the full cell05 row-only design uses seven parser leaves, seven typed leaves, six internal composition nodes, and one input owner: 21 owners. This is a design count, not a completed whole-cell certificate. The six tested owners can be reused unchanged; completing that network needs five further parser leaves, five further typed leaves, and five further binary nodes. Other original top-level fields, vertices, values, faces/facets, terminal array delimiter, and final parser/decoder/shape transport remain necessary.

The existing seven cell12 candidate owners cover rows 0–7, 3296–3303, and 6592–6599 but are source only. Their byte-offset stress tests remain a prerequisite before claiming that the cell05 measurements scale to that input. No mass generation or old-owner recompilation was performed.

The P2 task `e4b55535803d48ed83321044ca6ddd4e` was cancelled while queued and never started. Only this task’s P1 staging, six-owner verification, and read-only evidence export/transport jobs were used. Git HEAD/index and publishing were left to the parent review.
