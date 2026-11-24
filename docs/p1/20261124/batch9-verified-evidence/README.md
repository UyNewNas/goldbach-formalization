# Batch9: actual cloud results

Execution commit `e44e941df0a4cdf126fc0a0c41df3abd7637d1e8`; task `job_b8aa92b8bb3249a7bbeb0f9c4f323e09`. One outer task ran two existing serialized lanes concurrently. It finished with exit 1 after 1266.493 seconds; sampled peak memory was 21,231,366,144 bytes.

The previous 11 normal passes completed independent named-kernel replay and full environment-owned declaration audit: **11 modules, 386 owned declarations, 357 public declarations**, with only the three standard axioms. These are the actual original `e2090abc…` acceptance receipt in the archive.

This round produced **12 new normal passes and 17 ordinary failures** from 29 requested ordinary targets. `SUMMARY.json` gives the exact sets. Normal success remains separate from kernel and all-owned acceptance. Higher failed after 813.015 seconds with an interpreter `memory_exception` (Lean exit 134); no mathematical goal failure was reported, and no Higher acceptance is claimed. Existing successful Low/Middle probes were reused, not repeated.

Both original four-root and signed-wire no-build checks still exit 3. All four original final theorem sources and the original dirty cloud Git worktree were preserved. Full P1 is incomplete.

`verification.tar.xz` is the byte-exact cloud export (379216 bytes, SHA256 `28ca4ce205f94cabcaf82185a1c777cbeef5fe105081107472db6b47b09a2e8d`). All 230 payload members were verified against the original `ARCHIVE_FILES.json`; its SHA256 is `4dd83276fad72ced80ac69a802fffa283e1d6bd6d60ff2b4f63cf7b5ac8c8707`. It retains complete original command logs, runtime/lane receipts, source context, failure blocks, Higher installation/probe provenance, and the complete audit11 receipt and declaration inventory.
