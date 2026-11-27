# P1.4 resource diagnostics: original failures, no new acceptance

This directory preserves the already recovered Indexed and Key diagnostics using the explicit 33-file payload allowlist in `ALLOWLIST.json`. `MANIFEST.json` pins every delivered file except itself. The payload bytes were copied unchanged; `PACKAGING_CHECK.json` records offline transport reconstruction and original-file hash verification. No remote read, data analysis, Lean command, Git operation, source repair, guard or validator change occurred while packaging.

## Original outcomes

| Case | Original run | Evidence classification | Acceptance |
|---|---|---|---|
| Indexed | job_25b5b644a3a94fb3baca594930540942 | Parent-reported memory_exceeded / exit-9; complete saved partial normal log has no target line; original normal-command and RESULT were not written at the observed paths | No normal/kernel/full-owned acceptance |
| Key | job_d80d8ffe57474cebae53aa364389689e | Completed normal failure, exit1, kernel excessive memory at Certificate.lean:16:2; complete original normal-command, RESULT and pipeline retained | accepted_owners=[]; no new acceptance |

The separate read-only export tasks succeeded. Their successful transport status is not compilation success. All parent-reported outer-run metrics remain explicitly distinguished from independently recovered original file contents.

## Read first

- [Indexed review](indexed/INDEXED_RESOURCE_REVIEW.md) and [structured review](indexed/INDEXED_RESOURCE_REVIEW.json).
- [Key review](key/KEY_MEMORY_REVIEW.md) and [structured review](key/KEY_MEMORY_REVIEW.json).
- [Key data analysis](key/KEY_BLOCK_DATA_ANALYSIS.json): pure Python observations about the exact complete source, not Lean proof or NPY authenticity.
- [Original analysis script](key/analyze_key_blocks.py): preserved historical bytes; it was not re-run to make this package.

Both cases retain the complete paginated transport in `transport/`, reconstructed stdout bytes, and all originals actually returned by those reads. Indexed's four observed absent paths are recorded without synthesizing files. The probed `runs/attempt-00001/BINDING.json` absence does not establish absence of the stage-root BINDING.

Original JSON files retain historical absolute `local_path` values unchanged. Use MANIFEST's `source_path` → `path` mapping to locate their packaged copies. The source-binding provenance is preserved in `provenance/D14_SOURCE_STATIC_REVIEW.json`; the original analysis script's absolute scratch paths were deliberately not rewritten. The accepted Range result under `key/reused/` is old reused evidence and grants zero additional credit.

The Key report discusses an unimplemented inverse-index certificate design. This package contains no generated lookup table and no new Lean proof. The only `.lean` payload is the exact original Indexed source returned by its read-only diagnostic task. The 1106 manuscript source and existing Core/Shape/Range proofs stay at their existing repository paths and are referenced by hash rather than copied or rechecked.

`whole_P1_4_complete=false` throughout. This is a failure-evidence package, not a new normal/kernel/full-owned receipt and not a board status update.
