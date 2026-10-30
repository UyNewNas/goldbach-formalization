# New restart checkpoint — 2026-10-30 10:14 UTC

Fresh reconstruction from published `3c94ec71e13d038ae661138dac1037116615a20f`; not restoration or completion of an earlier rejected publication.

All 26 current paired-certificate source files are backed up. 132 moved declarations, and all 158 original named declarations, retain statements and proof bodies. The two original batch APIs are retained through imports. No fixed external dependency changed.

Eight project modules (278 own declarations) passed fresh compile, full-own-declaration transitive axiom audit (only `propext`, `Classical.choice`, `Quot.sound`), exact target kernel replay, and independent receipt review. Six are prerequisites, two are new 8-row leaves. The other 24 changed/new targets are **not yet accepted**; see status.json. Full-root CI and unconditional hLower/hUpper closure are not established.

Runtime: fixed Lean 4.33.0-rc1, all11 manifest pins tracked-clean; local `-t0 -j2 -M6144`, full `-o/-i/-c/--json`; sampled aggregate RSS6144MiB (not hard kernel cap), per-source combined1800seconds, run16200seconds, serial compiler lock. Exact replay only checks target-own declarations against imported environment. This is **not** CI4GiB or Lake --setup equivalence.

This intentionally small source checkpoint includes full source files, per-batch execution receipts, independent review summaries, runtime source and hashes. Large before/after source manifests and detailed stage logs remain in the current local evidence directory and are NOT represented as remotely preserved here. Their hashes are in receipts. Runtime scripts retain original absolute paths; rebind paths for a different checkout and rerun fresh runtime tests before reuse. Eight replay tests and nine RSS supervisor cases passed in this new restart.

No previously rejected evidence blob or repackaged version is included. No claim is made that the separate paused historical upload completed.
