# New source checkpoint 002 — 2026-10-30 10:33 UTC

Parent remote checkpoint `fe8b806f1cd52dadaff4e501624f647a9c3f7e94` preserved the paired certificate split. This checkpoint preserves the complete new Prefix128 split (18 files: 1 changed original + 17 new modules).

Through ci4/batch009, **41 modules / 2474 own declarations** independently passed genuine Lake builds using the original CI guard `-t0 -j2 -M4096`, actual Lake-generated setup JSON and full `-o/-i/-c/--setup/--json`, complete-own-declaration transitive axiom audit and exact kernel replay. Cached Lake jobs are not counted as fresh project compilations. Both previously failing PairedV2Batch4To64 and PairedV2Batch64To128 targets passed in this selected scope, including their full33-project closure. Three Prefix4/Prefix64 prerequisites also passed.

Of the new Prefix128 split only Data and Keys000..032 (four leaves) are accepted here. The other12 leaves and final Prefix128 aggregator are **not yet accepted** at this checkpoint. All127 edges are statically covered once with left indices0..126/right1..127; original API,512-grid encoding and every following theorem body are preserved. No full-mask geometric union or unconditional hLower/hUpper theorem is asserted.

Fixed Lean4.33.0-rc1 and all11 dependency pins are unchanged/tracked-clean. Native replay still has sampled aggregate RSS6144MiB; each source has a combined1800second budget, run16200second budget, shared serialcompiler lock. Sampling can miss transient peaks and is not a kernel hard cap. This is a selected genuine-Lake4GiB experiment, **not a complete CI workflow success**. Wiener/ZetaBounds/B8Finite and earlier fixed external budget blockers are not patched or claimed solved.

Full new source, execution receipts, independent summaries, local validation runtime and hashes are saved. Detailed stage logs and large full-source snapshots remain local, not claimed remotely preserved by this intentionally small source checkpoint. Their hashes remain in receipts; rebind absolute runtime paths and rerun fresh tool tests for reproduction. No paused historical rejected upload or repackaged rejected evidence is included or claimed completed.
