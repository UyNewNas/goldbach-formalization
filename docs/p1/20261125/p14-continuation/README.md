# P1.4 manuscript-bound continuation — 2026-11-25

## Current scope

P1.4 is **not yet complete**. This branch advances the existing fifth-layer geometry, strict gates, positive refinement schedule and actual owner chain. No closed full-table numerical obligation is replaced by an assumption.

The source reference is the frozen November 6 manuscript at `UyNewNas/chen-imbalanced-semiprimes`, commit `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`, under `paper/release-20261106/en/`. Existing proofs and existing accepted objects are reused. No manuscript-external theorem is introduced.

## Accepted P1.4 owners

Each accepted owner passed normal Lean compilation, independent `leanchecker` replay and the complete environment-owned declaration/type/axiom audit. A source-only header in an unchanged historical file does not override the receipts.

| Owner (prefix `ImbalancedChen.`) | Accepted source commit | Evidence |
| --- | --- | --- |
| `P1FifthGrid400UnitBoxPartition` | `4c2df3b31541d7227b8058b0cce889d9bb84b0d0` | checkpoint01; 26 owned declarations |
| `P1OriginalFifthRawBoxGateSoundness` | `faef01bfb9c4fc5f1395c2db8cff3436eb0f01c8` | checkpoint01; 16 owned declarations |
| `P1OriginalFifthCorrelatedRawBoxGates` | `7a16cea1624c8798c0e8e49114d1f36825dd6f9f` | checkpoint01; 126 owned declarations |
| `P1OriginalFifthCorrelatedDecodedGates` | `869ed92e2a9d36298a6c53aee21e882192f7cf3e` | checkpoint01; 8 owned declarations |
| `P1OriginalFifthFiniteTableRefinementConstructor` | `44453d3b1da4c49a61c6257d66bb0a06e9aad4df` | checkpoint02; 18 owned declarations |
| `P1OriginalFifthPositiveBufferSchedule` | `e5b8f2b22156261e7074d4a0f03e6e250761b82f` | checkpoint02; 28 owned declarations |
| `P1FifthRawKeyThirdOwnerPersistence` | `c26df93b46104bf0fad4565dfb04aaa9131ff5f1` | checkpoint02; 8 owned declarations |
| `P5OriginalCommonRefinedSeedHull` | `540244f58dcfa10e035c12c7196597ee2198f327` | accepted in `bytes-frame-seed`; checkpoint03 export queued |

`P1FifthRawKeyThirdOwnerPersistence` was accepted at `c26df93b46104bf0fad4565dfb04aaa9131ff5f1`: normal compilation, independent kernel replay and complete owned-declaration audit all passed. Its eight owned declarations are archived in checkpoint02. The four rational-to-real casts and missing namespace opening were repaired while retaining the original selector, key checker, thresholds and theorem statements.

The first seven P1.4 owners contain 230 environment-owned declarations in total. The additional seed-hull owner passed normal compilation, independent kernel replay and the full-owned audit in task `job_134bbfdd74a24531aca75e6585577123`; its original source is unchanged. Their gate/table hypotheses remain explicit; these acceptances do not assert whole P1.4 completion. The same task's byte-literal and NPY-frame owners failed normal compilation and are excluded from acceptance.

## Archived evidence and reproducibility

[checkpoint01](evidence/checkpoint-01.tar.xz) contains 502 files, including failed attempts, successful normal logs, kernel command sidecars and logs, full owned declaration inventories and complete type/axiom dumps. It covers four newly accepted P1.4 owners and seven reused owners: 11 owners and 312 owned declarations in total.

[CHECKPOINT01_VERIFIED.json](CHECKPOINT01_VERIFIED.json) separates these groups: 176 declarations in the four P1.4 owners, 108 in six shared P1.5 repairs, and 28 in the previously accepted fourth-layer untruncated integral. It does **not** include the later refinement/schedule stages.

[checkpoint02](evidence/checkpoint-02.tar.xz) and [CHECKPOINT02_VERIFIED.json](CHECKPOINT02_VERIFIED.json) add the three later P1.4 owners and three independently accepted shared owners. The 309-file archive contains 113 owned declarations. Its failed shared owner and source-deployment receipt are retained but excluded from acceptance counts. Across both disjoint checkpoints there are 17 accepted owners and 425 declarations: seven P1.4 owners / 230 declarations, plus ten reused owners / 195 declarations.

Run the offline consistency check from the repository root:

```sh
python3 -B docs/p1/20261125/p14-continuation/verify_evidence.py --checkpoint 01
python3 -B docs/p1/20261125/p14-continuation/verify_evidence.py --checkpoint 02
```

This checks the archive hash and every exported file, current target-source identity, normal/kernel/audit exit receipts, every owned declaration and its axioms, matching source/output fingerprints and preserved original Git states. It does not rerun Lean or the kernel. Compiled object binaries are retained in the P1 compiler, not in this text-receipt archive. Historical commit associations are checked through the source-bound cloud receipts; the offline verifier does not fetch historical Git objects.

The only permitted transitive axioms are `propext`, `Classical.choice` and `Quot.sound`. The audit includes private and generated declarations. No `sorry`, `admit`, new axiom, `native_decide` or `unsafe` was introduced.

## Existing work reused

- [REUSED_QUANTITATIVE_GATE.json](REUSED_QUANTITATIVE_GATE.json) locates the previously accepted quantitative refinement module and its original receipt for 25 owned declarations. It was not rebuilt.
- [REUSED_SHARED_ANALYTIC.json](REUSED_SHARED_ANALYTIC.json) binds six accepted shared analytic repairs to the exact Git blobs from `c57be92d833b429592d684da495d66db800d9dc8`.
- [REUSED_SHARED_ANALYTIC_ROUND02.json](REUSED_SHARED_ANALYTIC_ROUND02.json) binds three further accepted shared owners to `b2fdcf785d32b712b359d254947d97638b2c00ed`. That batch also contained a failed owner, which is not reported as accepted here.
- [REUSED_SHARED_ANALYTIC_ROUND03_04.json](REUSED_SHARED_ANALYTIC_ROUND03_04.json) binds four later accepted shared owners to their original receipts.
- [REUSED_SHARED_ANALYTIC_ROUND05_06.json](REUSED_SHARED_ANALYTIC_ROUND05_06.json) binds seven additional accepted shared owners, including the original fifth untruncated integral. Full-root exports for these rounds retain failed attempts without counting them as acceptance.
- [REUSED_SHARED_ANALYTIC_ROUND07.json](REUSED_SHARED_ANALYTIC_ROUND07.json) binds the accepted actual fifth untruncated domination theorem to its original source and independent audit. The same batch's failed full-mean owner is explicitly excluded.
- `P1OriginalFourthUntruncatedIntegral` already had matching accepted evidence at `9ea714790c06b2270f2028555d9ba774b152d536`; its source is unchanged and its receipt is included in checkpoint01.
- [REUSED_GAMMA_GEOMETRY.json](REUSED_GAMMA_GEOMETRY.json) records matching published acceptance for `P1OriginalThirdGammaMeshSectionBridge` and `P1OriginalThirdGammaValueStability`, including unchanged source/output fingerprints. `FirstCoordinateRise` already has matching compiled objects; no new build was attempted and this check does not claim its separate full-owned receipt.
- [FUTURE_OWNER_INVENTORY.json](FUTURE_OWNER_INVENTORY.json) records the next consumer frontier and identifies the already accepted `P1OriginalFifthJointMeshSchedule`; it is a read-only snapshot, not acceptance of the missing consumers.

No shared owner listed above was recompiled by this continuation. New shared source changes that have not passed their own acceptance are not promoted by these reuse records.

## Execution

`run_stage.py` is a thin, Git-bound caller of the existing pinned normal/kernel/full-owned APIs. It checks the complete published source closure, the pinned Lean/Mathlib runtime and protected roots before execution. Existing accepted dependencies are checked with stock `--no-build` readiness and reused. Successful owners are not included in subsequent retry stages.

The P1 runtime is Lean `4.33.0-rc1` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, with the existing `/workspace/blue-member-build` project. The original `/workspace/goldbach-formalization` checkout is preserved.

`materialize_sources.py` only installs already-published unchanged sources absent from the member build directory. It reuses the existing missing-source installer and serializer. Unknown preimages and symlinks are rejected. Its result is explicitly source deployment, not proof acceptance; it does not alter the validators or compiled objects.

The proof repairs address actual compiler diagnostics: erased case binders, additive argument order, computable/Classical decision-instance conversions, an ambiguous five-dimensional type alias, explicit rational casts and namespace resolution. Public mathematical premises and conclusions are preserved. In particular, the additive-order repair reduced the failed raw-box normal from a 394-second heartbeat timeout to a successful 14-second build without raising its heartbeat budget.

## Remaining P1.4 obligations

The accepted symbolic gates still take the real finite-table check results as explicit inputs. `exists_checked_refinement_with_original_dictionary` retains the actual grid/check data and selected owner. The scheduled owner-image theorem retains its raw zero-check and integer-key checks. These conditional geometry results do not certify all 292,633 archived rows.

The existing analytic chain to `P1OriginalFifthUntruncatedIntegral` and `P1ActualVariableFifthUntruncatedDomination` has now passed on the shared P1.5 branch. The latter's exact source at `089a7f99646fe1921d0cd1450485561e6b52b5e4` was accepted by task `job_ffc41fd9dd994612a23c21ffe06334ce` and is reused here. The actual unit-box gain decomposition and archive consumers must still be accepted on the resulting source closure.

The actual table/owner endpoint must still retain original NPY/typed-row identity and order, distinct keys, one common refinement, inherited fourth cap, both strict own-cube gates, dynamic third/fourth/fifth history and licensing on the same instance, signed gains and both reserves.

The original full NPY-to-typed association source already exists at `docs/source-only/20261102-certificates-l/original_npy_kernel/P1HistoricalFifthOriginalNpyKernel.lean`, with its registered original binary fixture. It supplies closed source bodies for `original_complete_ordered_columns` and `original_complete_parse`, but has no accepted execution yet. Reuse this existing source when its parents are ready. A typed encode/decode roundtrip or compilation of the generic byte reader is not the actual original-file association check.

The full stored-parent replacement obligation remains the existing closed equality

```lean
∀ i : ArchiveIndex,
  (storedAt i).newQ80 =
    max (storedAt i).oldQ80
      (∑ c : ChildIndex, originalExactFloor (originalFields (archiveRow i) c))
```

It uses the original 3/4 logarithm rounding and all 64 children. The existing row-5 pilot in `docs/p1/20261124/batch4-repairs/ParentExactRow5Probe.lean` is to be reused when its imports are ready. The first two rows or source-index chunk checks do not discharge the complete floor obligation. The existing whole-floor/integral terminal must then receive normal, kernel and complete owned-declaration acceptance before P1.4 can be marked complete.
