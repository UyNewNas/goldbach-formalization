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
| `P1OriginalFifthFiniteTableRefinementConstructor` | `44453d3b1da4c49a61c6257d66bb0a06e9aad4df` | cloud stage `refinement`; later checkpoint pending |
| `P1OriginalFifthPositiveBufferSchedule` | `e5b8f2b22156261e7074d4a0f03e6e250761b82f` | cloud stage `schedule-retry`; later checkpoint pending |

The current `P1FifthRawKeyThirdOwnerPersistence` repair is a **candidate pending acceptance**. Its five observed failures were four rational-to-real casts and a missing namespace opening. Its original selector, key checker, thresholds and theorem statements are retained.

## Archived evidence and reproducibility

[checkpoint01](evidence/checkpoint-01.tar.xz) contains 502 files, including failed attempts, successful normal logs, kernel command sidecars and logs, full owned declaration inventories and complete type/axiom dumps. It covers four newly accepted P1.4 owners and seven reused owners: 11 owners and 312 owned declarations in total.

[CHECKPOINT01_VERIFIED.json](CHECKPOINT01_VERIFIED.json) separates these groups: 176 declarations in the four P1.4 owners, 108 in six shared P1.5 repairs, and 28 in the previously accepted fourth-layer untruncated integral. It does **not** include the later refinement/schedule stages.

Run the offline consistency check from the repository root:

```sh
python3 -B docs/p1/20261125/p14-continuation/verify_evidence.py
```

This checks the archive hash and every exported file, current target-source identity, normal/kernel/audit exit receipts, every owned declaration and its axioms, matching source/output fingerprints and preserved original Git states. It does not rerun Lean or the kernel. Compiled object binaries are retained in the P1 compiler, not in this text-receipt archive. Historical commit associations are checked through the source-bound cloud receipts; the offline verifier does not fetch historical Git objects.

The only permitted transitive axioms are `propext`, `Classical.choice` and `Quot.sound`. The audit includes private and generated declarations. No `sorry`, `admit`, new axiom, `native_decide` or `unsafe` was introduced.

## Existing work reused

- [REUSED_QUANTITATIVE_GATE.json](REUSED_QUANTITATIVE_GATE.json) locates the previously accepted quantitative refinement module and its original 25-owner-declaration receipt. It was not rebuilt.
- [REUSED_SHARED_ANALYTIC.json](REUSED_SHARED_ANALYTIC.json) binds six accepted shared analytic repairs to the exact Git blobs from `c57be92d833b429592d684da495d66db800d9dc8`.
- [REUSED_SHARED_ANALYTIC_ROUND02.json](REUSED_SHARED_ANALYTIC_ROUND02.json) binds three further accepted shared owners to `b2fdcf785d32b712b359d254947d97638b2c00ed`. That batch also contained a failed owner, which is not reported as accepted here.
- `P1OriginalFourthUntruncatedIntegral` already had matching accepted evidence at `9ea714790c06b2270f2028555d9ba774b152d536`; its source is unchanged and its receipt is included in checkpoint01.

No shared owner listed above was recompiled by this continuation. New shared source changes that have not passed their own acceptance are not promoted by these reuse records.

## Execution

`run_stage.py` is a thin, Git-bound caller of the existing pinned normal/kernel/full-owned APIs. It checks the complete published source closure, the pinned Lean/Mathlib runtime and protected roots before execution. Existing accepted dependencies are checked with stock `--no-build` readiness and reused. Successful owners are not included in subsequent retry stages.

The P1 runtime is Lean `4.33.0-rc1` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, with the existing `/workspace/blue-member-build` project. The original `/workspace/goldbach-formalization` checkout is preserved.

`materialize_sources.py` only installs already-published unchanged sources absent from the member build directory. It reuses the existing missing-source installer and serializer. Unknown preimages and symlinks are rejected. Its result is explicitly source deployment, not proof acceptance; it does not alter the validators or compiled objects.

The proof repairs address actual compiler diagnostics: erased case binders, additive argument order, computable/Classical decision-instance conversions, an ambiguous five-dimensional type alias, explicit rational casts and namespace resolution. Public mathematical premises and conclusions are preserved. In particular, the additive-order repair reduced the failed raw-box normal from a 394-second heartbeat timeout to a successful 14-second build without raising its heartbeat budget.

## Remaining P1.4 obligations

The accepted symbolic gates still take the real finite-table check results as explicit inputs. `exists_checked_refinement_with_original_dictionary` retains the actual grid/check data and selected owner. The scheduled owner-image theorem retains its raw zero-check and integer-key checks. These conditional geometry results do not certify all 292,633 archived rows.

The existing analytic chain to `P1OriginalFifthUntruncatedIntegral` and `P1ActualVariableFifthUntruncatedDomination` is being advanced on the shared P1.5 branch and is reused as it is accepted. The actual unit-box gain decomposition and archive consumers must be accepted on the resulting source closure.

The actual table/owner endpoint must still retain original NPY/typed-row identity and order, distinct keys, one common refinement, inherited fourth cap, both strict own-cube gates, dynamic third/fourth/fifth history and licensing on the same instance, signed gains and both reserves.

The full stored-parent replacement obligation remains the existing closed equality

```lean
∀ i : ArchiveIndex,
  (storedAt i).newQ80 =
    max (storedAt i).oldQ80
      (∑ c : ChildIndex, originalExactFloor (originalFields (archiveRow i) c))
```

It uses the original 3/4 logarithm rounding and all 64 children. The existing row-5 pilot in `docs/p1/20261124/batch4-repairs/ParentExactRow5Probe.lean` is to be reused when its imports are ready. The first two rows or source-index chunk checks do not discharge the complete floor obligation. The existing whole-floor/integral terminal must then receive normal, kernel and complete owned-declaration acceptance before P1.4 can be marked complete.
