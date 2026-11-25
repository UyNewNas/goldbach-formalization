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
| `P5OriginalCommonRefinedSeedHull` | `540244f58dcfa10e035c12c7196597ee2198f327` | checkpoint03; 18 owned declarations |
| `P1HistoricalFifthOriginalByteLiteral` | `c6d6d5eed2b4a4c5a288645864e781716c7e5771` | checkpoint04; 66 owned declarations |
| `P1HistoricalFifthNpyFrame` | `c6d6d5eed2b4a4c5a288645864e781716c7e5771` | checkpoint04; 33 owned declarations |
| `P1FifthUnitBoxGainDecomposition` | `4d294de6b2a3128a6fb281426e4f204a8514beaa` | checkpoint04; 18 owned declarations |
| `P1OriginalFifthActualOwnerGateCrossing` | `4d294de6b2a3128a6fb281426e4f204a8514beaa` | checkpoint04; 13 owned declarations |
| `P1HistoricalFifthTypedArchiveShape` | `4d294de6b2a3128a6fb281426e4f204a8514beaa` | checkpoint04; 176 owned declarations |
| `P1FifthUnitBoxLiteralGainLower` | `8237d0b698ca01153a7e2823510cf67148083c0a` | checkpoint05; 14 owned declarations |
| `P1OriginalFifthMovingMeshFubiniBridge` | `8237d0b698ca01153a7e2823510cf67148083c0a` | checkpoint05; 17 owned declarations |
| `P1OriginalFifthLiteralKernelModulus` | `8237d0b698ca01153a7e2823510cf67148083c0a` | checkpoint05; 36 owned declarations |
| `P1HistoricalFifthTypedArchiveRangeCore` | `61566a18871e26b80cced0a4408944294d793071` | checkpoint05; 2 owned declarations |
| `P1HistoricalFifthTypedArchiveRangeBlock000` | `61566a18871e26b80cced0a4408944294d793071` | checkpoint05; 2 owned declarations |
| `P1FifthMask5RawOwnerLicence` | `c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b` | `owner-license-retry`; checkpoint06 pending |
| `P1FifthMask6RawOwnerLicence` | `c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b` | `owner-license-retry`; checkpoint06 pending |
| `P1FifthPositivePartActualOwner` | `c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b` | `literal-positive-retry`; checkpoint06 pending |
| `P1FifthCheckedUnitBoxWholeGain` | `c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b` | `literal-positive-retry`; checkpoint06 pending |
| `P1HistoricalFifthNpyPositionalSemantics` | `c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b` | `npy-positional-retry`; checkpoint06 pending |
| `P1OriginalFifthActualOwnerCrossingVolume` | `a700772dbddaa09df497590c7d1b54d6e488f812` | `owner-fibre-volume-retry`; checkpoint06 pending |
| `P1HistoricalFifthTypedArchiveRangeBlocks001010` | `5ba405bc08aaef020868399aa62a429ca4281eda` | `typed-range-blocks-001-010`; archive pending |
| `P5OldFifthFrozenUpperSurrogate` | `8682bf05456060c0677bdddb210df38f33229817` | `frozen-upper-surrogate`; archive pending |
| `P1HistoricalFifthTypedBaseGeometryCore` | `e4dfe229579714b69c302e667d88649a14b58a0c` | `typed-base-core`; archive pending |
| `P1HistoricalFifthTypedBaseGeometryBlock000` | `e4dfe229579714b69c302e667d88649a14b58a0c` | `typed-base-block000`; archive pending |

`P1FifthRawKeyThirdOwnerPersistence` was accepted at `c26df93b46104bf0fad4565dfb04aaa9131ff5f1`: normal compilation, independent kernel replay and complete owned-declaration audit all passed. Its eight owned declarations are archived in checkpoint02. The four rational-to-real casts and missing namespace opening were repaired while retaining the original selector, key checker, thresholds and theorem statements.

The first eight P1.4 owners contain 248 environment-owned declarations in total and are covered by checkpoints01–03. The seed-hull owner's original source is unchanged. In the original `bytes-frame-seed` task the byte-literal and NPY-frame owners failed normal compilation; their repaired sources subsequently passed normal compilation, independent kernel replay and the full-owned audit in the `bytes-frame-retry` stage of task `job_72fd5697ae854699b4a40184a3aeb5cf`. The generic reader and frame theorems do not execute the actual complete original-file association. These acceptances do not assert whole P1.4 completion.

## Archived evidence and reproducibility

[checkpoint01](evidence/checkpoint-01.tar.xz) contains 502 files, including failed attempts, successful normal logs, kernel command sidecars and logs, full owned declaration inventories and complete type/axiom dumps. It covers four newly accepted P1.4 owners and seven reused owners: 11 owners and 312 owned declarations in total.

[CHECKPOINT01_VERIFIED.json](CHECKPOINT01_VERIFIED.json) separates these groups: 176 declarations in the four P1.4 owners, 108 in six shared P1.5 repairs, and 28 in the previously accepted fourth-layer untruncated integral. It does **not** include the later refinement/schedule stages.

[checkpoint02](evidence/checkpoint-02.tar.xz) and [CHECKPOINT02_VERIFIED.json](CHECKPOINT02_VERIFIED.json) add the three later P1.4 owners and three independently accepted shared owners. The 309-file archive contains 113 owned declarations. Its failed shared owner and source-deployment receipt are retained but excluded from acceptance counts. Across both disjoint checkpoints there are 17 accepted owners and 425 declarations: seven P1.4 owners / 230 declarations, plus ten reused owners / 195 declarations.

[checkpoint03](evidence/checkpoint-03.tar.xz) and [CHECKPOINT03_VERIFIED.json](CHECKPOINT03_VERIFIED.json) add the seed-hull owner and twelve accepted shared owners from rounds03–07. All 725 exported files are hash-checked, with no omitted files. The archive contains 13 accepted owners / 197 owned declarations. Its full roots also preserve the failed ByteLiteral, NpyFrame and FullMean attempts without promoting them to acceptance. The three disjoint checkpoints total 30 owners / 622 declarations: eight P1.4 owners / 248 declarations and 22 reused owners / 374 declarations. Later `bytes-frame-retry` acceptance is outside these fixed archive roots.

[checkpoint04](evidence/checkpoint-04.tar.xz) and [CHECKPOINT04_VERIFIED.json](CHECKPOINT04_VERIFIED.json) add five P1.4 owners and the reused FullMean owner from round08. All 386 exported files are checked, including original failed attempts and the cancelled Range partial history. The six accepted owners contain 310 owned declarations. The fixed ByteLiteral/NPY-frame audit lane contains both owners and all 99 declarations; their separate source, normal and kernel receipts are checked. Checkpoints01–04 total 36 distinct owners / 932 owned declarations: 13 P1.4 owners / 554 declarations and 23 reused owners / 378 declarations. The retained23 review adds no duplicate acceptance.

[checkpoint05](evidence/checkpoint-05.tar.xz) and [CHECKPOINT05_VERIFIED.json](CHECKPOINT05_VERIFIED.json) add five P1.4 owners from the completed `8237` and `61566` pipelines. All 295 exported files are checked. These owners contain 71 owned declarations, including 66 public declarations. The exact LiteralGainLower/FubiniBridge audit lane contains both owners and all 31 declarations; its two separate normal and kernel commands are checked. The eight failed normal attempts and eight held stages remain recorded without acceptance. Across checkpoints01–05 there are 41 distinct owners / 1,003 owned declarations / 954 public declarations: 18 P1.4 owners / 625 owned declarations and 23 reused owners / 378 owned declarations. Later C490/A700 acceptances listed above are outside these five archives and await checkpoint06. These module counts do not measure a percentage of whole P1.4 completion.

Run the offline consistency check from the repository root:

```sh
python3 -B docs/p1/20261125/p14-continuation/verify_evidence.py --checkpoint 01
python3 -B docs/p1/20261125/p14-continuation/verify_evidence.py --checkpoint 02
python3 -B docs/p1/20261125/p14-continuation/verify_evidence.py --checkpoint 03
python3 -B docs/p1/20261125/p14-continuation/verify_evidence.py --checkpoint 04
python3 -B docs/p1/20261125/p14-continuation/verify_evidence.py --checkpoint 05
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
- [REUSED_NUMERIC_ANCESTORS.json](REUSED_NUMERIC_ANCESTORS.json) locates the existing full-owned/kernel receipts for the four previously stale Wire/row5 ancestors, with current target-source byte matches. No ancestor is recompiled by this inspection, no lane total is treated as an individual declaration count, and current runtime closure readiness remains a separate gate. The existing row5 probe is retained verbatim.
- [REUSED_PARENT_DIAGNOSTIC.json](REUSED_PARENT_DIAGNOSTIC.json) locates the existing exact integer/Fraction diagnostic for eight selected original parents and all 512 corresponding children. All eleven bound source files match the recorded Git source. The original 3/4 max equality holds for those eight samples, including the complete 64-child row5 case. The diagnostic was not rerun; it is neither Lean acceptance nor a check of the complete 292,633-parent table.
- [FUTURE_NUMERIC_CONTINUATION.json](FUTURE_NUMERIC_CONTINUATION.json) records the existing post-Chord consumers and separate named-parent side branch. Its nineteen listed modules remain subject to their original readiness and acceptance gates. The existing `LogPrimeBoxIntegral` dependency fingerprint is reused without promoting it to a new independent owner audit.

No shared owner listed above was recompiled by this continuation. New shared source changes that have not passed their own acceptance are not promoted by these reuse records.

## Execution

`run_stage.py` is a thin, Git-bound caller of the existing pinned normal/kernel/full-owned APIs. It checks the complete published source closure, the pinned Lean/Mathlib runtime and protected roots before execution. Existing accepted dependencies are checked with stock `--no-build` readiness and reused. Successful owners are not included in subsequent retry stages.

The P1 runtime is Lean `4.33.0-rc1` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, with the existing `/workspace/blue-member-build` project. The original `/workspace/goldbach-formalization` checkout is preserved.

`materialize_sources.py` only installs already-published unchanged sources absent from the member build directory. It reuses the existing missing-source installer and serializer. Unknown preimages and symlinks are rejected. Its result is explicitly source deployment, not proof acceptance; it does not alter the validators or compiled objects.

The proof repairs address actual compiler diagnostics: erased case binders, additive argument order, computable/Classical decision-instance conversions, an ambiguous five-dimensional type alias, explicit rational casts and namespace resolution. Public mathematical premises and conclusions are preserved. In particular, the additive-order repair reduced the failed raw-box normal from a 394-second heartbeat timeout to a successful 14-second build without raising its heartbeat budget.

## Remaining P1.4 obligations

The accepted symbolic gates still take the real finite-table check results as explicit inputs. `exists_checked_refinement_with_original_dictionary` retains the actual grid/check data and selected owner. The scheduled owner-image theorem retains its raw zero-check and integer-key checks. These conditional geometry results do not certify all 292,633 archived rows.

The existing analytic chain to `P1OriginalFifthUntruncatedIntegral` and `P1ActualVariableFifthUntruncatedDomination` has now passed on the shared P1.5 branch. The latter's exact source at `089a7f99646fe1921d0cd1450485561e6b52b5e4` was accepted by task `job_ffc41fd9dd994612a23c21ffe06334ce` and is reused here. The actual unit-box gain decomposition, actual-owner gate crossing, and typed archive shape were accepted at `4d294de6b2a3128a6fb281426e4f204a8514beaa` by task `job_1cea508c1b3745b694cb5ff810334b66` using normal compilation, independent kernel checking and the complete owned-declaration audit. Their downstream consumers remain separate checks.

The actual table/owner endpoint must still retain original NPY/typed-row identity and order, distinct keys, one common refinement, inherited fourth cap, both strict own-cube gates, dynamic third/fourth/fifth history and licensing on the same instance, signed gains and both reserves.

The original full NPY-to-typed association source already exists at `docs/source-only/20261102-certificates-l/original_npy_kernel/P1HistoricalFifthOriginalNpyKernel.lean`, with its registered original binary fixture. It supplies closed source bodies for `original_complete_ordered_columns` and `original_complete_parse`, but has no accepted execution yet. [REUSED_ORIGINAL_NPY_SOURCE.json](REUSED_ORIGINAL_NPY_SOURCE.json) records the byte-identical production copies of this existing source and its two positional/association parents, together with the original fixture's exact Git blob at `ImbalancedChen/provenance/original-fifth/cells.npy`. This is source reuse, not new mathematical acceptance. The binary include requires exact input identity before and after compilation in addition to the existing Lean-source checks. A typed encode/decode roundtrip or compilation of the generic byte reader is not the actual original-file association check.

The full stored-parent replacement obligation remains the existing closed equality

```lean
∀ i : ArchiveIndex,
  (storedAt i).newQ80 =
    max (storedAt i).oldQ80
      (∑ c : ChildIndex, originalExactFloor (originalFields (archiveRow i) c))
```

It uses the original 3/4 logarithm rounding and all 64 children. The existing row-5 pilot in `docs/p1/20261124/batch4-repairs/ParentExactRow5Probe.lean` is to be reused when its imports are ready. The first two rows or source-index chunk checks do not discharge the complete floor obligation. The existing whole-floor/integral terminal must then receive normal, kernel and complete owned-declaration acceptance before P1.4 can be marked complete.

**Completion boundary — `SOURCE_LOCATED_ACCEPTANCE_UNVERIFIED`.** `P5OriginalFullFifthFloorIntegral` is the numerical/integral terminal, not the complete P1.4 endpoint. The existing declarations below locate the separate actual-data, gate, same-owner and Full87 history/license checks and their downstream bindings. This source inspection changes no acceptance count or evidence status; matching existing receipts must be reused. P4A's full All22 integral payments and global coefficient estimates remain cross-node consumers, not a requirement to reimplement the entire P4A proof in this task. The protected `P1OriginalFinalPolicy*` and `P1OriginalCompleteFormalProof` roots are binding references only and must remain unchanged.

- **Actual input identity.** Check `P1HistoricalFifthOriginalNpyKernel.original_complete_parse` and its ordered ten-column/byte association against the independent original fixture, together with `P1HistoricalFifthTypedKeyPartition.actual_typed_keys_nodup` and `P1HistoricalFifthTypedBaseGeometry.licensedIndices_eq_univ`. The actual fourth input is supplied by `P5OriginalFourthFifthSourceInputs.originalFourth_wire_source`, `originalRows4` and `originalAdmission4`. Generic parsing or typed base geometry alone does not supply the strict fifth gates.
- **Actual gates and reserve schedule.** `P5HistoricalActualReserve64Schedule.exists_full_actual_reserve64_paid_schedule` supplies one actual `e,q` with both zero/positive gate filters, canonical history and the full child reserve controlled; its conclusions include `licensedOwners = adoptedOwners` for every archive index. Check this closed supplier and `exists_original_density_reserve64_payment` separately from conditional refinement lemmas and the full stored-floor endpoint. The fifth density allocation does not pay the separate compiler reserve in the downstream coefficient ledger.
- **Same-instance history and licenses.** `P1HistoricalFifthCommonPolicyInputs.actual_archive_common_fifth_test` uses the dynamic fourth ancestor of the same `sourceData`; `P5OriginalFourthFifthSourceInputs.heldData` instantiates the original banks but does not itself assert Full87 realization. The existing public suppliers are `P4AOriginalFull87ActualCommonHistory.exists_original_common_history`, `P4AOriginalFull87ActualSourceMembership.exists_cofinal_original_source_membership` and `P4AOriginalFull87LicensedSixthRealization.exists_shared_licensed_sixth_schedule`. Their schedule conclusions supply actual history, occurrence membership and licenses; local lemmas that assume `RealizedHistory` or `ArchiveLicenses` are not substitutes.
- **Existing final-consumer binding.** Follow `P4AOriginalNewFifthUnion.data` and `P4AOriginalFull87UnionHistory` into `P4AOriginalOrderedThirdFullPolicy.policy_on_old_owner` and the actual `P4AOriginalFiniteAll22RawLedger.finalPolicy`. The owner equality retains its supported-history and cutoff conditions. The existing quantitative consumers `P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect` and `P4AOriginalFull87UpperDispatch.lowerEighth_eq_paid_source` identify the same-instance early and Full87 terms. Verify these bindings against existing evidence without turning P1.4 acceptance into fresh implementation or blanket revalidation of P4A's All22 integrals or global coefficient budget.

The final shared analytic supplier `P1ActualVariableFifthFullMean` is now reused from accepted source `29295f6a7196c523b525104f864da20035cc15d9`, with four owned declarations and its original receipts recorded in [REUSED_SHARED_ANALYTIC_ROUND08.json](REUSED_SHARED_ANALYTIC_ROUND08.json). It is not recompiled here. This extends the shared analytic inputs and does not close P1.4.

### Range computation and original-input continuation

Task `job_1cea508c1b3745b694cb5ff810334b66` was deliberately stopped after 1843.106 seconds while the first full `TypedArchiveRange` normal compilation was still running. This is a resource-scheduling interruption, not a reported Lean proof failure or a mathematical counterexample. The earlier completed UnitBoxGain, ActualOwnerGateCrossing and TypedArchiveShape stage receipts remain individually accepted. Range is not accepted and no missing final pipeline/result/Git receipt is reconstructed. The original terminal task responses are retained as explicitly labelled local observer attachments under `evidence/checkpoint-04-observations/`.

The existing `TypedValid` definition and constructive instance are factored unchanged into `P1HistoricalFifthTypedArchiveRangeCore`. The existing block000 closed obligation is factored into `P1HistoricalFifthTypedArchiveRangeBlock000`, retaining its exact statement, actual data and resource limits, and requesting `decide +kernel`. Both owners were accepted by task `job_7b50045d5ba442e593de467f321eb031` at `61566a18871e26b80cced0a4408944294d793071`. Block000 normal compilation took 32.866 seconds and its kernel/full-owned audit stage took 52.424 seconds. The remaining 142 existing closed obligations are moved, with their statements unchanged, into 15 bounded owner groups; only their proof command changes to the accepted kernel-reduction form. The full range module imports all 143 obligations and retains the complete original aggregation and full-table conclusions verbatim. These further groups and the full aggregation still require acceptance; block000 does not stand for the full table or the independent original-file association.

The separate `LowerKeyBounds` check still supplies the original five-coordinate bounds `1..77`. Its unchanged definition and instance are extracted into `P1HistoricalFifthTypedBaseGeometryCore`, and its original block000 obligation into `P1HistoricalFifthTypedBaseGeometryBlock000` with the same resource limits and `decide +kernel`. Both owners passed normal/kernel/full-owned acceptance at `e4dfe229579714b69c302e667d88649a14b58a0c`; block000 normal compilation took 16.983 seconds and its audit stage 42.551 seconds. The remaining 142 existing obligations are now separated into fifteen bounded groups with the same statements, data references and options; only `decide` changes to `decide +kernel`. [TYPED_BASE_FACTORING.json](TYPED_BASE_FACTORING.json) records the complete mapping and the distinct original runtime and extraction preimages. The main module imports all 143 obligations and retains the entire `rows_lower_key_bounds` aggregation and downstream conclusions byte for byte. The fifteen new groups and main aggregation still require acceptance. These bounded suppliers establish neither original-file identity nor strict owner licenses.

`run_original_npy.py` and `ORIGINAL_NPY_INPUT_MANIFEST.json` add a fixed, single-consumer data-input binding around the unchanged normal/kernel/full-owned APIs. They pin the retained original `cells.npy` by canonical path, bytes, SHA256 and Git blob before/after normal compilation and after the audit. Existing objects without the original compilation-time data records are held. Worker completion remains pending until the serializer exits successfully and the original Git before/after states match; only the outer attempt can then issue `DATA_BOUND_ACCEPTANCE.json`. The adapter has received static review but has not executed the original NPY proof, and supplies no mathematical acceptance by itself.
