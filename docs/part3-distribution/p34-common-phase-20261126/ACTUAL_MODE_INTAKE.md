# P3.4 ACTUAL-mode endpoint and energy intake

## Decision

Use a 12-project-module Mathlib-only gate for the five existing ACTUAL-mode specializations. Move eight existing provider declaration blocks into two narrow modules and the five existing specialization blocks into one module. Retain their complete qualified names and declaration bytes. With the two modules from the current common-phase move, the union has 14 project modules. This is first acceptance of the five specialization declarations and compatibility verification of the moved providers. The P3.2 arithmetic, Poisson, chart, spectral and positive-count arguments stay in their existing modules.

This is a read-only source and artifact audit at P3.4 base `b945f39a1e355ff4fcca9865ab59ffc97f2172c0`. The only output is this report. I did not run Lean, Lake, a cloud job, a fetch, or a Git mutation. The two new common-phase module names and imports below describe the currently executing migration.

## 1. Exact donor blocks

Each path below starts in the repository root. Hashes cover the bytes from the first declaration token through the last line of the declaration, including internal line breaks and indentation, with no final line feed. Copy leading documentation with the declaration where present and reproduce the namespaces, scope and local instance setup separately. All eight provider blocks compare byte-for-byte with P3.2 verified source `34201be0ca95d465336119fce24b7681c17ab0c6`.

| Source path and line | Declaration under `ImbalancedChen.Part3` | Exact block SHA-256 |
| --- | --- | --- |
| `ImbalancedChen/Part3DistributionTargets.lean:37` | `MediumAtom` | `493b5957494dcc6e54da13ac9b8da4e3b62d8d8578f4c76e0f8637b810d462cb` |
| `ImbalancedChen/Part3DistributionTargets.lean:64` | `factorCarrier` | `f16adebb0a0970d075687815f9208163164354893fda0e4ec4d2de10fd05b2a8` |
| `ImbalancedChen/Part3SharedFirstFactorSmallCoreSmoothFrequency.lean:28` | `MediumAtom.sharedSmoothFrequencyBound` | `936c2791864842727d721445ba3272b2c8fbdbef19a20ad7b6639ff647968829` |
| `ImbalancedChen/Part3ActualSeparatedRowFiniteMatcher.lean:1941` | `ActualSeparatedRowPacketMatchSourceOnly.baseCarrier` | `0986da9eb998fde56106d5f64c57cd25f2559eccda1e179ef919133045ee4301` |
| `ImbalancedChen/Part3ActualSeparatedRowFiniteMatcher.lean:2282` | `ActualSeparatedRowPacketMatchSourceOnly.signedResidue` | `0eab1c1e8e1b00045ac5b644aac52a101196c76fe8a5092ee25d20291252b0fb` |
| `ImbalancedChen/Part3ActualPositiveLatticeSmoothCover.lean:299` | `ActualPositiveLatticeSmoothCoverSourceOnly.scaleF` | `ac2dfecbe79c243ad05088fdeba46b3fbfee5108772f286cd567c0b8de4151e6` |
| `ImbalancedChen/Part3ActualM2FinitePoissonAdapter.lean:28` | `ActualM2FinitePoissonAdapterSourceOnly.signedResidue_natAbs` | `fe115e7f1bdf1674603a409012755733eadc83d3c88255795805c5fd978770a5` |
| `ImbalancedChen/Part3ActualModeJointBetaPositiveCount.lean:89` | `ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource` | `8d0856e956e5a618e5f6021e79bfa0c2aa994638dc1a8a0a7d065fdc7eeb700f` |

Keep the entire original `MediumAtom` declaration, in order.

```lean
structure MediumAtom where
  U : ℝ
  V : ℝ
  Q1 : ℝ
  Q2 : ℝ
  Q3 : ℝ
  residue : ℤ
  intervalLo : ℝ
  intervalHi : ℝ
  alpha : ℕ → ℂ
  beta : ℕ → ℂ
  gamma1 : ℕ → ℂ
  gamma2 : ℕ → ℂ
  gamma3 : ℕ → ℂ
```

The actual source still filters the exact finite `carrier` by the original nonzero output. Its arguments are (g*l), the signed residue of the same atom, the original image of factor-carrier points divisible by (D/delta), the literal common smooth frequency bound, and the symmetric closed signed (f)-window with integer ceiling and floor. The extraction keeps the behavior of the quotient when an input is zero and introduces no positivity, coprimality or counting hypothesis. The two Bool parameters of `actualDyadicBeta` keep their different roles.

The four short declarations keep namespace `ImbalancedChen.P3ZActualPrimaryShortEndpoint`. The last row keeps namespace `ImbalancedChen.P3ZActualPrimaryDyadicAssembly`. Direct comparison confirms identical statement and body bytes in the immutable base and the registered short donor blob `7b3374576687df50307ef847aa51e9fef15dddae` or assembly donor blob `3a12da5b72eeddd3558c4714eecd7754cd660a55`.

| Original donor path and lines | Declaration | Exact block SHA-256 |
| --- | --- | --- |
| `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean:48–54` | `actualDyadicBeta` | `9102f7104e708e021f0d4613c24fa2cebd95d43331d7ed76573319ba37644e4e` |
| `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean:56–62` | `actual_nonempty_endpoint_bounds` | `ae90141d976682e602768b4f9250468f3ba0541a4c013795804b244116fe5194` |
| `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean:64–70` | `actual_short_index_eq_one` | `f74e62b76ab21efd78271d3f129850cf8b4c66e3e44970990f7dfea3d975bf70` |
| `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean:72–78` | `actual_nonzero_coprime` | `1d815d626bd6523d5da164cf983304e4524ef9429293c220b58fb0b7c655614e` |
| `ImbalancedChen/Part3ZActualPrimaryDyadicAssembly.lean:26–47` | `actual_beta_energy_assembly` | `c7f5fe7f45f09a1315f82237a9cc5678dbd96e8299650bd5ca138e74ef621e74` |

The earlier `376df9d58bd92de218719a6b1dd8e08505d4bddc44fbd46e99b38f786d50ab2c` for `actual_nonzero_coprime` additionally hashes the blank line and following section-closing `end`. The 487-byte value here ends on `dyadicBeta_coprime hb` and is the appropriate check for a declaration moved into a new wrapper.

## 2. Exact extraction and compatibility remainders

1. **`ImbalancedChen.Part3MediumAtomCore`** owns the original `MediumAtom` structure and `factorCarrier` in the original namespace. Use direct Mathlib imports covering complex numbers, real floor/ceiling and natural finite intervals. Candidate roots available locally are `Mathlib.Data.Complex.Basic`, `Mathlib.Algebra.Order.Archimedean.Real.Basic`, and `Mathlib.Order.Interval.Finset.Nat`. `Part3DistributionTargets` imports this module and removes only these two declarations in this unit. Its prior packet and common-variable relocations stay in force, and `MediumAtom.scale`, the alpha/beta carriers, target definitions and every other declaration stay in that file.
2. **`ImbalancedChen.Part3ActualNonzeroSourceCore`** imports `Part3MediumAtomCore` and `Part3LiteralReciprocalSource`. `Mathlib.Data.Int.Interval` and `Mathlib.Algebra.Order.Archimedean.Real.Basic` provide the signed finite interval and real floor/ceiling. Move the other six provider blocks, retaining their original namespaces. In dependency order they are `MediumAtom.sharedSmoothFrequencyBound`, `baseCarrier`, `signedResidue`, `scaleF`, `signedResidue_natAbs` and `actualNonzeroSource`. Preserve `open Classical Finset` and the local classical decidability in the actual-source definition as needed. The inherited `carrier`, `nonzeroSource` and `Source` come from the already accepted `Part3LiteralReciprocalSource` via `ActualCompletedSquarePushforwardSourceOnly`, so the finite source is defined only once. Old donor modules each add an explicit import of the new core and remove only the selected declaration blocks. The new core imports none of these donor modules.
3. **`ImbalancedChen.Part3PrimaryDyadicActualMode`** imports `Part3ActualNonzeroSourceCore` and `Part3PrimaryDyadicAssembly`. The latter already covers the short core and the accepted `nonempty_endpoint_bounds`, `short_nonzero_index_eq_one`, `dyadicBeta_coprime`, `finite_beta_energy_assembly` and `nonzeroSource_idempotent`. Move all five specialization blocks unchanged under their two original namespaces. Use `open Classical Finset`, `open scoped BigOperators` and the original finite source namespace where referenced. The specialized proofs leave `lambda` and `omega` as the original theorem parameters.

After this move the two old P3.4 parent files have **import-only remainders**. For maximum source-level compatibility, leave all existing imports from the completed common-phase migration and add `import ImbalancedChen.Part3PrimaryDyadicActualMode` to each. Drop stale `SOURCEONLY` commentary and the empty namespace/section wrappers. The short parent then re-exports the common and actual names, and the assembly parent keeps its import of the short parent plus the common/actual assembly access. Keeping old extra imports preserves the transitive environment for historical callers. The small gate must import the new owning module directly. Compiling the legacy remainders with all their historical imports is a separate compatibility check. The only tracked direct callers found are the assembly parent, the source-only `UncompiledContinuation` import catalog, and archived `Part3OriginalPrimaryPacketRows`. The archive has further original-data dependencies outside this gate.

All two-stage moves are relocations with one defining module per name. The first provider is separated from the actual finite source so `Part3DistributionTargets` does not acquire a dependency on `Part3LiteralReciprocalSource`. Putting all eight blocks in one module could save one gate module at the cost of that new provider dependency.

### Generated declarations and prior owners

- The structure's constructor, 13 projections, recursors and any structure helpers move from `Part3DistributionTargets` to `Part3MediumAtomCore`. The owner of any generated `factorCarrier` helper can be the old defining module or an old elaborating consumer.
- For the other definitions, possible old owners include their respective defining files in the donor table and modules that first materialized equational lemmas by unfolding them. Source scans found materialization sites in `Part3ActualSeparatedRowFiniteMatcher` for `baseCarrier` and `factorCarrier`, `Part3ActualM2FinitePoissonAdapter` for `signedResidue`, `Part3ActualSeparatedRowLogModeSupplier` for `MediumAtom.sharedSmoothFrequencyBound`, `Part3ActualChartResidueEnergy`, `Part3ActualCompletedZeroDifferencePayment`, `Part3ActualLogModeWeightedPhysicalDEnergy` and `Part3ActualZeroTagFreeEpsilonPayment` for `scaleF`, and `Part3ActualRestrictedChartWeightCount` and the energy specialization for `actualNonzeroSource`. The moved `signedResidue_natAbs` proof still runs `simp [signedResidue]`. The moved energy specialization still runs `unfold actualNonzeroSource`. Their new modules can materialize corresponding helper constants. These are observed source sites, with no exact historical ownership asserted for those generated equations.
- No explicit references to named generated equation lemmas for those eight blocks appear in the current tracked Lean sources. The P3.2 published declaration inventory covers only six terminals and does not expose complete generated ownership from its historical provider imports. Query actual module-index ownership and serialized constants for the new environment. Include helpers even when their names are under an old namespace, and reject duplicate constants or inconsistent defining owners. Never mix an old whole-object donor with its relocated declarations.
- P3.1 has one documented example of late generation. The original `ImbalancedChen.Part3.CommonCompletedVariable.weight.eq_1` is owned by `Part3CommonCompletedInterface` in its accepted inventory. This exact extraction leaves both common-phase modules untouched and does not import the P3.1 interface, so it has no need to generate that equation. A later joint import of P3.1 and P3.4 still needs a compatible build of the relocated provider environment. No private/generated name gets grandfathered merely by matching its textual namespace.

### Gate closure and checks

The 12-module ACTUAL closure, in dependency order, is the accepted nine-module dyadic gate followed by the three proposed modules.

1. `Part3FourierModeIndex`
2. `Part3CoprimePacketCore`
3. `Part3CuspPhaseCore`
4. `Part3CoprimePacketCoefficients`
5. `Part3PrimaryPrimeSupport`
6. `Part3LiteralReciprocalSource`
7. `Part3FixedRhoPrimaryFiniteCore`
8. `Part3PrimaryDyadicShortEndpoint`
9. `Part3PrimaryDyadicAssembly`
10. `Part3MediumAtomCore`
11. `Part3ActualNonzeroSourceCore`
12. `Part3PrimaryDyadicActualMode`

For the 14-module joint gate add the current `Part3CommonCompletedVariableCore` and `Part3PrimaryDyadicCommonAssembly` after their own prerequisites. The assembly imports only the common-variable core and `Part3PrimaryDyadicAssembly`. The two extensions otherwise have independent project imports. A combined audit imports both consumer modules, as well as any audited owners needed by the verifier. The gate does not reach the six old providers, the two old P3.4 remainders, or P3.1/P3.2/P3.5 terminals.

Use a clean isolated checkout from the completed common-source tip. Bind the 13 donor block hashes, the move ledger, source tree, package/tool hashes and actual Lean-resolved project object paths/parts. The nine existing local dyadic `.olean` files all match the accepted local and clean-cloud report SHA-256 values byte-for-byte. For the local focused check, reuse those nine imported providers and strictly compile, replay and inventory only the three new owners. For the final P3 acceptance, use a clean gate beginning with zero project objects. Building the nine providers there checks compatibility in the new closure and adds no new proof credit. Use the same no-proof-placeholder source policy and warning-as-error gate as the accepted dyadic unit. Inventory and compare source/frontend and serialized ownership of all constants in the new modules, including generated constants. Capture elaborated types and all reachable axioms of every newly owned declaration, accepting only `Classical.choice`, `Quot.sound` and `propext`. In the combined audit, check the three common and five actual names coexist under their exact namespaces and the accepted provider object bindings remain stable. Keep standalone/common receipts scoped to their own source and object trees.

Verification can establish the five specializations inside the thin closure during this turn if the exact move and the new serialized-object checks pass. The existing local toolchain and narrow Mathlib roots are present, as are the nine exact compatible accepted dyadic objects. This audit did not run that check or accept any new declarations. The historical-language phrase “SOURCEONLY / UNCOMPILED” in old donor files alone does not distinguish a previously compiled provider from a newly accepted theorem.

## 3. Two larger alternatives

### A. Current-source providers plus historical object intake

For exact counts I parsed the immutable Lean import headers including CRLF and added the two current common-phase nodes. The actual source supplier closure has 111 project modules at base and 112 after the common move. The two original wrappers after the common move reach 128. If the short wrapper directly imports `Part3ActualModeJointBetaPositiveCount`, the short dyadic core, and the new common assembly, then removes its now-unused opens, the full source-compatible gate reaches 121 modules. The assembly continues to import `Part3PrimaryDyadicAssembly` and the short wrapper. The seven excluded modules are `Part3ActualLiteralPacketIntegral`, `Part3ActualNormalizedSmoothF`, `Part3ActualSampledFourierLattice`, `Part3ActualWeightedSpectralBudget`, `Part3FixedRhoPrimarySignedFiniteDecomposition`, `Part3NativePeriod64Reconstruction` and `Part3NativePeriod64Sampling`. None supplies a name used by the five specialization blocks.

For a provenance-conservative rebuild, invalidate the six source-different providers and every dependent in this closure. The six are `Part3DistributionTargets`, `Part3CanonicalReciprocalData`, `Part3SharedFirstFactorSmallCoreFourierTruncation`, `Part3PhysicalSmoothReciprocalPoisson`, `Part3ActualReciprocalSquarePoisson` and `Part3ActualCompletedSquarePushforward`. The physical Poisson file differs only in its provenance header. Build it when requiring exact source/object pairs. The Fourier truncation difference is the relocated `poissonNonzeroFrequencyWindow` and its import. In particular the old `Part3DistributionTargets` and the old finite-source owners serialize constants now owned by the extracted packet and literal-source cores. Importing those old objects alongside the newer cores risks duplicate or mismatched definitions.

The 121 project modules split into **60 fresh or changed-closure modules**, **52 P3.2 historical reuse candidates**, and **nine independent accepted P3.4 dyadic modules**. The 60 comprise the six changed providers, 50 byte-identical P3.2 sources whose input import closures changed, the two new common modules and the two original specialization wrappers. Already accepted common-phase objects can satisfy their two entries if their actual bindings match. The levels below give a valid rebuild order given the 61 unchanged prerequisites.

| Level | Rebuild modules, all prefixed `ImbalancedChen.` |
| --- | --- |
| 0 | `Part3CommonCompletedVariableCore` |
| 1 | `Part3DistributionTargets`, `Part3PrimaryDyadicCommonAssembly` |
| 2 | `Part3ComplexDispersion` |
| 3 | `Part3CommonSmoothCutoff`, `Part3ComplexCRTConsumer`, `Part3FactorFiberDivisor` |
| 4 | `Part3CanonicalReciprocalData`, `Part3CleanBetaLargeGCDMajorant`, `Part3CommonPoisson` |
| 5 | `Part3CanonicalReciprocalPhase`, `Part3PhysicalSmoothReciprocalPoisson`, `Part3PolynomialResidueDivisorBound`, `Part3SmoothProgressionError`, `Part3TransposedDispersion` |
| 6 | `Part3ActualLargeGCDBetaMass`, `Part3SharedFirstFactorDispersion`, `Part3SmoothCoprimeError`, `Part3TransposedZeroCovariance` |
| 7 | `Part3PrimitiveZeroReal`, `Part3SharedFirstFactorCharacterDictionary`, `Part3SharedFirstFactorDifferenceReciprocity`, `Part3SharedFirstFactorHighConductor`, `Part3SignedDivisorDeletion`, `Part3TransposedPrimitiveU` |
| 8 | `Part3PairedAlphaDeletion`, `Part3SharedFirstFactorLargeResidualZero`, `Part3SharedFirstFactorLowConductorSW`, `Part3SharedFirstFactorSmallResidualHighConductorZero`, `Part3TransposedGCDPoissonMask`, `Part3TransposedPrimitiveUMoment`, `Part3TransposedPrimitiveV` |
| 9 | `Part3SharedFirstFactorLowConductorAggregate`, `Part3SharedFirstFactorPairCount`, `Part3TransposedPrimitiveUPayment`, `Part3TransposedPrimitiveVMoment` |
| 10 | `Part3SharedFirstFactorLargePairedGCDW`, `Part3SharedFirstFactorZeroCovariancePayment`, `Part3TransposedPrimitiveVPayment` |
| 11 | `Part3SharedFirstFactorLargePairedGCDNonzero`, `Part3SharedFirstFactorLargeSupportedDeletion`, `Part3SharedFirstFactorPrimitiveUVPayment` |
| 12 | `Part3SharedFirstFactorEnergyNonzeroReduction` |
| 13 | `Part3SharedFirstFactorSmallPairedSupportedReduction` |
| 14 | `Part3SharedFirstFactorSmallCoreFourierTruncation` |
| 15 | `Part3SharedFirstFactorSmallCoreSmoothFrequency` |
| 16 | `Part3SharedFirstFactorSmallCoreSquaredFinite` |
| 17 | `Part3SharedFirstFactorGeneralDRootPacket`, `Part3SharedFirstFactorSupportedCoreCauchy` |
| 18 | `Part3ActualSeparatedRowFiniteMatcher`, `Part3SharedFirstFactorGeneralDPairedFourier` |
| 19 | `Part3ActualPositiveLatticeSmoothCover`, `Part3SharedFirstFactorGeneralDRowAdapter` |
| 20 | `Part3ActualReciprocalSquarePoisson`, `Part3ActualSeparatedRowLogModeSupplier` |
| 21 | `Part3ActualCompletedSquarePushforward`, `Part3ActualM2FinitePoissonAdapter` |
| 22 | `Part3ActualModeJointBetaPositiveCount` |
| 23 | `Part3ZActualPrimaryShortEndpoint` |
| 24 | `Part3ZActualPrimaryDyadicAssembly` |

The needed 52 historical provider objects are, alphabetically with prefix `ImbalancedChen.` omitted.

```text
ActualGridEnvelopes, ActualSieveGate, AsymptoticTransfer, BadSourceLocalization,
BoundaryCellContainment, BoundaryGlobalCaps, BoundaryGridBudget, CoprimeRecentering,
Counting, CurrentMainTheorem, CurrentNumericalTransfer, CurvedRegionDiscrepancy,
FiniteSieveModel, HalfProductGeometry, HalfProductMassError, HalfProductMassFibres,
HalfProductMassLimit, HalfProductMassSplit, HalfProductPanFinite, HalfProductSource,
LogCutoffError, MassLogIntegral, MultiplicativeGridPartition, Multiplicity,
NormalizationGrowth, OrderedBad, PanProductAggregateBudget, PanProductGrid,
PanProductGridRanges, PanProductLiuBridge, PanProductResidueBudget, PanProductStrips,
Part3CompactCoordinateFourier, Part3ElementaryE1RealEndpoint,
Part3ElementaryE1StrictFloor, Part3ElementaryIntervalDivisibility,
Part3ElementaryTauDeletionFiber, Part3ElementaryTauTruncation, PowerErrorBudget,
PrimeRectanglePrefixes, RationalPowers, RealHalfProductMass, RealHalfProductMassSplit,
RealHalfProductSource, RectangleDiscrepancyAssembly, ResidueSelectorBudget,
RestrictedResidueScale, SelectedGridRanges, SieveSourceCoprimality, SingularSeries,
TotientReciprocalBudget, UniformPrimeTail
```

#### Artifact locations and actual provenance

| Receipt | Location and reuse evidence |
| --- | --- |
| P3.2 accepted source and CI | `34201be0ca95d465336119fce24b7681c17ab0c6` with evidence commit `30e2a96b601458d59116517ca478c496a68a39c9` in `/workspace/scratch/e4b706aea1e3/goldbach-p31`. The evidence paths start at `docs/part3-distribution/node32-20261125/`. `ci-34201be0/report.json` records all 130 resolved objects and exact source hashes. The actual supplier SHA-256 is `2549105079d05ef1bc5f1f2f555c30fca8f549c595f9d515fcd11161e65c3b07` for the old object and `f56bd1ee5294fb62a1f5c0fc003908f61daa190a2cf4c4ade84e7a0e9f74504e` for its still-identical source. The 52-member `ci-34201be0/p3-node32-34201be0.zip`, CI run 45573162551 and artifact 15006126803, contains zero serialized objects. The build paths on the GitHub runner are historical. |
| P3.1 new actual interface | At `5b9a6548bf2cd18f48b2858a881701b033b6f722`, `docs/part3-distribution/p31-actual-interface-20261126/verification/report.json` contains 64 resolved project objects. For the 52 needed historical providers, 31 have exactly matching post-strict `.olean` SHA-256 in both reports. The P3.1 43-member `verification.zip` contains no objects. `verification/cache-intake.json` records pre-build copies of 60 source/trace/object groups from the cloud checkout `/workspace/p35-full-height-20261125` into `/workspace/p31-actual-interface-20261126` before the build. Neither path exists locally. Intake hashes can differ from the verified final objects. `Part3DistributionTargets.olean`, for example, is `ace5c67f…` at intake and `3c3a309d…` in the post-strict report. |
| P3.5 supplied tip | At `ce38b7e8a5a2e7d501afe3a0213e08641dfbc777`, `docs/part3-distribution/continuation-20261126/test-seminorm/RECEIPT.json` explicitly records no binaries. Its 39-member archive and report supply evidence for the two owned P3.5 modules, neither needed by these five P3.4 statements. The named warm P3.5 checkout in P3.1's intake manifest is a potential object source if still recoverable and verified in a later authorized run. |
| P3.4 dyadic | `docs/part3-distribution/p34-20261126/dyadic-clean-cloud-report.json` at the immutable base binds all nine accepted objects. The 62-member evidence ZIP contains logs, inventory and hashes. The nine matching local binaries were actually found in `/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/`. |
| Other named local stores | The two P3.1 local checkouts have no project object directory containing these binaries. `/workspace/scratch/dcb7c80f70a4/p34-delta` contains Git stores and source-recovery metadata. Those source and evidence objects are distinct from Lean object files. |

A valid warm intake must recover actual bytes for each selected historical object and all required serialized parts, compare against report-bound SHA-256 and source content under the exact pins, and confirm Lean resolves those files. Do not substitute a nearby worktree's source hash or an earlier copied trace for the accepted byte pair. A successful strict/replay check of the two legacy wrappers would still need a fresh full transitive axiom audit for the five declarations. This route lacks the 52-object historical payload in the inspected local stores.

### B. Full source-compatible build

The exact current source closure is present. The 121-module direct-import route, or the 128-module original-umbrella route, can be ordinarily built using the original proofs under the pinned runtime. This is a compatible build of existing source, with fresh strict compilation and kernel replay targeted at the new specialization declarations and any moved owners. Bind the complete actual source and object resolution and audit all transitive axioms of the targeted declarations. This preserves existing mathematical proof credit and uses ordinary trusted imports for historical providers.

The frozen `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` match P3.2 byte-for-byte. The local Lean and bundled checker SHA-256 values match the accepted P3.1 environment. The local package checkouts identify Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and goldbach `09b97db5764ade1246bfb77206baa1b124760958`. The broad closure had 16 direct external import roots with missing local compiled objects at inspection. The 14 Mathlib roots are `Analysis.Calculus.BumpFunction.InnerProduct`, `Analysis.Distribution.SchwartzSpace.Fourier`, `Analysis.Fourier.AddCircleMulti`, `Analysis.Fourier.FourierTransformDeriv`, `Analysis.Fourier.PoissonSummation`, `Analysis.Fourier.ZMod`, `Analysis.PSeries`, `Analysis.SpecialFunctions.Complex.CircleAddChar`, `Analysis.SpecialFunctions.Log.Base`, `Analysis.SpecialFunctions.Log.Summable`, `NumberTheory.AlmostPrime`, `NumberTheory.Harmonic.Bounds`, `NumberTheory.PrimeCounting`, and `NumberTheory.SelbergSieve`. The two pinned goldbach roots are `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean` and `MathlibNt.SieveTheory.LiLiuPanBoundedAggregate`. Their source is in the pinned dependency checkout. The pinned goldbach package has no local `.lake/build/lib/lean` directory. This identifies a lower bound on the cache recovery/build work, since secondary packages and transitive object parts still need resolution checks.

For scale, P3.2's historical CI recorded 2,349.827 seconds for ordinary target build and 2,499.525 seconds from verifier start to finish. The P3.1 actual-interface retry took 471.255 seconds with one Lean thread and a recorded peak of 8,549,105,664 bytes, after a two-thread 10,000 MB attempt exceeded its budget. These are prior runs with different closures. The local environment has about 10 GB of total memory and shares it with the running common gate. With the presently available objects, neither broad route supports a quick or established same-turn acceptance claim.

## 4. Acceptance boundary

A successful thin-gate receipt establishes the exact actual finite-source specialization, endpoint inequalities, short-index rigidity, residue coprimality and beta-energy partition. The source uses the installed type and actual signed finite source data and keeps the entire existing proof of `signedResidue_natAbs`. The historical positive-count proof and other manuscript-internal P3.2 derivations retain their accepted status and their existing owner modules.

The immediate work is import and defining-owner compatibility plus the first strict/replay and transitive-axiom checks of the five declarations. There is no missing `OriginalData`, `FixedBlock`, automorphic Fourier, Fricke, or completed-Eisenstein input for this exact scope. Those dependencies matter for the larger original-row or spectral interfaces. Exact finite beta-energy partition with supplied `lambda` and `omega` does not construct the original row, give its signed spectral norm cost, or close P3.4.
