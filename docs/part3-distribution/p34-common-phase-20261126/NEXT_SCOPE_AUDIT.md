# P3.4 next-interface audit — read-only, 2026-11-26

## Decision

The smallest useful next P3.4 unit is **first acceptance of the three already-written common-phase consumers**:

1. `ImbalancedChen.P3ZActualPrimaryShortEndpoint.short_common_phase_packet`;
2. `ImbalancedChen.P3ZActualPrimaryDyadicAssembly.common_phase_source_assembly`;
3. `ImbalancedChen.P3ZActualPrimaryDyadicAssembly.common_phase_beta_assembly`.

Their complete statements and proof bodies already exist and remain identical to the registered donor bodies. They preserve the genuine `CommonCompletedVariable.weight`, original finite source, beta, mode phases and signs. No new mathematical argument, arbitrary replacement weight, `OriginalData`, automorphic Fourier coefficient, Fricke supplier or completed-Eisenstein supplier is needed for these three identities.

For a small standalone acceptance closure, the recommended migration is two unchanged common-variable source definitions into one Mathlib-only provider and these three unchanged proofs into one consumer. The resulting proposed project closure has **11 modules: the already accepted nine dyadic modules, the common-variable provider, and the three-proof consumer**. This is a source/interface relocation and first verification of the retained consumers, not another proof of P3.1's accepted inequalities or P3.5's accepted Cauchy/exhaustion theorems.

This audit does not certify any new Lean declaration. No Lean/lake/leanchecker command, compiler job, branch change or tracked-file edit was performed. Worktree HEAD stayed `b945f39a1e355ff4fcca9865ab59ffc97f2172c0` and `git status --short` stayed empty. Root supplied additional exact Git objects during the audit; only named revisions were read. The sole output written by this agent is this report.

## 1. Frozen sources and exact eight-consumer inventory

Repository: `/workspace/library-files/p34-proof-work`.

Manuscript: `/workspace/scratch/dcb7c80f70a4/analytic-appendix-1106.tex`, 45,951 bytes, SHA-256 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`; parent source is the 1106 appendix frozen at manuscript commit `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`.

| Current file | Git blob at audited HEAD | SHA-256 |
|---|---|---|
| `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean` | `01e765e923fda572c750dd3724a7946f942ccd86` | `c5d026a2fedd7646f43bf614209782955fcc9e3f851bee5934bcf316d865c314` |
| `ImbalancedChen/Part3ZActualPrimaryDyadicAssembly.lean` | `57388059f7899cb735bddc3421f37502ef875805` | `b08866154b7704cc6ab4867032b18de6ede9172006e1d91b279d1d29d14ef1c1` |
| `ImbalancedChen/Part3DistributionTargets.lean` | `9f415fe7bb422874b4e81c6042751d06cd599ca8` | `ed26d01f977000a8656dc5375d8f1f6aca1f2a7a1c4c35616f0e37b90eb4bca2` |

All names in the first five rows below are in `ImbalancedChen.P3ZActualPrimaryShortEndpoint`; the last three are in `ImbalancedChen.P3ZActualPrimaryDyadicAssembly`.

| Declaration and current start line | Existing conclusion and true dependencies | Classification |
|---|---|---|
| `short_common_phase_packet`, short file 27 | For `0 < U` and `U/nu < 1`, the original double finite packet sum equals its `n=1` term when `1 ∈ N`, and zero otherwise. Depends only on the accepted `finite_singleton`, `short_modeCoefficient_zero`, literal packet/mode definitions and genuine `CommonCompletedVariable.weight`. Keeps existing `hz`, residue/level coprimality and all mode arguments. | Ready source-level finite consumer; recommend next unit. |
| `actualDyadicBeta`, short file 48 | Exact abbreviation of `dyadicBeta (signedResidue residueNegative e.residue) (actualNonzeroSource e D delta g l Z residueNegative) nu U yNegative lambda omega`. Residue sign and output sign remain independent. | Actual-mode supplier specialization; present source, larger provider closure. |
| `actual_nonempty_endpoint_bounds`, short file 56 | From positive `U` and nonzero same beta at `nu*n`: `0 < nu`, `0 < n`, `nu ≤ 2U`, `1/2 ≤ U/nu`. One-line use of accepted `nonempty_endpoint_bounds`. | Present proof; not a missing arithmetic derivation. |
| `actual_short_index_eq_one`, short file 64 | Same nonzero coefficient and `U/nu < 1` imply `n=1`. One-line use of accepted `short_nonzero_index_eq_one`. | Present proof; not a missing arithmetic derivation. |
| `actual_nonzero_coprime`, short file 72 | Same nonzero beta implies `Nat.Coprime n e.residue.natAbs`. Uses accepted `dyadicBeta_coprime` and existing `ActualM2FinitePoissonAdapterSourceOnly.signedResidue_natAbs`. | Present proof; larger actual-mode provider integration. |
| `actual_beta_energy_assembly`, assembly file 26 | Exact beta energy on the installed `actualNonzeroSource` equals the sum of its computed block beta energies. Uses accepted `finite_beta_energy_assembly` and `nonzeroSource_idempotent`; unfolds the existing actual-source definition. | Present proof; larger actual-mode provider integration. |
| `common_phase_source_assembly`, assembly file 51 | Exact source partition under the same `I.weight m` and the same payload `K m (output s)`. Uses `finite_source_assembly`, then finite sum exchange. | Ready source-level finite consumer; recommend next unit. |
| `common_phase_beta_assembly`, assembly file 62 | Exact beta partition under the same common weight and same payload. Uses `finite_beta_assembly`, distributivity and finite sum exchange. | Ready source-level finite consumer; recommend next unit. |

The retained three common statements are not consequences of a norm comparison alone: they are exact complex identities. Conversely, the exact beta-energy partition does not assert orthogonality of arbitrary spectral row sums.

### Donor equality and no-repeat check

`DYADIC_PRIOR_WORK_AUDIT.json` pins original donors `7b3374576687df50307ef847aa51e9fef15dddae` and `3a12da5b72eeddd3558c4714eecd7754cd660a55`, originally registered source-only at `29a0717b23cbab3a4bfb5f9066b815c181b3efa4`. Direct bounded declaration-text comparison found all eight current statements/bodies unchanged. For the three proposed consumers the normalized statement/body slice SHA-256 values are:

- `short_common_phase_packet`: `3b69d66d005f87ef465ffa8a2c0377048e11988a47e1c931147c5722d84a2718`;
- `common_phase_source_assembly`: `3a3a42d062b0be810f4ef96825781ff6bf3af2570006abdf56dba434a6f59ee0`;
- `common_phase_beta_assembly`: `25f08ae5f1f9568af254ecabeff2df5439eec69863cf1d6e885c0a0c8130c9b8`.

These slice hashes omit trailing whitespace and declaration-leading documentation; the complete file hashes above bind the full source. This was a source comparison, not elaborated-type or kernel verification.

The accepted union's 19 modules/294 constants does not include these retained parent consumers. The bounded P3.1/P3.2/P3.5 inventory checks below do not include them either. There is therefore a distinct first-acceptance task, but no justification for writing new synonymous proofs.

## 2. Accepted common providers: source coverage and compiled coverage

### P3.1 original common interface

At source `3624fefd379091dba61fccb2e58e7c457c3be69b`, evidence `eac59fac68a389eee5d15c3c44eb9dd487049ab9`, reuse:

- `ImbalancedChen.Part3.CommonCompletedInterface.sum_weight_mul_eq_sum_inter`;
- `ImbalancedChen.Part3.CommonCompletedInterface.weight_weightedEnergy_le`;
- `ImbalancedChen.Part3.CommonCompletedInterface.packet_weightedEnergy_le`.

The exact source SHA-256 is `2d2b50e2547cbb98daf5b9cdd23892c9885cb42c1fa7fa49f02d1a60213d12a2`. The complete accepted inventory contains six constants: these three theorems, two generated simp helpers, and **`ImbalancedChen.Part3.CommonCompletedVariable.weight.eq_1`**, owned by `Part3CommonCompletedInterface`. Preserve this ownership fact in later joint imports; the source namespace alone does not determine the defining module.

The provider `Part3DistributionTargets` has a historical accepted receipt with 91 constants, carried through the `c509267dc630d91df33033abde1c484ec86b96ae` baseline. `SOURCE_MANIFEST.json` records that the new P3.1 interface did not freshly replay the old provider. The old provider SHA-256 is `a0b43f877bb7bcdf7606e19281521a0165538c08c0495a2a3e2d58b66aeb08cc`. Its `CommonCompletedVariable` structure and `weight` definition are byte-identical declaration text to current lines 69–77. The full current provider is different because the previously accepted P3.4 change extracted `CoprimePacket`.

### New P3.1 accepted actual common interface, supplied during this audit

Root supplied exact tip `5b9a6548bf2cd18f48b2858a881701b033b6f722`. Its `docs/part3-distribution/p31-actual-interface-20261126/ACCEPTANCE.json` records source **`acfa81c6d593276ef50f8af4e4f79b150772d7c8`**, 35 passing stages, 10 owned constants, and **64 project sources and resolved objects bound**. It freshly strict-compiles/replays only `Part3ActualCommonCompletedInterface`; historical providers remain normal imported-environment trust, explicitly not a fresh full replay.

Reuse these six already accepted theorems in `ImbalancedChen.Part3.ActualCommonCompletedInterface`:

- `fullBlock_weight_sum_eq_mCarrier`;
- `modeCore_eq_fullBlock`;
- `spectral_mSide_weightedEnergy_le`;
- `rowPair_eq_nSide_mul_mSide`;
- `modeCore_eq_sum_nSide_mul_mSide`;
- `spectral_pair_norm_sq_le`.

Their four associated definitions are `SpectralIndex`, `mSide`, `nSide`, `rowPair`. The source is SHA-256 `90213e68cf634cd19a1969a0ec8a3406e0b61ed08f377354e76175d46a73b4c3`, unchanged at supplied source `c5ccf81ce1a55e2dafeca0116cd70177bf169504`. In particular do not reprove the signed product-kernel factorization or finite spectral Cauchy as a P3.4 follow-up.

The accepted report's actual provider object records include:

| Module | Accepted resolved `.olean` SHA-256, unchanged after strict/audit |
|---|---|
| `Part3DistributionTargets` | `3c3a309d23c32e703df4103419af32a9158bf654831af8cc0ddfe7f936cc3755` |
| `RestrictedResidueScale` | `98447335db03bd09d1e35ba880160f764d6f1d7ff6a980bbb8f26984720d063c` |
| `Part3CommonCompletedInterface` | `9cffaf878f3b8c920ec4770b0514648febd6a238db970b35995b7925a9cb8ca0` |

These are report-bound historical objects, not objects inspected or rebuilt in this audit. The three normal local object paths are absent in the P3.4 worktree. Do not load the old `Part3DistributionTargets.olean` beside the new `Part3CoprimePacketCore`: the old provider defines the same packet constants that were subsequently relocated.

### Exact source closure size

A bounded source-import inventory of the current provider has 48 project modules including itself. Of these, **46 files exactly match the new P3.1 accepted 64-module closure**, one is the changed `Part3DistributionTargets`, and one is the separately accepted `Part3CoprimePacketCore`. None is missing source. The nine-module dyadic closure overlaps it only at `Part3CoprimePacketCore`, so their union has 56 modules before adding a common consumer.

These counts are source-text import analysis for planning; the eventual acceptance must use actual Lean-resolved import/object provenance. The accepted P3.1 report supplies compiled historical coverage of the 46 unchanged providers, but not automatic acceptance of their combination with relocated P3.4 definitions.

## 3. Exact minimal migration and dependency order

Recommended tentative filenames are `Part3CommonCompletedVariableCore.lean` and `Part3PrimaryDyadicCommonAssembly.lean`; the filenames are implementation choices, not claims of existing modules.

### Provider migration

Move exactly the current `CommonCompletedVariable` structure and `CommonCompletedVariable.weight` definition from `Part3DistributionTargets.lean` lines 67–77, retaining namespace `ImbalancedChen.Part3`, fields, types, body and documentation. The provider needs only pinned Mathlib for complex exponential and natural finite intervals; no project module is mathematically needed. Use `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` (the existing packet core already uses it for the same complex exponential/pi syntax) and `Mathlib.Order.Interval.Finset.Nat`, subject to the actual compiler's import check. Make `Part3DistributionTargets` import the new provider and remove the old definitions.

This creates no replacement structure or alias. Preserve the existing public names. Constructor, projections, recursors, generated constants and any lazily generated equation lemma must be inventoried under their actual defining modules. Do not deliberately introduce a second `weight.eq_1` or copy P3.1's generated proof; check actual ownership when later reusing that interface.

### Consumer migration

Move precisely the three proofs identified in section 1, preserving their complete namespaces, theorem types and bodies. The new consumer imports only the new common-variable provider and `Part3PrimaryDyadicAssembly` as project dependencies. The latter already imports the short core, original finite source definitions, mode index and packet coefficient definitions required by the statements.

Remove these three old declarations from their old parent files and add an import of the new consumer there. The short parent retains `actualDyadicBeta` and its three actual endpoint/coprimality theorems; the assembly parent retains `actual_beta_energy_assembly`. Do not add `Part3ActualLiteralPacketIntegral`, `Part3FixedRhoPrimarySignedFiniteDecomposition`, P3.1's inequality module or any spectral module to the small consumer. Do not rewrite the statements with an arbitrary `ℕ → ℂ` weight merely to avoid the genuine common variable.

### Proposed 11-module source order

Retain the accepted dyadic verifier's existing nine-module order and append the two new modules:

1. `ImbalancedChen.Part3FourierModeIndex`
2. `ImbalancedChen.Part3CoprimePacketCore`
3. `ImbalancedChen.Part3CuspPhaseCore`
4. `ImbalancedChen.Part3CoprimePacketCoefficients`
5. `ImbalancedChen.Part3PrimaryPrimeSupport`
6. `ImbalancedChen.Part3LiteralReciprocalSource`
7. `ImbalancedChen.Part3FixedRhoPrimaryFiniteCore`
8. `ImbalancedChen.Part3PrimaryDyadicShortEndpoint`
9. `ImbalancedChen.Part3PrimaryDyadicAssembly`
10. proposed `ImbalancedChen.Part3CommonCompletedVariableCore`
11. proposed `ImbalancedChen.Part3PrimaryDyadicCommonAssembly`

The actual three-proof dependency order is independent: `short_common_phase_packet` consumes `finite_singleton` and `short_modeCoefficient_zero`; `common_phase_source_assembly` consumes `finite_source_assembly`; `common_phase_beta_assembly` consumes `finite_beta_assembly`. None needs another of the three.

The original nine proofs and receipts remain reusable. If the gate retains P3.4's fresh-small-closure policy, replaying those nine in the new eleven-module closure is compatibility verification, not new proof credit. Alternatively an explicit imported-environment reuse gate may bind unchanged accepted objects and verify only the two newly owning modules. The trust boundary must be chosen honestly before execution. No branch-wide provider or actual-parent compilation follows from either small gate.

The no-provider-move alternative is a consumer importing current `Part3DistributionTargets`, yielding 57 project modules. This is mathematically possible and can reuse historical providers, but requires a compatible rebuilt provider and careful source/object binding. The 11-module relocation avoids bringing the 46 unrelated accepted project providers into this new finite gate.

## 4. Five actual-mode specializations are not an OriginalData source blocker

The exact supplier is present at `ImbalancedChen/Part3ActualModeJointBetaPositiveCount.lean:89`:

```lean
nonzeroSource (carrier (g*l) (signedResidue negative e.residue)
  (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
  (Icc (Int.ceil (-scaleF e D g)) (Int.floor (scaleF e D g))))
```

Its file SHA-256 is `f56bd1ee5294fb62a1f5c0fc003908f61daa190a2cf4c4ade84e7a0e9f74504e`, matching the accepted P3.2 source closure at `34201be0ca95d465336119fce24b7681c17ab0c6`, evidence `30e2a96b601458d59116517ca478c496a68a39c9`. That 130-module source/object-bound closure also includes `Part3ActualM2FinitePoissonAdapter`, `Part3ActualSeparatedRowFiniteMatcher` and the old `Part3ActualLiteralPacketIntegral`; its six strict/replay terminals do not include the two P3.4 parent modules.

The current `Part3ActualModeJointBetaPositiveCount` source graph has 111 project files and no missing named import. Against P3.2's exact closure: 102 files match, three are the new accepted packet/primary/source cores, and six are changed provider files. The six are `Part3DistributionTargets`, `Part3CanonicalReciprocalData`, `Part3SharedFirstFactorSmallCoreFourierTruncation`, `Part3PhysicalSmoothReciprocalPoisson`, `Part3ActualReciprocalSquarePoisson`, and `Part3ActualCompletedSquarePushforward`. The physical Poisson difference is only its provenance header; the Fourier truncation difference is the moved `poissonNonzeroFrequencyWindow` and its import. The other changes must retain the existing P3.4 relocation records, not be silently replaced by old P3.2 objects.

Thus these five consumers can be a later source-preserving compatibility unit, without `OriginalData` or external spectral work. Their obstacle is larger provider integration/verification, not unavailable actualNonzeroSource bytes. Their freely supplied `lambda` and `omega` must not be advertised as a completed construction of the manuscript's full original row.

## 5. Genuine original coefficient/norm interfaces: preserve existing work

`docs/source-only/20261102-resume-30p/medium_spectral_dictionary/Part3OriginalPrimaryPacketRows.lean`, blob `4281ec328d4c3a0f4cb9ca21c2f0923604e6e47a`, SHA-256 `a3e1953d1a521d55aa62c5911c7b524a2dd61210417d891027ec28900f84e287`, already supplies the intended original construction in namespace `ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102`:

| Source declaration | Dependency role |
|---|---|
| `originalKeys`, `primaryBlock`, `outputCarrier`, `levelCarrier`, `outputFibre`, `quotientIndex`, `nCarrier`, `decode`, `blockBeta` (37–61) | Definitions on the genuine `D : OriginalData`, `originalSource D`, completed `D.lambda r`, and `D.omega`. |
| `outputCarrier_data` (75), `decode_quotient` (103), `quotient_decode` (115) | Obtain licenses from actual witnesses and prove the signed coordinate inverse. |
| `nCarrier_positive_coprime` (128), `nCarrier_dyadic` (141), `nCarrier_normalized` (150), `levelCarrier_licensed` (158) | Derive actual carrier support and packet constructor inputs. |
| `rowPacket` (176), `rowPacket_beta` (185) | Construct the existing `dyadicPacket` and identify its beta using accepted `signed_beta_block_eq`. |
| `rowCoefficient_eq` (194), `rowCoefficient_unphase` (210), `norm_rowCoefficient` (221) | Keep signed cusp phases, derive the coprime gate from `assembled_beta_coprime`, and prove the original coefficient norm identity. |
| `sum_outputFibre_eq_n` (229), `sum_output_eq_rows` (252), `nonzero_original_beta_has_row` (268) | Exact arithmetic reindexing without multiplicity loss and a genuinely occupied row witness from nonzero beta. |

Do not create a generic replacement row structure or assume the output licenses as fields. These existing proofs should be reused once the genuine OriginalData/FixedBlock dependency closure is available. The missing original dependency attachment is a source/integration blocker, not evidence of a mathematical contradiction in these proofs.

Other nearby existing statements must also be retained rather than recreated:

- `OriginalPoissonPrimaryRows20261102.original_source_block_eq_rows` (41), `row_fibre_eq_signed_coefficients` (50), and `completedPiece_eq_zero_and_primary_rows` (90) already connect the original source to these coefficient rows, retaining zero and tail lanes.
- `OriginalTwoZFourierAssembly20261102.norm_modulatedBeta` (64) and `modulatedBeta_eq_unphased_row` (71) already preserve the actual beta norm under Fourier mode phases and keep the inverse cusp phase explicit. They do not establish a spectral oldform identity.
- `OriginalClassicalSpectralSupports20261102.original_nonzero_row_classical_length` (77) is already a direct consumer of the accepted short-core `nonempty_endpoint_bounds` on the same genuine row. `original_fixed_level_A_range` (94), `original_level_classical_cover` (131), and `original_J_threshold_comparison` (147) are also already written; their OriginalData dependency must be restored, not substituted.

There is an independent elementary follow-up candidate in the same support file: `classicalMScale`, `classicalMScale_bounds`, `commonMBlock_classical_support`, `commonPoissonCompleted_classical_support`, `classicalLevelScale`, `classicalLevelScale_bounds` (34, 36, 49, 64, 111, 113). Their mathematical content is endpoint arithmetic, not a spectral theorem. However the m-support statements should reuse P3.1's existing `Part3OriginalCommonPoissonLanesCore`, not introduce duplicate definitions. At supplied tip `5b9a6548...`, source `c5ccf81...`, that 17-declaration common-Poisson intake was explicitly still queued/unaccepted. Do not count its preparation success as acceptance or launch a duplicate job. This is a later option, not the smallest next unit selected here.

## 6. P3.5 reuse and the boundary of permitted spectral work

Accepted P3.5 source `94cff537f2e60173aaf936c2345d5af0ee5e6585`, evidence `5285d4f5d8c40eddf92c108b492c909de8b43cef`, already provides:

- `ImbalancedChen.Part3.ContinuousTraceCauchy.printed_trace_norm_le`;
- `integral_printed_trace_norm_le`;
- `norm_integral_test_mul_printed_trace_le`;
- `norm_integral_test_mul_printed_trace_le_of_energy_bounds`;
- `ImbalancedChen.Part3.ContinuousTraceExhaustion.printed_trace_regular_integrable`;
- `printed_trace_regular_integral_norm_le`;
- `printed_trace_regular_integral_exhaustion`;
- the previously proved `Part3RegularCumulativeShellPayment` and `Part3RegularPositiveMeasureExhaustion` suppliers.

The Cauchy receipt has five owned constants; the later three-module height receipt has 81. Their four relevant source files are byte-identical at root-supplied new P3.5 tip `ce38b7e8a5a2e7d501afe3a0213e08641dfbc777`. No repeat Cauchy, compact L2, global L1, shell summation, or cutoff-limit proof is justified.

Their use on actual rows still requires the same normalized coefficient arrays, continuity and the two cumulative energy bounds; whole-height use also requires the original Bessel test's low/high envelopes at the actual scale. The paired row is `sum_i conjugate(left_i) * right_i / pi`, and both energies retain `1/pi`. The manuscript uses Maass weight `1/cosh(pi*t)`, holomorphic weight `1/(2*pi)`, and continuous measure `dt/pi`. Any native-to-printed conversion must identify the actual coefficients and measures, not merely rename them.

P3.1's accepted finite actual interface likewise still requires actual `hI`, pointwise `hkernel`, a consistent row/height family and a full-phase bound on the same pure m-side array. Its `spectral_pair_norm_sq_le` intentionally retains the actual n-side norm. Equality of the two signed coefficient norms is insufficient to identify their complex row sums with the same spectral kernel; use the existing signed interface, not a sign-erasing norm argument.

Under the present assignment, proving ABL's identities/Frobenius estimate, Kim–Sarnak, spectral decomposition/Kuznetsov, Fricke eigenform normalization, completed-Eisenstein Fourier theory, or Plancherel afresh is forbidden out-of-manuscript foundation work. The manuscript states the external inputs; their genuine existing formal suppliers and matching application hypotheses are the permissible integration boundary. Scalar phase cancellation and fixed-height Fourier integrals do not supply `R_v(a*nu*n) = lambda_v(a*nu) e(n(a*nu-1)/z) R_v(n)`, and must not be promoted to that statement.

## 7. Manuscript-local correspondence and difficulty classification

| Frozen manuscript lines | Consequence relevant here | Current status/classification |
|---|---|---|
| 676–687 | Separate signs; original beta/B/Bnu norms; unit phases and coprime masks do not increase norms. | Accepted packet and dyadic energy cores; original row norm identities already written but await genuine OriginalData closure. |
| 700–717 | Same signed m intervals and phase at every level. | Proposed three exact common-weight consumers preserve the chosen object. P3.1 clipping/energy and actual packet Cauchy already accepted; constructing the full original family remains separate. |
| 722–727 | Exact coprime packet coefficient; common m-functional remains unchanged. | Source for the proposed three identities exists; no missing elementary proof. Oldform packet cost remains an external-input application. |
| 743–758 | Cauchy within the same positive spectral components and the same two arrays. | Reuse accepted P3.1 finite Cauchy and P3.5 continuous Cauchy; actual normalized array identification is still needed. |
| 951–982 | DI normalization, cusp phases, normalized dilation-specific ABL multiplier, and continuous Plancherel convention. | Genuine spectral supplier/application boundary. No phase-only shortcut and no new external foundation. |
| 999–1024 | Regular norm with `L ≥ 1/2` and fixed three component normalizations. | Accepted generic endpoint; original-row endpoint consumer already written. Remaining endpoint corrections are elementary source reuse, while the actual spectral norm identification is not supplied. |

**Implementation/verification gap:** the retained three common consumers; all bodies exist and their only missing small provider packaging is the existing common-variable definition. **Larger but source-complete integration gap:** the five installed actual-mode specializations, whose provider sources are already covered by P3.2/P3.1 provenance modulo documented P3.4 relocations. **True source blocker:** genuine OriginalData/FixedBlock and unavailable actual spectral provider attachment closures, as separately tracked by root's other audit. **Forbidden replacement:** newly formalizing external spectral foundations or inventing a target-shaped source/spectral structure.

The next acceptance should claim only that exact finite primary/sign/dyadic assembly and the short endpoint preserve the original common completed-variable functional. It should not claim construction of the full original spectral row, packet norm cost, regular trace assembly, or completion of P3.4.

## 8. Exact extraction blocks and generated-constant preflight

This appendix records the exact current source blocks to move; it is not an alternate implementation. The historical complete donor hashes from `DYADIC_PRIOR_WORK_AUDIT.json` are:

| Original donor | Git blob | Complete file SHA-256 |
|---|---|---|
| `Part3ZActualPrimaryShortEndpoint` before extraction | `7b3374576687df50307ef847aa51e9fef15dddae` | `8d8f41a161cf423e3944863cdf7ae8304c1536315a72b198cd6ae4eab8b6dd10` |
| `Part3ZActualPrimaryDyadicAssembly` before extraction | `3a12da5b72eeddd3558c4714eecd7754cd660a55` | `20fd20a906072b054fdfd65ba8cada3c1f8504a73d15b2455040dec0f346f935` |

### Common provider: namespace `ImbalancedChen.Part3`

```lean
/-- The returned variable has ONE interval and ONE phase, shared by all
levels. There is deliberately no level-indexed interval or phase field. -/
structure CommonCompletedVariable where
  intervalLo : ℕ
  intervalHi : ℕ
  additivePhase : ℝ

def CommonCompletedVariable.weight (d : CommonCompletedVariable) (m : ℕ) : ℂ :=
  if m ∈ Finset.Ico d.intervalLo d.intervalHi then
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d.additivePhase : ℂ) * (m : ℂ))
  else 0
```

### Short consumer: namespace `ImbalancedChen.P3ZActualPrimaryShortEndpoint`

```lean
/-- Literal packet reduction to n=1. The common completed-variable phase
is exactly the same object at every m and is never moved or discarded. -/
theorem short_common_phase_packet (rho : ℤ) (S : Finset Source) (nu z : ℕ)
    (U : ℝ) (negative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hz : 0 < z) (hc : Nat.Coprime rho.natAbs z)
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1)
    (k : D4 → ℤ) (Z : ℝ) (I : CommonCompletedVariable)
    (M N : Finset ℕ) (K : ℕ → ℕ → ℂ) :
    (∑ m ∈ M, ∑ n ∈ N, I.weight m * signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) n * K m n) =
      if 1 ∈ N then ∑ m ∈ M, I.weight m * signedCoefficient negative
        (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) 1 * K m 1 else 0 := by
  have hs (m : ℕ) := finite_singleton N
    (fun n => I.weight m * signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) n * K m n)
    (fun n hn => by
      rw [short_modeCoefficient_zero rho S nu z U negative lambda omega hz hc hU hshort k Z hn]
      simp)
  simp_rw [hs]
  by_cases h1 : 1 ∈ N <;> simp only [h1, if_true, if_false, sum_const_zero]
```

### Assembly consumers: namespace `ImbalancedChen.P3ZActualPrimaryDyadicAssembly`

```lean
/-- Exact finite common-phase packet assembly on the actual source.
The same I.weight is present in every block, row and completed m. -/
theorem common_phase_source_assembly (rho : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (I : CommonCompletedVariable)
    (M : Finset ℕ) (K : ℕ → Output → ℂ) :
    (∑ m ∈ M, ∑ s ∈ nonzeroSource S, I.weight m * weight lambda omega s * K m (output s)) =
      ∑ k ∈ keys rho S, ∑ m ∈ M, ∑ s ∈ block rho S k,
        I.weight m * weight lambda omega s * K m (output s) := by
  have hs (m : ℕ) := finite_source_assembly rho S
    (fun s => I.weight m * weight lambda omega s * K m (output s))
  simp_rw [hs]
  rw [sum_comm]

theorem common_phase_beta_assembly (rho : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (I : CommonCompletedVariable)
    (M : Finset ℕ) (B : Finset Output) (K : ℕ → Output → ℂ) :
    (∑ m ∈ M, ∑ zy ∈ B, I.weight m * beta (nonzeroSource S) lambda omega zy * K m zy) =
      ∑ k ∈ keys rho S, ∑ m ∈ M, ∑ zy ∈ B,
        I.weight m * beta (block rho S k) lambda omega zy * K m zy := by
  calc
    _ = ∑ m ∈ M, ∑ zy ∈ B, ∑ k ∈ keys rho S,
        I.weight m * beta (block rho S k) lambda omega zy * K m zy := by
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro zy _
      rw [finite_beta_assembly rho S lambda omega zy, mul_sum, sum_mul]
    _ = ∑ m ∈ M, ∑ k ∈ keys rho S, ∑ zy ∈ B,
        I.weight m * beta (block rho S k) lambda omega zy * K m zy := by
      apply sum_congr rfl
      intro m _
      exact sum_comm
    _ = _ := by rw [sum_comm]
```

### Retained remainder and implicit-generation check

The short file must retain exactly these four source declarations (plus imports/wrappers): `actualDyadicBeta`, `actual_nonempty_endpoint_bounds`, `actual_short_index_eq_one`, `actual_nonzero_coprime`. The assembly file must retain `actual_beta_energy_assembly`. Their existing statements and proof bodies already match the historical donor. Neither retained actual beta nor its source is to be redefined in the new common module.

Normalized declaration/body hashes for the retained remainder are:

| Declaration | SHA-256 |
|---|---|
| `actualDyadicBeta` | `9102f7104e708e021f0d4613c24fa2cebd95d43331d7ed76573319ba37644e4e` |
| `actual_nonempty_endpoint_bounds` | `ae90141d976682e602768b4f9250468f3ba0541a4c013795804b244116fe5194` |
| `actual_short_index_eq_one` | `f74e62b76ab21efd78271d3f129850cf8b4c66e3e44970990f7dfea3d975bf70` |
| `actual_nonzero_coprime` | `376df9d58bd92de218719a6b1dd8e08505d4bddc44fbd46e99b38f786d50ab2c` |
| `actual_beta_energy_assembly` | `c7f5fe7f45f09a1315f82237a9cc5678dbd96e8299650bd5ca138e74ef621e74` |

The three proposed proof bodies contain **no** `unfold`, `dsimp`, `rw [CommonCompletedVariable.weight]`, `simp [CommonCompletedVariable.weight]`, `simp_all`, or direct `weight.eq_1` reference. They leave `I.weight m` as an opaque multiplicative factor. In the short proof, `simp` follows a rewrite of the coefficient to zero and discharges multiplication by zero; the concluding `simp only` names only the membership branch and `sum_const_zero`. The two assembly proofs use their explicit finite assembly identities and finite sum rewrites. No source-level step needs the weight's defining equation.

Recommendation: preserve the two provider definitions exactly, and **do not eagerly materialize `CommonCompletedVariable.weight.eq_1`**. Do not import/reprove the accepted P3.1 inequalities and do not relocate their accepted generated equation constant. This source inspection removes an obvious trigger for duplicate equation ownership; only the actual compiled/serialized inventory can confirm what the pinned elaborator generates. Inventory all generated constructor/projection/recursor/equation helpers of the moved structure/definition and reject accidental duplicate ownership rather than filtering it out.

The small gate alone cannot certify a later joint import with `Part3CommonCompletedInterface` or `Part3ActualCommonCompletedInterface`. Those accepted sources and their inequalities remain reusable at their exact receipts; a full P3.1/P3.4 combined import claim must wait for an actual compatible-object check. No such claim is made here.
