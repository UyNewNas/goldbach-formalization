# P3.4 next independent endpoint audit — 2026-11-26

## Recommendation

First-accept the **already-written original cusp-one / literal Fricke Fourier phase interface**, centered on:

- `ImbalancedChen.Part3.ActualFrickeCuspPhase20261025a.sigmaOne_fourierCoeff_fricke_phase`;
- its final integrable form, `ImbalancedChen.Part3.ActualFrickeCuspPhase20261025a.integrable_sigmaOne_and_phase`.

Use the existing `Part3ActualFrickeCuspPhase.lean` source and its exact archived API repair, preserving the actual `normalizedScaling`, literal Fricke matrix, actual Gamma0 action, genuine lifted circle sections, normalized Haar Fourier coefficient and all signs. This is a valid source-complete next unit independent of `OriginalData`. It is more directly on P3.4's remaining cusp-normalization path than another elementary interval bound.

This is **first acceptance of existing source**, not a request to formalize a new Fricke foundation. Its existing canonical source-import closure has ten project modules and zero missing imports. Six modules are already packet-accepted; the four remaining existing owners require first acceptance. Static source availability is established here, not elaboration or kernel acceptance.

The allowed claim is the original cusp chart's exact relationship to the literal Fricke trace, at each positive height and each signed integer frequency. It is not DI/Whittaker coefficient identification, the ABL dilation identity, an oldform packet norm bound, a full continuous-spectrum normalization, or completion of P3.4.

## Scope and frozen observations

- Repository inspected: `/workspace/library-files/p34-proof-work`.
- Worktree HEAD before and after the reads: `da576de2c91df467d1865baee9c1b1b84ddc529b`; status was empty.
- Manuscript: `UyNewNas/chen-imbalanced-semiprimes`, commit `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`, `paper/release-20261106/en/analytic-appendix.tex`; local frozen copy `/workspace/scratch/dcb7c80f70a4/analytic-appendix-1106.tex`.
- Existing P3.4 finite source `97d5de82f2fd4e3d72fc86347ab40f00cc939a33`, fourteen modules / 235 inventoried declarations, is done. The seven theorem endpoints and `actualDyadicBeta` are not candidates for repeated proof or acceptance.
- Root supplied resident P3.1 tip `c3999ccf0dfb1a623c58c92decb758ec3b1c8f5a`; only its named acceptance files were read. No fetch, checkout, branch change, compilation, cloud submission, tracked-file edit or historical archive extraction was done by this audit.
- This report is the only file written by this audit.

## Exact source provenance

All five files below are directly present as Git objects at the resident donor commit `fa22a56829ee880404516a36d498ce27dcb32f92`. This identifies an exact reproducible donor; it does not claim that the commit is the globally earliest creation. The November 2 R22 registry predates the modern P3.4 work and records the original and repaired source hashes independently.

| Source path | Git blob at donor | SHA-256 / bytes |
| --- | --- | --- |
| `ImbalancedChen/Part3FrickeNormalizer.lean` | `8afb93b40fcd7797c1445ce6fc70ab26d2884c74` | `a714e2a5471d760e8308509f637626559427e27cce2b34beb552dbc9756908c9` / 8,879 |
| `ImbalancedChen/Part3Gamma0GeneralCuspWidth.lean` | `38dc5f712cd8a9b9a1f9dbec1a31efcf61421ae9` | `f22801b7f22f5ba5917579486a46d1be22fb11f99f814b398c8dd0344324dc30` / 8,304 |
| `ImbalancedChen/Part3Gamma0GeneralCuspUnitPeriod.lean` | `9d690658ea5429f0a8dec230f5cecce5b4c1f98d` | `0700be815a2a9dd95d4107b4a1d844375f296683c003a3c0628d1b7f91040446` / 10,776 |
| `ImbalancedChen/Part3ActualFrickeCuspPhase.lean` | `5bedd570c27e4741bec288e39d4d47369640b161` | `4b9366fc9d44c9713634747797d6a429e6e11a62a723d91e56468e53ee2a2b74` / 7,578 |
| `docs/source-only/20261102-resume-30r/oldform_continuous/repairs/Part3ActualFrickeCuspPhase.lean` | `8b47c8a7f053af911e13009e2a2676f9968f572c` | `749882d348253efdfb33387299a30653f0484b0810eeac84a761c2433609fddf` / 8,053 |

The last file consists exactly of its added nine-line explanatory header followed by the original file with all five occurrences of `AddCircle.fourier` replaced by `_root_.fourier` (including the `fourierCoeff` and `fourier_coe_apply` prefixes). Direct text comparison confirms this. The `AddCircle.haarAddCircle` measure is unchanged. The registration is `docs/source-only/20261102-resume-30r/oldform_continuous/REGISTRY.json`, `repairs` entry for `ImbalancedChen.Part3ActualFrickeCuspPhase`, with `literal_body_match_after_header: true`, `replacement_occurrences: 5`, and `historical_hold_not_overridden: true`.

The source-location inventory at `docs/source-only/20261026b-code-only/batch34/import-inventory.json` records the same four original owner blobs as `PUBLISHED_EXACT_CURRENT_BYTES`, imported through `UncompiledContinuation`. That is source provenance, not a successful compiler receipt.

## Exact terminal declarations and statement

Every name in the following table has prefix `ImbalancedChen.Part3.ActualFrickeCuspPhase20261025a.`. Original-file lines are given first, repaired-file lines second.

| Declaration | Lines | Role |
| --- | --- | --- |
| `newSL_eq_translation_fricke` | 28 / 37 | Proves the actual matrix equality `newSL = T * frickeSL`. |
| `original_cuspOneScaling_eq_fricke` | 35 / 44 | Binds the genuine width-normalized cusp-one scaling to `(T * W_N) * T_(1/N)`. |
| `frickeTrace` | 41 / 50 | Evaluates the original function on the literal Fricke action at a positive height. |
| `newTrace_eq_frickeTrace` | 47 / 56 | Removes the actual integral `T` using genuine Gamma0 invariance. |
| `frickeTrace_periodic` | 56 / 65 | Transports the already-established period-one property. |
| `frickeSection` | 62 / 71 | Lifts that actual periodic trace to `UnitAddCircle`. |
| `sigmaOneSection` | 69 / 78 | Lifts the trace from the actual `normalizedScaling N hN cuspOneMatrix`. |
| `newSection_eq_frickeSection` | 74 / 83 | Identifies the already accepted new-chart section with the literal Fricke section. |
| `sigmaOneSection_eq_oldSection` | 82 / 91 | Identifies the actual normalized cusp-one section with the accepted old-chart section. |
| `sigmaOneSection_eq_translated_frickeSection` | 91 / 100 | Retains the real translation `cuspShift N`. |
| `frickeFourierCoeff` | 99 / 108 | Takes the genuine circle Fourier coefficient of the Fricke section. |
| `fourier_cuspShift_int` | 104 / 113 | Expresses the signed integer translation factor as its complex exponential. |
| `sigmaOne_fourierCoeff_fricke_phase` | 111 / 120 | Main manuscript-facing Fourier phase endpoint. |
| `integrable_sigmaOneSection` | 121 / 130 | Transports an actual normalized-Haar integrability premise. |
| `integrable_sigmaOne_and_phase` | 129 / 138 | Packages integrability and the same exact Fourier identity. |

The repaired main statement, with its original proof body, is:

```lean
theorem sigmaOne_fourierCoeff_fricke_phase (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    _root_.fourierCoeff (sigmaOneSection N hN F hF y hy) n =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ)) *
        frickeFourierCoeff N hN F hF y hy n := by
  rw [sigmaOneSection_eq_translated_frickeSection]
  simpa only [fourier_cuspShift_int, frickeFourierCoeff] using
    fourierCoeff_translated (frickeSection N hN F hF y hy) (cuspShift N) n
```

No Fricke-eigenfunction hypothesis, desired coefficient identity, fabricated spectral structure, `FixedBlock`, `OriginalData`, arbitrary substitute weight, or assumed row norm is introduced. The function's actual Gamma0 invariance is the hypothesis that removes `T`. The final integrable theorem additionally requires `Integrable (frickeSection ...) AddCircle.haarAddCircle`; it does not silently supply that analytic fact.

## Existing ten-module closure and reuse

The terminal has exactly these two direct project imports:

```lean
import ImbalancedChen.Part3FrickeNormalizer
import ImbalancedChen.Part3Gamma0GeneralCuspUnitPeriod
```

The unrevised existing file-level closure is:

| Module | Existing direct project imports | Receipt disposition |
| --- | --- | --- |
| `Part3CuspPhaseCore` | none | Reuse packet receipt. |
| `Part3Gamma0ActualCusps` | none | Reuse packet receipt. |
| `Part3CuspScalingMatrices` | none | Reuse packet receipt. |
| `Part3ActualCuspWidthNormalization` | `Part3Gamma0ActualCusps`, `Part3CuspScalingMatrices` | Reuse packet receipt. |
| `Part3CuspTranslationFourierPhase` | `Part3CuspPhaseCore` | Reuse packet receipt. |
| `Part3ActualCuspFourierSection` | `Part3ActualCuspWidthNormalization`, `Part3CuspTranslationFourierPhase` | Reuse packet receipt. |
| `Part3FrickeNormalizer` | `Part3Gamma0ActualCusps` | Existing source awaiting selected acceptance. |
| `Part3Gamma0GeneralCuspWidth` | `Part3Gamma0ActualCusps` | Existing source awaiting selected acceptance. |
| `Part3Gamma0GeneralCuspUnitPeriod` | `Part3Gamma0GeneralCuspWidth`, `Part3ActualCuspFourierSection` | Existing source awaiting selected acceptance. |
| `Part3ActualFrickeCuspPhase` | `Part3FrickeNormalizer`, `Part3Gamma0GeneralCuspUnitPeriod` | Existing terminal with the recorded API repair. |

All names have prefix `ImbalancedChen.`. This is a static source-import closure; actual Lean-resolved imports and defining-module ownership still need the normal gate.

The six existing providers' current source SHA-256 values were compared directly against `docs/part3-distribution/p34-20261126/packet-cloud-report.json`, source **`145be87ff0a88914b607baa2a330bc88105a08d6`**, status `PASSED`; every value matches. Reuse those accepted objects and their source/object provenance when available. Do not recreate their proofs or count their declarations as new. The current finite endpoint receipt is unrelated to the four new owners and needs no repeated endpoint job.

The four original owner files contain 72 explicit source declarations (71 public): 22 + 16 + 19 + 15 (18 definitions and 54 theorems). The original audit undercounted by one because it omitted the private theorem `upperTriangular_signed_translation` at line 106 of `Part3Gamma0GeneralCuspWidth.lean`. The source provenance and file identities above still apply. This is a source-level count, not a generated declaration inventory or formal-credit count. Taking the existing four files avoids inventing a new provider/consumer API. Their mathematical statements and definitions should remain unchanged; if elaboration exposes another expression issue, diagnose it against these originals rather than weakening a premise or conclusion.

The crucial real provider names are `FrickeNormalizer.frickeMatrix`, `frickeMatrix_det`, `frickeSL`; `Gamma0GeneralCuspWidth20261025a.cuspWidth`, `cuspWidth_pos`, `cuspWidth_cuspOne`, `width_multiple_mem_gamma0`; and `Gamma0GeneralCuspUnitPeriod20261025a.integralReal`, `widthDiagonal`, `normalizedScaling`, `normalizedScaling_cuspOne`, `integralReal_smul`, `normalizedTrace`, `normalizedTrace_periodic`. The supplied matrix and period proofs exist. No missing original definition is hidden behind an abstract target-shaped interface.

## No-repeat evidence and the alternative finite candidate

1. The P3.4 current union (`p34-common-phase-20261126/ACCEPTED_SCOPE_UNION.json`) includes the six providers and none of the four new owners. Its already-accepted packet phase endpoints must stay credited and reused.
2. The R22 registry says the repaired Fricke phase source is source-only/uncompiled and preserves historical HOLD; its exact bytes are available. The known prefix repair was not presented as acceptance.
3. At root-supplied P3.1 tip `c3999ccf0dfb1a623c58c92decb758ec3b1c8f5a`, neither `p31-20261126-acceptance/ACCEPTED_SCOPE_UNION.json` nor `p31-kernel-lanes-20261126/verification/declarations.json` names these four modules. Neither the Poisson-lanes nor kernel-lanes verification report includes them among source/object providers.
4. The same P3.1 tip confirms that `Part3OriginalCommonPoissonLanesCore` is now accepted at source `d28d340b0240dc5cd8658893d07b61637ee94aa2`, and `Part3OriginalCommonPoissonKernelLanesCore` at `8e895502586ad41d5222ed5fd54386855b909b32`. Those provider proofs must not be re-created or re-submitted as new work.

There is a legitimate but less direct finite follow-up in the unchanged donor `docs/source-only/20261102-resume-30q/actual_spectral_energy/Part3OriginalClassicalSpectralSupports.lean`, donor commit `fa22a56829ee880404516a36d498ce27dcb32f92`, blob `00ea3113f35c8063519d8889ed3744b13d24d48d`, SHA-256 `17ef27e3c8d982eb49bef412d839758e2dc8d150c7818611972f07c6d5d2dbf0` (8,707 bytes):

- `OriginalClassicalSpectralSupports20261102.classicalMScale` (34), `classicalMScale_bounds` (36), `commonMBlock_classical_support` (49), `commonPoissonCompleted_classical_support` (64);
- `classicalLevelScale` (111), `classicalLevelScale_bounds` (113).

The first four retain the genuine `commonMBlock` and `commonPoissonCompleted.weight` and show that the inclusive-left interval fits `(2^j - 1/2, 2(2^j - 1/2)]`, with length at least `1/2`. The physical phase still uses `2^j`. These exact finite consumers are not in the inspected acceptance inventories. An exact extraction could import the now-accepted common-Poisson core; the original whole file instead imports `Part3OriginalRowPhysicalScalar` and `Part3OriginalAdditionalSpectralCosts`, inheriting unresolved `OriginalData`. The two `classicalLevelScale` facts alone are merely elementary bounds until bound to the actual original level row. The later `original_nonzero_row_classical_length`, `original_fixed_level_A_range`, `original_levelChart_one_le`, `original_level_classical_cover`, and `original_J_threshold_comparison` still require that genuine original row. Do not replace it.

This establishes bounded no-repeat evidence for the selected scope and known adjacent receipts, not a universal claim about every unadvertised private source or receipt.

## Manuscript correspondence, material advance, and residual boundary

| 1106 lines | What is actually addressed |
| --- | --- |
| 951–958 | Actual trivial-character level and displayed cusp-one scaling. `normalizedScaling_cuspOne` and `original_cuspOneScaling_eq_fricke` retain both square-root factors. |
| 960–962 | Geometric cusp conversion and its signed exponential. The selected endpoint proves the original section's Fourier phase against literal Fricke action. It does not by itself prove the cited Kloosterman conversion theorem. |
| 964–971 | The selected geometric phase becomes a precise supplier for later actual normalized-dilation integration. It does not prove `R_v(a*nu*n) = lambda_v(a*nu) e(n(a*nu-1)/z) R_v(n)`. Accepted scalar phase cancellation remains reused. |
| 972–982 | ABL/Frobenius/packet norm and full continuous Plancherel application are still separate; no common eigenvalue across dilations may be introduced. |
| 988–1024 | Maass, holomorphic and Eisenstein `R` definitions, radial normalization and all three measures remain uninstantiated by this fixed-height theorem. |
| 700–717, 999 | The alternative classical-support unit concerns the actual common interval and minimum support length, preserving the phase. It supplies support qualification, not a spectral estimate. |

The selected work materially advances P3.4 because the accepted `oldFourierCoeff/newFourierCoeff` identities presently refer to the old/new matrix charts. The new accepted sink would connect them to the independently defined **literal Fricke trace** and the original general width-normalized cusp chart, an input explicitly consumed by the existing `ActualPrincipalCuspOneRemoval20261102r.principalCuspOneFourierCoeff_eq_phase` and its subsequent actual Fourier-to-amplitude chain. It is not another generic exponential cancellation theorem.

The next genuine spectral-source blockage after that interface remains the registered `ImbalancedChen.Part3ActualFrickeNonzeroFourier`, original author path `.lake/proof-continuation/source-reviews/drafts/20261026b-FrickeNonzero/Part3ActualFrickeNonzeroFourier.lean`, **8,079 bytes**, SHA-256 **`926ee1b5e78c1a714fcb91405b6c85cc0c8d09dd32ad61c9135c2f15359a27fc`**. Its recorded imports are `Part3CompletedIntegerNonzeroFourier` and `Part3ActualContinuedZeroCuspMean`. Its missing physical nonzero-Fourier theorem `completed_fricke_nonzero_integral_critical` is used by the already-written `principalFrickeFourierCoeff_eq_amplitude`; the phase theorem cannot replace it. Recovering that single file would not certify its full dependency closure or the full spectral normalization.

The genuine original finite-row consumers continue to require the previously registered `Part3OriginalMediumPhysicalE3Block` (6,566 bytes, SHA-256 `1ed9fec9d526f866fff9a29f9d8d0fa96d63def2a8b1e4e7a42ad759a8989982`) and factor-window closure. Those are outside this independent phase unit.

**Difficulty classification:** the known five-prefix repair is an expression/API issue. Original row and nonzero-Fourier attachment absence are source/integration blockages. No omitted elementary derivation needs to be invented for the selected phase unit: its proofs already exist. No substantive mathematical gap in the 1106 manuscript has been established by these observations. Actual DI/Whittaker normalization and ABL application remain real unclosed obligations; they may not be bypassed by identifying a fixed-height Fourier integral with a height-independent spectral coefficient.
