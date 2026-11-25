# Gamma5 actual-source dependency handoff

This handoff resolves the **original, manifest-pinned** `ImbalancedChen.P2FiniteMarkedGamma5LogExtension` project graph: **176 source modules, 155 active and 21 archived; no absent or ambiguous project source**. It preserves the heavy arithmetic-source closure for subsequent validation. The separately extracted constants/profile, derivative budget, and physical extension are outside this frozen graph. This inventory performed no compilation, replay, remote submission, or active Lean edit.

The machine-readable companion is `GAMMA5_DEPENDENCY_RESOLUTION.json`. It includes every selected source path, SHA-256, import list, install path, dependency order, donor alternative, and direct native boundary. All paths below are relative to the current P2 checkout unless explicitly identified as P1.

## Source identities and reuse

- P2 checkout: `ac9e6404a9ff7e2f980da6eaa8b80a19677044c6`. The original target is `docs/source-only/20261124-p2-gamma5-log-extension/ImbalancedChen/P2FiniteMarkedGamma5LogExtension.lean`, SHA-256 `3ecc727198a6efcd45fe9205883e3397b46d487af974f7aca55306ca464089f6`.
- The pinned arithmetic supplier is `docs/source-only/20261102-resume-30s/s16_gamma5_and_costs/P2EnhancedBadGamma5ArithmeticGeometry.lean`, SHA-256 `53f0e246929d51ee338b56880d4ae773dcf0bacda0e2f251357cbe9e940d0019`.
- The pinned smooth gate is active `ImbalancedChen/P4BSmoothGateUpperStep.lean`, SHA-256 `7f51e436ec635bf89fbcf69f02e8c35f8b1a46df1183322f04c61dc69ea43764` (7103 bytes). The older density manifest records a different 7101-byte identity, SHA-256 `4a4f83fb9c1de975235ed538bd8933006d9e047b5b2cb587be238d105f90fe9b`; do not overwrite the explicit Gamma5 choice with that older metadata.

Exactly **101** selected project source hashes match the existing 247-owner source census; **75** reached project names are outside it. There are no differing source hashes in that overlap. The census itself records no cache acceptance, so these are source comparisons, not automatic object-reuse receipts. Of the active P2 sources, 149 also match the P1 active tree and six have the existing repair alternatives below. Reached archive candidates had no competing different-byte identities.

## Staging sequence

1. Compare the live remote sources and accepted records with the JSON source hashes and import signatures. Preserve any already-qualified live repair. Use the original graph as a baseline for the heavy arithmetic closure; reconcile the separate lossless extraction explicitly before compiling a changed final caller.
2. For an unchanged baseline source matching one of the six donor preimages, reuse its documented P1 repair instead of re-solving the same elaboration problem. Stage only the archived sources still absent remotely, using the destination module path in the JSON. Do not apply a global same-basename overlay or broad candidate installer.
3. Check the 21 extra direct native roots below against the current native checkpoint and exact package sources. The four archived native copies are only available source bytes; their transitive dependencies still need to be resolved in the existing native environment. Reuse qualified native signatures where they match.
4. Once that native boundary is qualified, validate the heavy target `ImbalancedChen.P2FiniteMarkedGamma5LogExtension` in the established strict driver, followed by independent replay and the complete owned-declaration audit. The additional `P2FiniteMarkedGamma5SeedPlateau` caller requires its own reached closure; it is not covered by this inventory.

### Archived project sources, in dependency order

The destination for each row is `ImbalancedChen/<module>.lean`; full hashes are in the JSON.

| Module | Selected archive path |
|---|---|
| `P2EnhancedSwitchedUnsiftedSource` | `docs/source-only/20261102-resume-30o/enhanced_switch_mass/P2EnhancedSwitchedUnsiftedSource.lean` |
| `P2OriginalChildPhysicalNormalization` | `docs/source-only/20261102-resume-30m/h247_w2_mass_license/P2OriginalChildPhysicalNormalization.lean` |
| `P2EnhancedSwitchedTrueNormalization` | `docs/source-only/20261102-resume-30o/enhanced_switch_mass/P2EnhancedSwitchedTrueNormalization.lean` |
| `P2EnhancedUnitSourceGeometry` | `docs/source-only/20261102-resume-30p/enhanced_switch_mass/P2EnhancedUnitSourceGeometry.lean` |
| `P2OriginalBankChildPrimeMass` | `docs/source-only/20261102-resume-30m/h247_w2_mass_license/P2OriginalBankChildPrimeMass.lean` |
| `P2OriginalBankThetaMassLimits` | `docs/source-only/20261102-resume-30m/h247_w2_mass_license/P2OriginalBankThetaMassLimits.lean` |
| `P2OriginalCompactMovingGateMass` | `docs/source-only/20261102-resume-30o/h247_moving_mass/P2OriginalCompactMovingGateMass.lean` |
| `P2OriginalCompactScaledPrimeMass` | `docs/source-only/20261102-resume-30o/h247_moving_mass/P2OriginalCompactScaledPrimeMass.lean` |
| `P2OriginalCompactThetaMass` | `docs/source-only/20261102-resume-30o/h247_moving_mass/P2OriginalCompactThetaMass.lean` |
| `P2OriginalPositiveSameQMassLift` | `docs/source-only/20261102-resume-30o/h247_moving_mass/P2OriginalPositiveSameQMassLift.lean` |
| `P2EnhancedUnitSourceMass` | `docs/source-only/20261102-resume-30p/enhanced_switch_mass/P2EnhancedUnitSourceMass.lean` |
| `P2EnhancedNonunitPhysicalQuadrature` | `docs/source-only/20261102-resume-30q/enhanced_nonunit/P2EnhancedNonunitPhysicalQuadrature.lean` |
| `P2EnhancedNonunitLabelGeometry` | `docs/source-only/20261102-resume-30q/enhanced_nonunit/P2EnhancedNonunitLabelGeometry.lean` |
| `P2EnhancedReceiverRoughPurification` | `docs/source-only/20261102-resume-30p/enhanced_switch_mass/P2EnhancedReceiverRoughPurification.lean` |
| `P2EnhancedNonunitWordMass` | `docs/source-only/20261102-resume-30q/enhanced_nonunit/P2EnhancedNonunitWordMass.lean` |
| `P2EnhancedBadGamma5ConstantCutoff` | `docs/source-only/20261102-resume-30r/gamma_costs_units/P2EnhancedBadGamma5ConstantCutoff.lean` |
| `P2EnhancedBadGamma5PrimeQuadrature` | `docs/source-only/20261102-resume-30s/s16_gamma5_and_costs/P2EnhancedBadGamma5PrimeQuadrature.lean` |
| `P2EnhancedNonunitMarkedMass` | `docs/source-only/20261102-resume-30q/enhanced_nonunit/P2EnhancedNonunitMarkedMass.lean` |
| `P2EnhancedShortWordUnitBound` | `docs/source-only/20261102-resume-30r/gamma_costs_units/P2EnhancedShortWordUnitBound.lean` |
| `P2EnhancedBadGamma5ArithmeticGeometry` | `docs/source-only/20261102-resume-30s/s16_gamma5_and_costs/P2EnhancedBadGamma5ArithmeticGeometry.lean` |
| `P2FiniteMarkedGamma5LogExtension` | `docs/source-only/20261124-p2-gamma5-log-extension/ImbalancedChen/P2FiniteMarkedGamma5LogExtension.lean` |

## Existing P1 donor repairs

The following sources and their validation receipts all byte-match immutable P1 commit `99c1f8ba1dc453b21f47e30b667db0de93d73387`; the observed donor HEAD was `14278e45f9627539f54a16c24ca648a46eaa0e9c`. Sources live at `ImbalancedChen/<module>.lean` in `/workspace/scratch/cba105ac8c38/goldbach-p1`. Their exact preimage/postimage hashes, normal and kernel commands, log hashes, receipt paths, and receipt hashes are retained in the JSON. All six historical normal builds and independent kernel replays exited 0. The audit scopes differ and must retain their historical credit.

| Module | P1 repair batch | Historical export audit | Existing repair |
|---|---|---|---|
| `P2SeedOmegaQuotientUnitCarrierExact` | 18 | public only 10 | Existing Nat.div_self API repair: pass the positivity premise directly. |
| `P5OriginalFeedbackTableKernels` | 85 | full owned 18 | Existing simp repair: explicitly unfold weightedTable. |
| `Part5RenewalTablePrimitive` | 66 | full owned 52 | Existing singleton/set-predicate normalization and explicit change repair. |
| `Part5UpperTableLookup` | 26 | public only 31 | Existing lookup proof repair: explicitly unfold Set.indicator. |
| `P5ZU11CanonicalSwitchedIntegrable` | 54 | full owned 22 | Existing ENNReal scope repair and source status comment. |
| `P5ZU11MeasurableEnvelope` | 32 | public only 47 | Existing witness, classical, guarded, Measurable.ite, and if_true proof elaboration repairs. |

These historical receipts establish reusable repair provenance. They do not accept the current P2 dependency context, and the public-only audits are not full owned-declaration audits.

## Native environment boundary

The reached project graph imports **37 direct MathlibNt roots**. Sixteen occur in the old owner/native source census. **21 are outside that census**, listed below; only four of these have source bytes found in the prior targeted local archive lookup. The other 17 have unresolved local availability, not a finding that they are missing from the current remote package. The old package pin is `goldbach` commit `09b97db5764ade1246bfb77206baa1b124760958`.

| Direct root outside old census | Local archived bytes or metadata |
|---|---|
| `MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherOriginalWindows` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.BoxMassTheta` | Metadata only in `docs/source-only/20261112-resume/t01/density-validation-v2/NATIVE_RESEARCH_OVERLAY.json`; no local source bytes found. |
| `MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitPrimeOutput` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.ReboxingNormalization` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.ImprovementCrossLower` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.GeoMassElementaryPrimitives` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.GeoMassOriginalBlocks` | `docs/source-only/20261102-resume-30s/s16_gamma5_and_costs/native/GeoMassOriginalBlocks.lean` |
| `MathlibNt.Wu2008DoubleSieve.GeoMassOrderedPure` | `docs/source-only/20261102-resume-30r/gamma_costs_units/native/GeoMassOrderedPure.lean` |
| `MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitChamberIntegral` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceGeometry` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitBoxedLimit` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitClosedQuadrature` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitFiniteKernelBound` | `docs/source-only/20261102-resume-30r/gamma_costs_units/native/SecondFunctionalUnitFiniteKernelBound.lean` |
| `MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitTupleGeometry` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.Omega3FiniteError` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.InclusiveRoughUniform` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation` | No local source bytes found by the prior targeted lookup; inspect existing remote package/research source. |
| `MathlibNt.Wu2008DoubleSieve.Gamma5MassQuadrature` | `docs/source-only/20261102-resume-30r/gamma_costs_units/native/Gamma5MassQuadrature.lean` |

`docs/source-only/20261102-resume-30s/s16_gamma5_and_costs/REGISTRY.json` preserves additional native source provenance, and the older research overlay supplies the `BoxMassTheta` path, blob, size, and imports. Neither constitutes a qualified native closure. In particular, staging four direct-root copies cannot establish the entire native import graph.

## Validation boundary

This handoff checked the saved source graph and its topological dependency order, exact source hash overlap with the old census, and 12 immutable-commit donor source/receipt identities. It does not claim that the original arithmetic target, its actual-source plateau, the future caller, or full P2 has passed. Preserve the existing literal arithmetic objects when completing that integration.
