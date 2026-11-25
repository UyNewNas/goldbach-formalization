# Reuse the published ordered-third mesh interfaces

The canonical `P4AOrderedThirdSameCoefficient` and `P4AOrderedThirdCommonSchedule` sources now exactly match their existing 20261123 `ten-task-continuation/selected-api` variants. The same bytes were already present in the cloud build project. This adoption writes no new proof and changes neither the historical packet nor the cloud project.

`SOURCE_SELECTION.json` records the original and selected hashes, Git blobs, packet manifest, actual cloud inspection, preserved wrapper-header hashes, and dependency checks. Both selected sources remain **uncompiled and unaccepted by this adoption**; the inspected cloud object facets were absent.

## Mathematical purpose

`joined_below` chooses the original aligned mesh below the payment tolerance, range tolerance, and an arbitrary positive `meshMax` in one call to `aligned_small`. `common_schedule_below` carries this bound through the same beta, `k`, target threshold, modulus carrier and physical coefficient. The original public `joined` and `common_schedule` statements are unchanged; their wrappers use `meshMax = 1` and discard the additional bound.

The pinned 1106 manuscript, `coefficient-appendix.tex` lines 252–257, requires the fine mesh to lie below the remaining positive reserves after the common beta choice and before the target grows. The packet's U04 strict-corner proof uses `meshMax = min (width r / 24) (eta / 2)` to establish its strict box margins without choosing a second coefficient instance.

## Scope and current dependencies

Current direct importers are `P4AOrderedThirdCommonSchedule` and `P4AOrderedThirdPhysicalAtoms` for `SameCoefficient`, and `P4AOriginalFiniteFallbackPolicy` for `CommonSchedule`.

The unchanged Batch5 graph helper verified that neither adopted module occurs in any of the four Batch11 repair source closures: UpperTaggedContinuationAccounting (296 modules), Saving19SimplexMoments (215), CommonRefinedPreservation (290), and PrimeEulerOperatorWords (100). Their union contains 342 project modules. This is a source-dependency check, not compilation evidence.

The downstream U04 consumers `P4AOriginalR17PaidIntegral` and `P2Saving16R17StrictFirstCorner` remain only in the existing source packet and have not been added to the canonical tree here. Their further project dependencies and selected source variants require a separate coherent selection. Adopting these two mesh interfaces does not establish the full U04 integration, a distribution estimate, kernel acceptance, or completion of P1.

## Bounded consumer source review

The two missing canonical consumers are `P4AOriginalR17PaidIntegral` (the Nov23 `selected-api/ImbalancedChen` source) and `P2Saving16R17StrictFirstCorner` (the Nov23 `ImbalancedChen` source), under `docs/source-only/20261123-resume/ten-task-continuation`. Use the selected PaidIntegral variant: it exposes `original_signed_density_and_count_below` and calls the newly preserved common-schedule interface. Neither consumer was installed.

PaidIntegral directly imports the existing `P4AOriginalR17Full87SavedEndpoint` and the adopted `P4AOrderedThirdCommonSchedule`. StrictFirstCorner additionally imports the absent canonical `P2Saving16FirstCornerReciprocalResidual`; its exact local source is `docs/source-only/20261122-resume/ten-task-continuation/ImbalancedChen/P2Saving16FirstCornerReciprocalResidual.lean`.

That residual imports existing `P2OriginalFourteenSignedRetainedLower` and two further absent canonical modules. Their historical sources were located and hash-verified at commit `9b1b19b44e756777738a8b37ef677429c60eb5e3`:

- `docs/source-only/20261120-p2-saving16-no-deletion/P2Saving16NegativeNoDeletion.lean`
- `docs/source-only/20261120-p2-saving16-upper-corner/P2Saving16ActualUpperCornerCap.lean`

The historical sources introduce three unresolved, absent canonical dependencies: `P2Saving16NegativeCoefficientComparison`, `P2Saving16SignedCorrectionFamilies`, and `P2Saving16ActionGatesClosedBox`. The upper-corner source's other direct import, `PrimeHistoryLogCoordinates`, exists. The review stops at this frontier; it does not claim a complete consumer source closure. Exact hashes, blobs, imports, and current existence are recorded in `SOURCE_SELECTION.json`. No consumer or dependency source was added, and no compilation or acceptance is inferred from these source checks.
