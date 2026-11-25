# Original ordinary schedule: mechanical source-only extraction

**Status: source-only, uncompiled, no acceptance or P2.5 credit.** This package
changes declaration ownership and imports so the existing original ordinary
integral and common schedule do not require the unrelated closed numerical
endpoints. It introduces no mathematical statement, estimate, hypothesis,
parameter choice, or replacement source.

## Exact changes

The six existing declarations retain their original namespaces. Five complete
declaration commands are byte-identical. The sixth is the existing
`with_common_history` helper: its statement and proof are unchanged, and only
`private` is removed, as explicitly authorized by the parent task. Its old
saved-endpoint caller and the moved ordinary-source caller still use the same
source name. The compiled private declaration identity necessarily changes;
this is recorded separately from the five byte-identical moves.

| Existing namespace | Declaration | New owner module |
| --- | --- | --- |
| `P4AOriginalFull87ActualSavedEndpoint` | `Scheduled` | `P4AOriginalFull87ScheduleDefinitions` |
| `P4AOriginalR17Full87SavedEndpoint` | `Ordinary` | `P4AOriginalR17OrdinarySource` |
| `P4AOriginalR17Full87SavedEndpoint` | `with_common_history` | `P4AOriginalR17OrdinarySource` |
| `P4AOriginalR17Full87SavedEndpoint` | `original_ordinary_source` | `P4AOriginalR17OrdinarySource` |
| `P4AOriginalArchiveFourteenPositivePresieve` | `schedule` | `P4AOriginalArchiveScheduleData` |
| `P4AOriginalArchiveFourteenPositivePresieve` | `data` | `P4AOriginalArchiveScheduleData` |

The three old definition owners remove these commands and import the new
owners. Their other declarations retain their exact bytes. The existing
selected `P4AOriginalR17PaidIntegral` imports the ordinary source directly.
`CompleteSixthChronology`, `CatalogFiveArchiveSchedule`, and
`Full87SourceDispatch` import the same archive schedule/data from its new owner.
These changes preserve the original archive bank and admission predicate.

The remaining import changes cut two unused routes into the old saved-gain
endpoints and retain the providers that their callers actually use:

| Owner suffix, after `P4AOriginal` | Import change |
| --- | --- |
| `OrderedThirdFullPolicy` | `NewFifthCounting` to `Full87DataPolicy` |
| `HistoricalFirstStop` | `ThirdFallbackPaidDensity` to `Full87RawChronology` and `P4ASameRhoCompact` |
| `HistoricalThirdOccurrence` | Add direct `ThirdFallbackAdmission` |
| `HistoricalThirdActualRoot` | Add direct `FourPositiveEndpoints`, `NewFifthUnion`, and `Full87JointPhysicalBudget` |
| `ThirdFallbackOccurrence` | `NewFifthPaidDensity` to `Full87RawChronology` and `NewFifthUnion` |

No declaration body changes in these import-only postimages. The final
`ThirdFallbackOccurrence` cut is necessary: keeping its old paid-density import
would otherwise reintroduce the saved-gain numerical path through the admission
chain.

## Preimages, context, and duplicate avoidance

`DECLARATION_IDENTITY.json` gives every origin, before/after SHA-256, literal
replacement, moved-command SHA-256, and the complete affected-owner list.
`before/` and `after/` contain the exact twelve selected preimages and postimages.
`ImbalancedChen/` contains only the three new owners.

The preimages are pinned by the existing
`20261125-p2-5-fourteen-family/PREIMAGE_CLOSURE_SELECTION_1688.json`, not chosen
from arbitrary current files. The `OrderedThirdFullPolicy` preimage reuses its
already recorded `published_install_transform`, which supplies
`producerEligible` from `P1OriginalVariableFourthContinuation`. Its untouched
archive origin is also saved under `archived-origin/`. This package adds no new
context repair to that source. `CompleteSixthChronology` retains its original
CRLF bytes.

`mechanical-owner-relocation.patch` is against the logical selected
`ImbalancedChen/<module>.lean` paths. In particular, its OrderedThird preimage
is the previously selected transformed source, not the raw archive origin.
Apply one postimage per module; do not load both an old definition owner with
its original declarations and the new declaration owner. The old heavy owners'
postimages are included to preserve their callers if they are later selected.

Existing `HistoryCore`, `IntegralDefinitions`, the retained negative finite
owners, and the targeted local original sources did not already export these
six declarations from a lightweight owner. This package therefore moves the
existing commands rather than introducing parallel definitions or new proofs.

## Static dependency reduction and its limits

`DEPENDENCY_REDUCTION.json` compares the same existing selection before and
after this patch. Its basis is the pinned 1,688-entry historical selection,
overlaid by the frozen 377-source round-2 selection, the seven existing negative
finite postimages, and the explicitly recorded existing fourteen-family
upstreams. All versions and transforms remain recorded. The report is an import
graph, not an installation map or a compilation receipt.

| Existing root | Before | After | Removed | Added | Missing source providers after |
| --- | ---: | ---: | ---: | ---: | --- |
| `P4AOriginalR17PaidIntegral` | 1,673 | 1,487 | 189 | 3 | None in the selected graph |
| `P2Saving16R17StrictFourteenCorners` | 1,698 | 1,512 | 189 | 3 | 2 |

Counts cover project module nodes only; the all14 counts include its two
unresolved nodes. No cycle was found in either declared graph. The known
`P4AOriginalFull87SavedGain`, `P4AOriginalFull87Saved86`,
`P2OriginalSaving16OwnedIntegral`, `P2OriginalSaving19OwnedSource`,
`P2OriginalSaving19OwnedIntegral`, and
`P2OriginalSaving20FirstFailureIntegral` paths are no longer reachable from
either root. Five generic Saving19 modules remain: `Archive`,
`MomentFloorConsumer`, `SimplexMoments`, `SourceJson`, and `SourceMeasure`.
Their existence in the graph is retained; this package gives them no new
acceptance credit.

The unresolved all14 source providers are the existing imports
`ImbalancedChen.P2Saving16ActionGatesClosedBox` and
`ImbalancedChen.P2Saving16OriginalPhysicalEightSource`. Targeted local filename
searches did not find their sources. Neither is replaced or recreated here.
The original negative-comparison donor was found and is recorded at its exact
existing path/hash in the graph. Historical sources whose paths need
materialization or previously recorded transforms still need that work before
an actual complete source selection.

Two preexisting duplicate-definition-owner corrections also remain necessary
for a full analytic installation:
`P4AOriginalFull87EighthKernelControl` and
`P4AOriginalFull87SourcePrimeTests`. Reuse their existing IntegralDefinitions
refactor hunks in
`docs/source-only/20261124-p2-winner9-original-full87/original-modules-refactor.patch`.
The seven negative finite postimages under
`docs/source-only/20261125-p2-5-fourteen-family/owners/` are likewise existing
inputs, not regenerated work in this package.

## Preserved common schedule and remaining estimate

`Scheduled` keeps the same quantifier order: trim and resolution, rational
strip, common mesh and displacement, then the even arithmetic target.
`with_common_history` still uses `min eo eh`, `max qo qh`, the same `N0`, and
the same signed-coefficient identity for every later modulus. `schedule` and
`data` still use the exact original fourth bank and admission filter.
The selected paid-integral source and same-coefficient endpoint keep their
entire theorem/proof bodies, including the shared beta, k, N0, Q and rho.

The already existing source
`docs/source-only/20261123-resume/ten-task-continuation/selected-api/ImbalancedChen/P4AOrderedThirdSameCoefficient.lean`
contains `joined_below`. It supplies the common schedule, compiler reserve,
density comparison, support, and the counting majorant with the same compiled
Q and rho. Its right-hand side still contains
`realPhysicalDistributionError b N T Q rho`, together with `ceil z` and `T+1`.
The existing fourteen-corner wrapper identifies that same error with its
fourteen-family expression; it does not bound the error.

The remaining actual distribution obligation is a quantitative bound for that
error on the exact compiled Q/rho and one shared beta/k/N0 schedule, strong
enough with the retained tails for the target endpoint. This is not an absent
wrapper or an interface compatibility issue. The extraction neither assumes
nor proves that estimate and supplies no new all14 integral, simplex, finite
cell, or P2.5 result.

## Verification and future selection

Only Python byte-identity, source/import metadata, and syntax checks were run.
An independent read-only review found no must-fix in the declared relocation
or byte replacements. Cropped imports can still affect elaboration or tactic
availability; only future strict execution can resolve that.

`SOURCE_SELECTION.json` selects the exact fifteen postimages and separates the
twelve changed owners reachable from the ordinary root from the three old
numerical endpoint owners retained for compatibility. A future ordinary-root
run need not compile those three unreachable heavy endpoints. None of those
three may be reported accepted without its own strict checks. Promotion of all
fifteen affected owners requires their full serialized/environment owned
inventories, including generated/private declarations, normal compilation,
kernel replay, and unchanged strict audit gates. The moved private helper's
new compiled identity must be included explicitly.

No production file, strict runner, acceptance selection, pending P2 task, or
cloud state is changed by this package. All finite-cell and P2.5 credit flags
remain false.

To verify the frozen literal transformation without installing sources or
running Lean:

```sh
python3 docs/source-only/20261126-p2-5-lightweight-original-schedule/verify_identity.py
```

`report_dependency_reduction.py` can reconstruct its static graph from the
recorded local source-selection inputs. It is not a compiler or acceptance
runner.
