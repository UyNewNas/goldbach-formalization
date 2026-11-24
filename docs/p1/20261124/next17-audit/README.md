# Next17: reuse completed normal builds, audit the exact current context

Status: plan only. The 17 individual normal builds are evidenced by their original complete logs; new named kernel and full environment-owned type/axiom acceptance remains pending.

## Source binding

The fixed baseline is `2ab8216113394bce00f8d2d9d76de330541f1720`. Exactly three existing published source files from `48db3d603d632bc60037e149a55717832e4c04be` overlay that baseline. Their SHA256 and Git blob IDs match the actual cloud source recorded in both batch5 and batch7. `SOURCE_UPDATE.json` contains three preserve records (`cloud_source_mutation_required=false`): publish the same bytes in canonical Git and leave cloud bytes and metadata untouched.

The audit binds all **572** project source files. Each of the 17 targets' entire project import closure is present in its original normal source context and matches this expected context. The next 17 source repairs (the 15 batch6 failures plus ZeroCutoffLimit and MixedFrechetBudget) do not occur anywhere in the audit closure.

The three reused sources change only existing theorem proof bodies. Their imports, declarations, definition bodies, global options, variables and all 37 existing `by` theorem headers are byte-identical outside proof bodies. No new proof was written. Historical inventory classified these as published proof-only candidates. A search of 106 old blue `VALIDATION_RESULTS.json` files found no standalone owner receipt for these three; their downstream successful normals are not represented as new independent kernel/full-owned acceptance.

## Original normal receipts

Every selected module has an actual `✔`, `⚠` or `ℹ Built` header in the full raw log. The six log bindings include the **complete** Built set. Five original commands exited 1 because other targets failed; this plan credits only the explicitly Built modules.

| Original source commit | Selected modules | Original normal stages |
| --- | ---: | --- |
| `9612b73337f15bb9623cd44eb1ae46f21081eec1` | 6 | parent-1-normal (exit 0), first14-normal (exit 1) |
| `01f5bcc251cadb8d8548eef9b65c63b4b923723b` | 3 | ordinary-00-normal and ordinary-02-normal (both exit 1) |
| `2ab8216113394bce00f8d2d9d76de330541f1720` | 8 | repair-first-five-normal and repair-second-five-normal (both exit 1) |

### batch5_parent-1-normal

- `ImbalancedChen.P1OriginalFifthEnvelopeTerminalReduction`

### batch5_first14-normal

- `ImbalancedChen.P5ZU1011OriginalSixteenInteriorArithmetic`
- `ImbalancedChen.P1OriginalFifthAttainedRowBinding`
- `ImbalancedChen.P1OriginalVariableFourthSmallCellPointwise`
- `ImbalancedChen.P5ActualHBDyadicOccurrenceFamily`
- `ImbalancedChen.P4BActualSmoothFamilyWitness`

### batch6_ordinary-00-normal

- `ImbalancedChen.P4ACommonPolicyTaggedCompiler`

### batch6_ordinary-02-normal

- `ImbalancedChen.ActualThirdOriginalSixTentRoundedConsumer`
- `ImbalancedChen.P2Winner9CompleteSeedChronology`

### batch7_repair-first-five-normal

- `ImbalancedChen.P1OriginalVariableFourthBoundedSourceLimit`
- `ImbalancedChen.P5ZU1011OriginalSixteenResidualWalls`
- `ImbalancedChen.P1ActualVariableFourthFifthCellTestLimit`
- `ImbalancedChen.P1OriginalFourthIntegerCubeGateSemantics`

### batch7_repair-second-five-normal

- `ImbalancedChen.P1OriginalFourthDerivativeNumerator`
- `ImbalancedChen.P4BPhysicalBoundaryQuantifiers`
- `ImbalancedChen.P1HistoricalFifthSigned64Payload`
- `ImbalancedChen.P1OriginalFourthPackedParserCompleteness`

## Exact runner and execution

Use the unchanged runner at `docs/p1/20261124/normal-supplement-audit/run_parallel_acceptance_multibatch.py`, SHA256 `e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1`.

Prepare with `--plan <AUDIT_PLAN.json> --prepare-only`, then execute **only** `--plan <AUDIT_PLAN.json> --lane 1` inside the existing state1 serializer. The runner accepts `--receipt-root` if the same explicit root is used at preparation and execution. It has no `--root` option. Lane0 is deliberately empty and must not be launched; do not use the default dual-lane invocation. The exact runner already applies its guards, so add no outer guard around the audit.

The independent receipt root is:

`/workspace/p1-complete-proof/20261124-resume/batch5-batch6-batch7-next17-normal-supplement-acceptance`

All original gates remain: exact raw normal-log SHA and complete Built set; all 572 project-source SHAs; each target source plus five artifacts; stock `lake --no-build` before and after; named `leanchecker`; all environment-owned declarations including private/generated types and axioms; complete owner-name inventory and only standard axioms; source/artifact/log/plan invariance. Any mismatch must stop the audit.

No normal compilation is repeated. The completed Seed90, audit24, audit8 and prior13 groups are excluded as targets (135 distinct modules); imported ancestors remain strictly source-bound. The actual 90/24/8 complete receipts, including the 8-module result with 276 owned declarations, are bound in `PROVENANCE.json`.

## Files

`AUDIT_PLAN.json` is the runner input. `PROVENANCE.json` contains original commands, log paths, hashes, complete Built headers, target source commits/blobs, all current expected source metadata/imports, normal-context matches, and excluded complete receipts. `NORMAL_EVIDENCE.tar.xz` preserves all used original raw evidence bytes, including the six logs and commands, source-context records and the 17 published normal source inputs. `REUSE_MANIFEST.json` and `SOURCE_UPDATE.json` describe the three exact donor preserves; original donor sources and review patches are under `strip3-reuse/`.

`MANIFEST.json` is the publication file list. Local preparation scripts and the intermediate baseline `SOURCE_GRAPH.json` are excluded from that list. No cloud job, Lean, Lake, kernel audit or runner preparation was executed to create this plan. Current runtime readiness and whole-P1 completion are not claimed.
