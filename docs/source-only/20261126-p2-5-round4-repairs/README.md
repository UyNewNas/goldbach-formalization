# P2 round 4: deduplicated dependency repairs

**Status: source package prepared for review; the eight selected files have not been compiled in the current P2 context.** Production sources and all original verification drivers were unchanged while this package was prepared.

Round 3 completed its normal phase with 325 of 377 modules successful: 315 qualified reused results and ten new normal successes. It left eight direct failures and 44 dependent modules blocked. Its unchanged 69-target owned audit accepted 38 targets. This package addresses the eight direct failures, with no new mathematical theorem, hypothesis, definition or algorithm.

## Selected sources

Each `before/ImbalancedChen/` file is the exact source recorded by the round-3 failure. Each `after/ImbalancedChen/` file is the proposed replacement. `REPAIRS.patch` is the complete difference.

| Owner | Actual diagnostic | Selected repair and provenance |
| --- | --- | --- |
| `P4AOriginalFirstFailureH3SourceSemantics` | Two residual goals in `h3_eval_common` were left outside the final tactic sequence. | Exact existing round-3 candidate; apply the existing `first / rfl / ring` alternatives to all remaining goals. |
| `P4AOriginalH5H7SourceDispatch` | The complete log reports 11 unused simp arguments in each of `h5_priority_rows` and `h7_priority_rows`. | Existing candidate completed by removing the 13 reported entries omitted from the truncated-log draft. All 22 removals are identified by the original log. |
| `P2OriginalFourthCapProducerInterface` | Addition orientation, shadowed `B`, finite-index normalization, min/max API names, cast transport and folded predicates. | Exact previously compiled source from historical batch 39, source SHA-256 `cb5ed8d9c1095d2fc460ed4426ab430db9543944508c58409d9a2906db723ade`. |
| `P1OriginalHistoricalPhysicalCoefficient` | The proof referred to an unqualified distribution-cap name. | Exact previously compiled source from historical batch 48; it also matches the earlier round-3 candidate. |
| `P1OriginalCoarseFourthCellIntegral` | A pointwise function subtraction and two lambda applications were still folded. | Exact previously compiled source from historical batch 38, using `Pi.sub_def` and `dsimp only`. |
| `P5OriginalAdoptedEighthPhysicalMasks` | Three strict linter errors for unnecessary `<;>` sequencing. | Exact existing round-3 candidate, replacing only the three reported sequences. |
| `P4AActualEighthInheritedHistoryGuard` | `Fin.last` versus a literal index, followed by a finite-index normalization goal. | Exact previously compiled revision-2 source from historical batch 80. |
| `P2OriginalAffineSimplexGeometry` | One unused simp argument and a deprecated set-membership lemma name. | Exact existing round-3 candidate, removing `mul_assoc` and using `mem_ofPred_eq`. |

The four historical preimage hashes match the current failing source bytes exactly. Their normal compilation and independent kernel-replay command receipts both report exit zero, and the retained original logs were checked against the receipt hashes. Historical batches 38 and 39 audited public exports; batches 48 and 80 audited complete owned declarations. These are historical facts, not current P2 acceptance receipts.

The producer source has one explicit statement-spelling correction: the previously unelaborated `oldComponent_vector` header used the parent namespace's natural-valued `B` on a real argument. The selected source writes the existing real-valued `VariableEnvelope.B` explicitly. The original full log records the type mismatch. All six components, constants, quantifiers and hypotheses remain as in the historical reviewed correction; no equivalence to a previously elaborated erroneous kernel type is asserted.

## Evidence and scope

`SOURCE_SELECTION.json` records all eight full-log hashes, source hashes, historical commits and receipt scope. The original complete logs are preserved under `docs/verification/20261126-p2-5-resumed/`; the JSON export binds each log to the original record-selected path. `historical/` retains lightweight original receipt copies and provenance. Large historical raw logs remain referenced by immutable commit/path and their independently checked hashes.

`STATIC_VERIFICATION.json` records lexical source checks. All scanned non-theorem command chunks are identical. All theorem statement prefixes are identical except the single producer name qualification described above. Imports and options are identical, and no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide` was added. These checks do not substitute for Lean elaboration or kernel replay.

Historical object reuse is not asserted. Although the toolchain and package manifest match, the historical source trees have changed dependency files, and the current P2 environment has an explicitly qualified native snapshot. The new run preserves its own records and lets the unchanged drivers determine reuse.

## Resume wrapper

`docs/verification/20261126-p2-5-resumed/run_p2_round4.py` imports the exact original round-2 helper definitions without running their main function. It preserves the prior result, records, audit summary, all 69 latest audit receipts, and the prior attempt files before checking out the reviewed publication. It verifies the old 377-source table, substitutes exactly the eight selected hashes, and verifies the resulting physical sources and unchanged imports after checkout.

The wrapper runs the existing compile driver once with the same five roots, one worker, one thread, 11264 MiB heap and 1400-second budget, then runs the existing audit driver on the same 69 targets. Four repaired files are dependency-only in that audit scope: the producer interface, historical coefficient, fourth-cell integral and inherited-history guard. They receive normal strict compilation through the 377-module closure. The four repaired audited owners are placed first without adding targets.

The original acceptance predicate remains 377 successful modules and 69 accepted owned audits, plus unchanged source, gate, external-context, checkout, baseline and preserved-history checks. The source selection is pinned by SHA-256. The caller must supply the reviewed wrapper hash and a full publication commit, and materialize the wrapper outside the old checkout before execution:

```text
python3 MATERIALIZED_RUNNER.py PUBLICATION_COMMIT --runner-sha256 REVIEWED_RUNNER_SHA256
```

The wrapper refuses to overwrite an existing attempt-004 directory or round-4 audit summary. It preserves the original 1 GiB free-space requirement and records partial or failed results without claiming acceptance. No cloud execution or Git push is performed by this preparation package. `P2_5_proved` remains false.

The focused local test command is:

```text
python3 -B docs/source-only/20261126-p2-5-round4-repairs/test_run_p2_round4.py
```
