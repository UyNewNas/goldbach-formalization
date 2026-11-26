# Round 8 continuation draft

Historical preparation note: the prerequisites below have since been supplied and the final preparer succeeded. See `README.md`, `SOURCE_SELECTION.json`, `RUN_CONFIG.json` and `OFFLINE_VALIDATION.json` for the final prepared state. This file retains the earlier pending state and is not an execution input.

This package continues the unchanged 377-module graph, 69 owned audit targets and five compile roots from round 7 at source publication `1e80a5fa2fa2dbb346dbdef5760a7361a8001a46`. It does not install production files or execute Lean. The current local repository HEAD is not the required P2 previous checkout.

The parent observed that round 7 completed its normal phase with 346 successful modules, including 339 reused modules and seven newly compiled modules. Its only direct normal failures were `P1OriginalVariableFourthRowModulusTransfer`, `P1OriginalVariableFourthCellTestLimit` and `P4AOriginalFull87Ownership`. This observation selects candidate identities; final counts, the prior result SHA and owned acceptance remain unbound until the complete original result and postflight evidence are available.

## Selected source scope

| Module suffix | Source preparation | Current status |
|---|---|---|
| VariableFourthRowModulusTransfer | Exact existing donor bytes from `round8-existing-reuse`; explicit arguments to the existing `profile4_row_le` | Candidate copied; historical standalone normal/kernel acceptance is not claimed |
| VariableFourthCellTestLimit | Exact existing donor bytes from `round8-existing-reuse`; existing continuous bound, qualified residual, indicator lemma name and congruence orientation | Candidate copied; original normal/kernel/owned evidence retained in the reuse package |
| Full87Ownership | Separate reviewer repaired the remaining two `source_kind_rows` finite-sum branches | Final postimage `1023637bdce71f2cfb2d2f9fd05ddfb1bba0174de8ae51044a9ad87a15c1e332`; two exact local diagnostic branches passed, whole-module current acceptance remains pending |

The existing `ProducerAttainedRowBinding` and `VariableFourthSourceCoefficient` repairs remain available only in the reuse inventory. Their round-7 executions were dependency-blocked, so they are not selected. `FifthAttainedRowBinding` is also not selected; its complete donor adds an import outside the current graph. No graph expansion is authorized by this draft.

## Preserved checks

The new runner is a narrow continuation of the immutable round-7 runner. It adds the round-7 runner/selection pins to all earlier control pins, reconstructs the graph through rounds 4–7, verifies the original completed result and compile/audit logs, and preserves attempts 1–7. All prior source, table, helper, baseline, external-provider, history, records, per-target receipt and postflight checks remain in place. The normal and audit commands, memory/thread/time settings and original 1 GiB disk minimum are unchanged.

One additional source-admission check reads actual `FAIL <module> <exit>` lines from the SHA-bound round-7 `COMPILE.log`. Each selected repair must be a direct executed failure and belong to the terminal failed scope. A dependency-blocked module cannot be selected merely because it appears in `failed_or_blocked`. The preparer also requires the two P1 postimages to match the existing reuse manifest exactly, with unchanged imports and options.

The compile driver continues to decide cache reuse from its existing source, dependency and environment signatures. The preparer rejects any repair whose reverse dependency closure would invalidate a previously successful normal module or a previously accepted owned target. No historical object is imported as current proof acceptance.

## Completion sequence

1. Obtain the original round-7 `RUN_RESULT.json` and `COMPILE.log`. The preparer expects local copies under `docs/verification/20261126-p2-5-resumed/p2-round7-attempt007/`; their bytes must match the actual remote artifacts. The execution driver independently reads and verifies the remote originals again.
2. Bind `PRIOR_RESULT_SHA`, `PRIOR_NORMAL_SUCCESSFUL`, `PRIOR_NORMAL_REUSED` and `PRIOR_OWNED_ACCEPTED` to that complete result, including the original postflight checks. Do not derive final acceptance from progress stdout.
3. Recheck the three exact preimages against the fixed round-7 publication, including the separately supplied final Ownership candidate; preserve all proof statements, definitions, imports and options. The final Ownership postimage has now been supplied; its failed intermediate attempt is retained separately and is not selected.
4. Run `prepare_p2_round8.py --write` to emit the final `SOURCE_SELECTION.json` and `RUN_CONFIG.json`. It validates all source pairs and computes the affected dependency closure against the complete prior result. It does not install production sources.
5. Independently review the final source and runner delta, then let the parent install the three reviewed production source bytes, publish and execute. The parent owns all cloud calls and Git operations.

`SOURCE_SELECTION.DRAFT.json`, `RUN_CONFIG.DRAFT.json` and `RUNNER_DELTA.DRAFT.patch` are explicit nonexecutable drafts. The runner and preparer reject the missing prior pins before any cloud filesystem access, output creation or Lean command. The final names are deliberately absent until the prerequisites are met.

## Local checks performed

Only three new offline boundary checks ran: unbound receipt/count rejection, direct failure versus dependency blocking, and the added round-7 control chain. The initial test invocation occurred before the new runner existed and reported three missing-file errors; it is retained only as development history, not presented as proof that the guard logic failed. After implementation all three targeted checks passed. A direct `prepare_p2_round8.py --write` invocation also stopped at the unbound prior receipt and emitted no final selection or config. No settled Lean tests, historical donor compilations, cloud stages or production changes were repeated.

This draft provides no new current-context formal credit and does not prove P2.5.
