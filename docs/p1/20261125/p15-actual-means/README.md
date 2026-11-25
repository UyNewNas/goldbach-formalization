# P1.5 actual fourth and fifth means

[中文定理范围、参数和剩余义务](PROOF_SCOPE.md) · [历史依赖源码定位](history-source-recovery/README.md)

`run_selected.py` checks the 304 published project sources leading to the two mean theorems, the four protected roots, and the reviewed member compiler configuration. Pass full module names from the 23-owner list. It orders selected owners using their imports. The existing `P1OriginalFourthFifthTotalTupleSource` object supplies an import and is excluded from the list.

```sh
python3 -B run_selected.py --source-commit "$source_commit" --check --targets \
  ImbalancedChen.P1OriginalFourthUntruncatedIntegral
python3 -B run_selected.py --source-commit "$source_commit" --run --targets \
  ImbalancedChen.P1OriginalFourthUntruncatedIntegral
```

Both commands use the existing member project and source repository. The source commit must already exist there and match the installed sources. The static check reads files and Git objects. Execution uses the existing lane-0 serializer and guard. For each owner, the pinned Batch13 API checks direct dependency readiness with Lake, requires one normal build or a matching normal receipt, and immediately runs or revalidates its kernel and full-owned declaration audit. A ready target without a matching normal receipt, a previously failed or interrupted normal with the same source/dependency context, or a partial audit is held for inspection.

The wrapper also inspects retained owner history across source commits. A matching source/dependency/configuration/runtime context is held for evidence recovery or failure inspection, even when a documentation-only commit changed its path. Audit plans that lack a completed audit directory remain held. The pinned validator still decides whether a receipt is valid; this wrapper does not rewrite receipt identities. Six local regression tests cover these decisions at the external compiler boundary (`python3 -B test_retry_history.py -v`). They are orchestration tests, not Lean acceptance.

Per-owner receipts live under `/workspace/p1-complete-proof/20261125-p15-actual-means-v1/<source-commit>/<module>/`. Each dispatch writes source/runtime snapshots, Git state, command logs, and a `RESULT.json` under the sibling `runs/attempt-*/` directory. A successful exit covers only the selected owners.

## Review retained receipts

Run `python3 -B review_retained.py --source-commit <installed-full-sha> --output <summary.json>` after the 23 owners have completed. The reviewer checks each original audit and its normal receipt against the installed closure using the pinned validator. It writes a single summary containing the original receipt paths and SHA-256 hashes, owned and public declaration counts, before/after context, and any missing, ambiguous or rejected evidence. A successful exit requires exactly one currently valid audit per owner and stable project, receipt inventory and Git state. Choose a new output path if an earlier report differs.

## Export the completed review

Use the final review path below and a fresh sibling output directory. The exporter includes the entire receipt tree, the installed source closure, protected sources, reviewed configuration, guards, lane state, and audit template. Each tar member preserves its original path relative to `/workspace`. The exporter verifies the size and SHA-256 of the exact bytes it adds to the archive and rechecks the original files before publication.

```sh
evidence=/workspace/p1-complete-proof
review="$evidence/20261125-p15-actual-means-v1/reviews/actual-means-final.json"
python3 -B review_retained.py --source-commit "$source_commit" --output "$review"
python3 -B export_retained.py --source-commit "$source_commit" --review "$review" \
  --output-dir "$evidence/20261125-p15-actual-evidence-export-v1"
```

The deterministic tar format, embedded file index, xz compression and three SHA-256 checks come from `docs/p1/20261125/batch13-accepted-evidence/MCP_EXPORT_TASK.json` (SHA-256 `e64af9f0caec92ce4e155924b02b3823e895f6c161a2692458066020c24a9ff2`). After transfer, run `python3 -B verify_export.py verification.tar.xz SUMMARY.json --repo <local-repository>`. It verifies the compressed archive, uncompressed tar, embedded index, every indexed member, the 304 published sources, and each original normal/kernel/owned-declaration receipt. This offline check invokes no compiler.

## Bounded repairs

`install_repairs.py --source-commit <full-sha> --manifest docs/p1/20261125/p15-actual-means/round-01/SOURCE_REPAIRS.json` installs only the six recorded changed sources. It verifies their exact failed preimages, all unchanged imports and the complete 304-source context, saves the preimages, and uses the existing lane-0 serializer and pinned install helper. It leaves the original dirty Git worktree intact. Installation does not claim compilation. Run the selected owners afterwards with the matching published driver and source commit.
