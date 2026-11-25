# P1.5 actual fourth and fifth means

`run_selected.py` checks the 304 published project sources leading to the two mean theorems, the four protected roots, and the reviewed member compiler configuration. Pass full module names from the 23-owner list. It orders selected owners using their imports. The existing `P1OriginalFourthFifthTotalTupleSource` object supplies an import and is excluded from the list.

```sh
python3 -B run_selected.py --source-commit "$source_commit" --check --targets \
  ImbalancedChen.P1OriginalFourthUntruncatedIntegral
python3 -B run_selected.py --source-commit "$source_commit" --run --targets \
  ImbalancedChen.P1OriginalFourthUntruncatedIntegral
```

Both commands use the existing member project and source repository. The source commit must already exist there and match the installed sources. The static check reads files and Git objects. Execution uses the existing lane-0 serializer and guard. For each owner, the pinned Batch13 API checks direct dependency readiness with Lake, requires one normal build or a matching normal receipt, and immediately runs or revalidates its kernel and full-owned declaration audit. A ready target without a matching normal receipt, a previously failed or interrupted normal for the same commit, or a partial audit is held for inspection.

Per-owner receipts live under `/workspace/p1-complete-proof/20261125-p15-actual-means-v1/<source-commit>/<module>/`. Each dispatch writes source/runtime snapshots, Git state, command logs, and a `RESULT.json` under the sibling `runs/attempt-*/` directory. A successful exit covers only the selected owners.
