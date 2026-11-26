# P2 round 8: three direct failures

The final candidate selection is bound to the completed original round-7 result. The source scope remains 377 project modules, 69 owned targets and five compile roots. No production source is installed by this package's preparer, and no current P2 acceptance is claimed before the parent runs the existing compile/audit gates.

## Prior result and reuse

The original `p2-round7-attempt007/RUN_RESULT.json` has SHA-256 `582a51b587ee14361aeeab66b7f127d63f14d31a238ba82062e90acdcbf369e3`. Its complete stdout-preserved bytes also match the independent remote export hash. The original compile and audit logs likewise match both the receipt hashes and that export.

Round 7 completed with 346/377 normal modules, including 339 reused modules and seven newly compiled modules. Its 45/69 accepted owned targets were reused. All seven postflight checks passed, while the aggregate result remained false because three direct normal failures blocked the remaining dependency closure.

The three selected repairs affect exactly those 31 failed or blocked modules, including 24 owned targets. No previously successful normal module or previously accepted owned target is invalidated. The existing qualified drivers still decide whether each retained object may actually be reused from its source, dependency and environment signatures.

## Exact candidates

| Module suffix | Selected postimage SHA-256 | Origin |
|---|---|---|
| VariableFourthRowModulusTransfer | `ade8a06270b2fba04d2d2d116b08b11ec9f975cdc4f4be0e6fb9cca5146d3f27` | Exact existing donor; standalone historical acceptance is not claimed |
| VariableFourthCellTestLimit | `a38a85f1f73eec6727c2918231f58a735b4881d07e5a77092732cc9f411f2992` | Exact existing donor with its original normal/kernel/owned evidence |
| Full87Ownership | `1023637bdce71f2cfb2d2f9fd05ddfb1bba0174de8ae51044a9ad87a15c1e332` | Two remaining finite-sum proof-expression branches; precise diagnostic and identity evidence are recorded separately |

All preimages match both source publication `1e80a5fa2fa2dbb346dbdef5760a7361a8001a46` and the graph reconstructed through rounds 4–7. Imports and options are unchanged; no placeholder or new axiom is added. The two P1 postimages are byte-identical to the earlier `round8-existing-reuse` inventory. The remaining same-import donors are not selected because their executions were dependency-blocked. The FifthAttained donor, which adds an external-to-graph import, is not installed.

## Continuation runner

The new runner retains all prior control pins and adds the immutable round-7 runner and selection. It checks the actual original round-7 result, compile/audit logs, reconstructed source closure and latest per-target receipts before creating attempt008. It preserves attempts 1–7, records and original baseline/external-source invariants. The input preparation, normal compilation, owned audit and seven postflight code blocks are identical to round 7 apart from the printed round label; proof flags, resource settings and the original 1 GiB disk minimum are unchanged.

The new admission check requires each source repair to appear as an executed `FAIL` in the original hash-bound compile log. It rejects selecting a merely blocked module. Three narrow offline checks cover missing prior pins, that direct-failure distinction and the new historical control chain; all three passed in the final version. `OFFLINE_VALIDATION.json` records the actual hashes and source-scope checks. The existing Lean and historical donor tests were not rerun.

Final publication invocation, after the independent reviews and parent-managed production installation:

```bash
python -B <exact_published_runner_copy> <publication_commit> \
  --runner-sha256 80621605d26f106af1343caee1679e4b1db5e5f36c4264722032add9a383be73 \
  --selection-sha256 3e9c62ca4dec8f88a15aaead1c80448de245d969a48bd82ee7c4748114ba9ba4
```

The P2 proof root is `/workspace/p2-saving16-20261125`, and its required pre-execution HEAD is the fixed round-7 source publication above. The runner performs its own detached checkout after verifying the preserved prior context. Its new output is `.lake/p25-followup-repairs-attempt008`.

`SOURCE_SELECTION.json` and `RUN_CONFIG.json` are the final prepared files. Files with `DRAFT` in their names retain the earlier nonexecutable preparation state and are not execution inputs. They document that no terminal receipt, final reuse counts or intermediate Ownership postimage was accepted in advance.

The parent owns all GitHub publication and cloud execution. Full-module round-8 normal/kernel/owned acceptance and P2.5 completion remain pending.
