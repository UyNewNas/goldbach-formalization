# Batch13: five source repairs

The five proof-body repairs are published at `c257b7ade3b82d8f3ae126ffb1ca999871e9cd57`. Its `SOURCE_REPAIRS.json` SHA-256 is `47942ef101dce5533ec8926649109c2e23b1b1616aa03e95b0c69928f27f7e0c`. The manifest and individual repair notes record the actual Batch12 diagnostics and source preimages. Source review and the local checks below are **not Lean compilation or acceptance evidence**.

| Group | Owners |
| --- | --- |
| `symbolic` | `P4AOriginalFull87PrefixBinding`, `P4AOriginalFull87HistoryCore`, `Part3ActualWResidualCompletion`, `P1OriginalFifthMovingHarmonicEnvelope` |
| `literal-pilot` | `P4AOriginalFull87AscendingAllInteriors` |

All module names have the `ImbalancedChen.` prefix. The groups have independent target closures. They use the existing lane-0 serializer sequentially and keep separate receipts. This caller adds no resource settings and changes no guard, serializer, checker, audit template, or historical driver.

## Commands

Run the published caller with the exact source commit; its own publication may be a later commit. Git fetching and caller extraction are performed separately by the coordinator. The caller only reads Git objects and never checks out, resets, or changes the dirty source repository.

```sh
python3 -B run_repairs.py --source-commit c257b7ade3b82d8f3ae126ffb1ca999871e9cd57 --group symbolic --check
python3 -B run_repairs.py --source-commit c257b7ade3b82d8f3ae126ffb1ca999871e9cd57 --group symbolic --run

python3 -B run_repairs.py --source-commit c257b7ade3b82d8f3ae126ffb1ca999871e9cd57 --group literal-pilot --check
python3 -B run_repairs.py --source-commit c257b7ade3b82d8f3ae126ffb1ca999871e9cd57 --group literal-pilot --run --normal-only
python3 -B run_repairs.py --source-commit c257b7ade3b82d8f3ae126ffb1ca999871e9cd57 --group literal-pilot --run
```

`--check` permits `--source-repo` and `--project` overrides. It reads the exact five-row manifest and published payloads, checks the selected group's source preimages, dependency sources/imports, independence and four protected roots. It creates no receipts or backups and invokes no Lean, Lake, guard, or serializer. It does not establish object readiness. Actual execution is restricted to `/workspace/goldbach-formalization` and `/workspace/blue-member-build`.

`--run` checks the complete selected group before any source write, backs up changed preimages with the unchanged Batch5 helper, and preserves exact already-after sources without rewriting them. Each normal attempt requires stock `lake --no-build` direct-dependency readiness and runs only its selected target. Full logs, the actual single `Built` entry, source plus five outputs, configuration, dependency objects/traces, and runtime fingerprints bind every durable normal success. Independent remaining owners can proceed after a failure; each successful receipt is preserved.

The final command above reuses valid literal normal success before requesting kernel/full-owned acceptance. `--normal-only` exit zero means only that every selected normal succeeded; its result explicitly leaves acceptance false. A ready target without a valid own normal receipt is held. A prior receipt with changed source, dependency, configuration, runtime, output, command or log evidence is held; successful normals are never silently repeated.

## Receipts and audit boundary

Receipts live under:

```text
/workspace/p1-complete-proof/20261125-batch13-repairs-v1/<full-source-commit>/<group>/
```

`BINDING.json` freezes the caller, explicit source commit, manifest, helper pins, group and runtime. `normal/<module>/NORMAL_PASS.json` records each actual normal success. `runs/attempt-NNNNN/` retains source backups/install records, complete command logs, Git state before/after and `RESULT.json`. A later invocation must match the same frozen driver and inputs.

The caller prepares the exact `e9dadb4e…` runner plan from actual successful normal logs, then invokes only populated `--lane 0` under the already-held serializer. Completed audits are reused only after current normal-context, source/output, plan, runtime, command/log, exact owned-inventory/count and standard-axiom checks. `audits/<key>/lane-0/VALIDATION_RESULTS.json` is the completed acceptance evidence. An existing partial audit holds further audit execution for inspection; the caller does not replay an unknown partial lane. Failed owners remain unaccepted even if the other owners pass.

Every context, normal receipt and e9 plan uses the explicit `--source-commit`. The `220c1463…` constant identifies only unchanged tooling and the manifest's failed-source preimages. No historical `COMMIT` global is modified and no old receipt is relabeled. The new `context`, `normal_valid`, and `audit_valid` functions take the source commit explicitly. The pinned helpers supply their existing graph, install, logging, snapshot, frozen-write and runtime utilities.

These receipts cover only the selected four-owner group or single literal owner. Every result retains `whole_P1_complete: false`.

## Local verification

The temporary focused checks were written first: the initial run failed because the new caller did not yet exist. After implementation, eight cases passed: exact manifest/commit scope; missing, duplicate, extra/wrong-group rows; unknown preimage and dangling source zero-write holds; payload integrity and exact-after no-op; exact normal commit/context binding; orphan ready-object hold; partial-audit hold; and dangling normal-receipt hold. A further positive resume check confirmed that a valid prior normal is returned after stock readiness without a normal build or receipt rewrite. These use temporary synthetic evidence and are not cloud or Lean evidence.

Read-only checks against the published source commit passed locally for both groups: four owners with 304 project sources, and one owner with 216 project sources. Local checks validate caller behavior and source bindings; actual normal, kernel and full-owned results must come from the selected cloud runtime.

Independent peer review and coordinator review found no material blocker. The final caller SHA-256 is `95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea`; it differs from the reviewed `9bd7b76c…` only by correcting the opening docstring to say two groups, both using lane 0. Python syntax and whitespace checks passed. Historical helper/driver files and all Lean sources were untouched by this caller implementation.
