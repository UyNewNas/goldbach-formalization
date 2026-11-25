# Serial acceptance of the Batch10 normal successes

`audit_batches.py` freezes small plans for the **unchanged e9 independent-kernel/full-owned audit runner** and executes one populated lane per invocation. It invokes no normal compilation or source installation. The proof snapshot remains `99c1f8ba1dc453b21f47e30b667db0de93d73387`; the normal driver remains SHA256 `63e999403a1d39251642097c8a03e8b60983df785267fcca32f118b57aab2f71`.

The scope is at most **75 Batch10 owners, including all 53 Higher owners**, not whole-P1 acceptance. A smaller actual-success parent plan stays explicitly partial. Fixture tests and preparation do not establish Lean acceptance.

## Get the actual normal plan and freeze small subsets

Wait for the normal job to stop. Extract the published helper outside the dirty cloud Git checkout as `/workspace/p1-audit-batches.py`. The normal job already freezes its exact driver at `/workspace/p1-complete-proof/20261125-batch10-resume/executed-driver.py`.

The following command revalidates durable normal successes, obtains their exact pending plan, and creates a fresh audit directory. It does not run Lean or Lake. Use a new output path if this one already exists.

```bash
python3 -B - <<'PY'
import json, subprocess
normal = '/workspace/p1-complete-proof/20261125-batch10-resume/executed-driver.py'
result = subprocess.run(['python3', '-B', normal, '--audit-plan-only'],
                        text=True, capture_output=True, check=True)
print(result.stdout, end='')
pending = json.loads(result.stdout)
assert pending['status'] == 'AUDIT_PLAN_PENDING'
subprocess.run(['python3', '-B', '/workspace/p1-audit-batches.py', '--prepare',
    '--plan', pending['plan'],
    '--out', '/workspace/p1-complete-proof/20261125-batch10-audits-v1'], check=True)
PY
```

The original pending plan and its `PENDING_COMMANDS.json` remain intact. The helper copies the exact parent plan, freezes plans of at most eight owners, places four owners in lane 0 and at most four in lane 1, and records plan hashes in `MANIFEST.json`. Shared normal logs keep their complete actual `Built` sets. Each selected module entry and its dependency source bindings are retained unchanged.

Fresh preparation reads the Batch5 helper through `git show` of the pinned snapshot and checks the parent template/runtime metadata. It does not require live Lean or write the build project. `--source-repo` and `--driver` support explicit locations for preparation and local fixtures; actual execution requires the original cloud project and pinned runtime.

## Run one explicit lane

```bash
python3 -B /workspace/p1-audit-batches.py --summary \
  --out /workspace/p1-complete-proof/20261125-batch10-audits-v1

python3 -B /workspace/p1-audit-batches.py --run-next \
  --out /workspace/p1-complete-proof/20261125-batch10-audits-v1 \
  --lane-key chunk-000:0
```

The first invocation of a chunk calls e9 `--prepare-only` only when that chunk's receipt root is absent. Execution then calls the existing serializer and e9 with explicit `--lane 0` or `--lane 1`. The helper never invokes the default two-lane coordinator or an empty lane. Subsequent calls select the next exact `UNSTARTED` key from the summary, such as `chunk-000:1`, then `chunk-001:0`.

Use one lane per compiler task for the first pilot. The task may use the service's existing 3,600-second limit; the helper adds no fixed cancellation timer and changes no memory, thread, heartbeat, or recursion settings. Four owners is a scheduling boundary, not a claim about measured memory safety. Any later grouping of sequential lane calls should use observed completed-lane durations.

Before a lane runs, every selected owner passes the unchanged normal driver's full receipt/context validation. After it finishes, reuse requires the exact frozen plan, normal provenance and raw logs, named kernel command results, full-owned inventory and counts, allowed axioms, stock no-build evidence before and after, current source plus five outputs, dependency object/trace hashes, configuration, and runtime bindings. E9 stage lines remain live in compiler output; complete logs remain under the lane directory.

## Resume boundaries and partial lanes

A lane becomes reusable only after its complete `VALIDATION_RESULTS.json` passes validation. `--summary` reports `COMPLETE_VALIDATED`, `UNSTARTED`, or `PARTIAL_REQUIRES_INSPECTION`. Repeating `--run-next` never reruns a complete validated lane. An explicit completed `--lane-key` is rejected.

E9 writes evidence exclusively and cannot resume inside a partial lane. Preserve that directory and inspect the actual logs. Individual kernel passes in a partial lane remain evidence but do not count as full-owned acceptance. An implicit next selection stops if any partial lane exists; an explicit untouched key can continue independent work.

After inspecting a partial lane, a new attempt can exclude all validated complete owners while retaining links to the old complete receipts and recording the old partial directories:

```bash
python3 -B /workspace/p1-audit-batches.py --prepare \
  --plan /workspace/p1-complete-proof/20261125-batch10-audits-v1/PARENT_PLAN.json \
  --driver /workspace/p1-complete-proof/20261125-batch10-resume/executed-driver.py \
  --out /workspace/p1-complete-proof/20261125-batch10-audits-v2 \
  --reuse-root /workspace/p1-complete-proof/20261125-batch10-audits-v1 \
  --retry-partials
```

This is an explicit fresh kernel/audit attempt for owners without complete acceptance. It does not replay their normal builds. Without `--retry-partials`, preparation refuses an inspected reuse root containing partial lanes.

## Read and export the actual evidence

Each complete lane provides `VALIDATION_RESULTS.json`, `OWNED_EXPORTS.json`, the full-owned audit source, full raw logs, command records, and source/output snapshots. The helper's summary reports the parent normal count, accepted owner count, and the union of all 53 Higher owners separately. `whole_P1_complete` stays false even when all 75 selected owners pass.

Use the existing deterministic archive/export procedure in `docs/p1/20261124/batch9-normal-accepted-evidence/MCP_EXPORT_TASK.json`. For this run set its base to `/workspace/p1-complete-proof`, its input parents to the disjoint `20261125-batch10-resume` and `20261125-batch10-audits-v1` directories, and its export root to a fresh sibling directory. Include every later audit attempt root if one is used. Preserve the complete raw logs and JSON/Lean/Python evidence; the precedent excludes only bytecode and compiled object artifacts. Read the actual new summary and complete lane results, instead of its historical `RESULT.json` lookup, when populating the archive's compact result field.

Retrieve `ARCHIVE_SUMMARY` and losslessly paginated `ARCHIVE_BASE64` from the compiler output. Verify compressed archive SHA256, uncompressed tar SHA256, index SHA256, and every indexed file before treating the exported archive as the local receipt copy. These are transport/integrity checks, not additional acceptance runs.

## Existing next-frontier components

The pinned Batch5 helper already supplies `imports`, `project_graph`, `closure`, `guard`, and `serialize`; Batch6 `run` preserves full command logs and actual build diagnostics. Reuse them for subsequent readiness-gated targets. Historical Batch5–9 coordinators and the Batch8 audit-plan preparer hard-code old scopes/receipts and must not be rerun as a generic frontier command. The existing ordinary-frontier pool and positive-stratum next-steps files are planning inputs; current readiness requires fresh no-build evidence. The normal driver in this directory is intentionally bound to the 75 owners at snapshot `99c1f8ba`.
