# Recovery v1: exact validation obligations

## Trust boundary and meaning

The reviewed `WORKFLOW_MANIFEST.json` and every file it lists must be pinned by
the deployer/consumer before starting this protocol. `ANCHORS.json` fixes the
original remaining9 verifier, source package, pilot and continuation indexes,
the original full P2 runtime snapshot and historical guard. That verifier's
authenticated `BOUNDARY.json` fixes the prefix13 and ShapeArrays repair verifiers,
raw-chain anchors, accepted source/object contracts and original guard reference.
The recovered ShapeArrays package manifest is an additional explicit anchor;
its entire member set must equal the already anchored source/workflow/verifier
contracts. It does not replace any original source identity.

The original configuration validators' required-helper/file-set obligations are
fixed by each exact original verifier SHA, not inferred from a target count or a
status string. Every member of those anchored workflow lists is authenticated
before imports; the source loader cannot import a helper omitted from the list.

`capture` proves full current selected-content equality using the unchanged
original `runtime_evidence` and `capture_runtime_guard` functions. The guard
function hashes all selected files under all ten snapshot roots, checks exact
selected names and link targets, and checks every captured lstat after hashing.
The new `CURRENT_RUNTIME_GUARD.json` has the exact format returned by that
function. It is located in the new recovery stage and is never substituted into
an original context or document. Its authority is the explicitly versioned new
certificate and independently pinned recovery implementation.

The original guard's SHA and body remain unchanged. Its actual lstat failure is
recorded during capture, and it is required to remain a failure during cached
verification. This protocol makes no claim about a historically recorded loaded
runtime inventory. It establishes current bytes equal to the preserved snapshot.

## Obligation mapping

Paths in the **original function** column are relative to the corresponding
original `tools/p26/cell05-*-20261126` directory. The three historical families
are `connections14-run`, `shape-repair`, and `remaining9-run`.

| Original function / obligation | Recovery v1 implementation | Evidence retained / scope |
| --- | --- | --- |
| `verify_*.load_configuration`: immutable workflow manifest and every listed file | `protocol_core.authenticate_family`, then `PinnedSourceFinder` / `PinnedSourceLoader` | Anchored original verifier bytes, all workflow file pins, execution directly from authenticated `.py` bytes; no pyc selection or unpinned local sub-import |
| Original import isolation | A fresh `python -I -S -B recovery_worker.py KIND` per family; `prepare`; `finder.check_loaded` | Each family uses its own original `receipt_checks`, runtime, portable evidence, join, and audit parser. Prefix checker is the explicitly pinned remaining9 copy. No function or module monkeypatch |
| `stage_entry.install_package`: package manifest scope, safe members, source-only contents and exact installed bytes | `package_check` | Original fixed schema/counts; all members pinned and checked against exact target/workflow/verifier member set; no old installation or copy function called |
| `verify_connections14.load_configuration` | `configuration('prefix13')` + original `fields_only_join.fields_inputs` | 14 targets, 88 protected suppliers, source manifests/audits, topological imports and transitive closures, exact selected old union83 |
| `verify_shape.load_configuration` | `configuration('shape1')`; original `receipt_checks.require_single_scope` | One accepted ShapeArrays repair, unchanged original audit, fixed accepted repair source provenance, original42 dependency boundary and88 retained suppliers |
| `verify_remaining9.load_configuration` | `configuration('remaining8')`; original `scope_contract.validate_scope`; original `join117.load_boundary` | All9 original target contracts, all117 supplier contracts, exact15/73/15/13/1 groups, source/import closure and original boundary scope |
| `fields_only_join.fields_inputs` | Called unchanged in `fields_join` | Original fields73 portable219 checks; original baseline15 evidence; old88 source/object registry; original runtime evidence; target graph |
| `fields_only_join.validate_join`: all obligations except obsolete physical guard continuity | `fields_join`: exact expected join dictionary + original `check_provider`, `field_path_map` | Exact stage/provider paths, plan/registry/selection/archive/baseline identities, fields219 and owned2875, original guard/snapshot relationship, actual path-map bytes, all zero-proof flags and exact legacy frozen evidence list |
| `origin_join.validate_origin` | Shape branch of `recovery_worker.main`, `configuration`, `bind_context` | Original14 package/verifier/workflow and both copies of all14 sources, original failed target/audit, unchanged old provider and guard, original fields stage, isolated repaired stage |
| `origin_join.require_separate_stage` | Called unchanged | Repair stage disjoint from original14 stage, provider, old fields stage and supplier roots |
| `supplier_join.joined_inputs` | Called unchanged in `join_remaining` | Original103 source/object and registry binding, fields73/219 and rows15/45 portable raw chains, baseline15, exact capsule and runtime linkage |
| `join117.check_received` | Called unchanged | Original receiver controls, 75 chunk pins/layout, capsule inventory267, mapping496, original anchors and immutable receipt semantics |
| `join117.readonly_probe` logical obligations | Independent authenticated `prefix13` / `shape1` workers, `probe_result`, explicit new schema check in `join_remaining` | Exact original context/target/source/object/records,39 and3 raw accepted checks; no claim that the old probe's live guard passed |
| `join117.origins` | `join_remaining`; original `scope_contract.validate_origin_groups` / `validate_origin_paths` | Prefix/repair/fields context agreement; exact original groups; unchanged guard's snapshot relation; same legacy frozen evidence pins |
| `join117.validate_join` | Original `load_boundary`, `validate_locations`, `selected_entries`, `documents`, `preflight_documents(..., True)`, `install_provider(..., completed=True)` in `join_remaining` | Exact existing117 provider source/object pairs; exact original path maps and provenance documents; exact original `SUPPLIER_JOIN.json` equality; completed=True prevents creation; worker audit hook also prohibits any write |
| `join117.report` | Called only as a pure constructor; its in-memory status replaced with `RECOVERY_REBUILT_ORIGINAL117_RELATIONSHIPS` | Exact legacy frozen input list and original context data for comparison. No original file/status/schema modified; no public claim of old live-validation success |
| `verify_*.bind_context_to_package`: complete package/context inventory binding | `bind_context`; original `frozen_expected_paths` | Exact original context schema/stage/targets/suppliers and exact original frozen input list (not a shortened list); every frozen file hashed |
| `bind_context_to_package`: runtime and environment | `bind_context` / `current_runtime` | Identical original fields runtime; only original intended object-root relocation in LEAN_PATH; exact cwd/object path; thread1; LEAN_SYSROOT; Mathlib/package root list including conditional Cli; actual binary pins and current readonly Git commit |
| `receipt_checks.check_context_inputs`: namespace/path and scope | `bind_context`, original namespace functions, `namespace_snapshot` | Canonical non-symlink paths; provider/stage separation; no ImbalancedChen fallback in stock roots; frozen join/guard references; no cloud source generation/old proof commands; actual source/object namespace inventory |
| Original `check_runtime_guard` live continuity | **Not passed, bypassed, overwritten or monkeypatched.** `runtime_capture` explicitly records its failure, calls the original new-capture utility, and `current_runtime` validates the separate witness | Old guard remains a frozen input with original SHA and original path. New certificate explicitly distinguishes old failed lstat from new byte equality |
| `runtime_compat.runtime_evidence` | Called unchanged in runtime capture and existing portable joins | Original successful P1/P2 probe metadata, equal ten logical roots, full snapshot sorted inventory/count/bytes/digests, exact original fields RUN/runtime relationship |
| `runtime_compat.capture_runtime_guard` | Called unchanged exactly once per attempted full capture | Hash every selected current byte, reject selected missing/extra names, compare original byte lengths/SHA/link targets, record new lstat in new output only |
| `receipt_checks.validate_step(..., check_inputs=False)` | Called unchanged through original `prior`, `reject_missing_successful_objects`, or directly for repaired ShapeArrays, after `configuration`/`bind_context`/new guard validation | Exact original RUN→command→result→accepted chain; mode/module/argv/cwd/env; source/audit/dependency/object pins; log; stock kernel identity; full owned declarations, types, permitted axioms and actual project import closure |
| Original full-context check disabled in the step primitive | Replaced only by the explicit, complete new context/physical-witness obligations above | This is an intentional new protocol. No assertion of old `V.load_configuration`, old `V.bind_context_to_package`, or old `validate_success` passing the invalid old guard |
| `prefix_validator.check_indexes` / `check_failed_normal` | Called unchanged for prefix13; generic equivalent with same exact primitive semantics for remaining8 | Original first13/39 and first8/24 only. Original pilot3 reused, continuation36+1failure or21+1failure, no acceptance on the failed owner, all failure artifacts remain |
| `receipt_checks.require_accepted_prefix`, `prior`, `reject_missing_successful_objects` | Called unchanged | No gaps, duplicate acceptances, hidden missing seals/results or lost accepted objects; no replay permission |
| Complete raw artifact coverage | `exact_verification_files` | Actual verification namespace equals the accepted step evidence plus the two exact failed chains and attempt RUN/index/reuse documents; reject extra unindexed failed commands as well as omissions. Exact supplier/new-source installation rows and zero-proof reuse scope are checked |
| ShapeArrays original `validate_success` index obligations | `shape_success` + unchanged per-step validation | Exact anchored original SUCCESS/RUN/context/three records;3 newly executed,0 reused; same object; frozen-input/one-owner scope flags; owned28; original13 not rerun |
| Full owned inventory totals | Original step parsers + fixed totals | Prefix112, ShapeArrays28, remaining8 116. Counts do not replace the full declaration/type/axiom/import checks |
| New cached certificate authority | `recovery.verify(expected)` requires externally frozen certificate path/bytes/SHA | Immutable certificate pins new guard, historical report, protocol manifest/files, original snapshot/guard, original runtime and exact counts. A mutable document cannot authorize itself |
| Cached current input binding | `validate_history`, `core.refs`, verify worker `current_runtime` + namespace checks, then final pin checks | Rehash every frozen historical evidence/source/object/helper, all protocol files and actual interpreter; check current guard and actual Lean/leanchecker/Mathlib commit; preserve exact namespace inventory. No proof command replay or new guard capture |
| Consumer exact boundary | `validate_history` + returned `original`, `target`, `dependencies`, `prefix8` | Original9-target context remains unchanged. Exactly125 suppliers (117+8), target closure126 including Shape, exact original source/object paths for the new isolated consumer |
| Writes/processes | `action_audit`, worker `deny_worker_mutation`, `write_new(..., 'xb')` | Parent may launch only fixed isolated Python worker commands; workers cannot launch processes/write files. Capture writes only3 fixed outputs exclusively; verify is read-only. No Git, cloud, Lean or leanchecker command |

## Files written and consumer contract

The fixed recovery stage is
`/workspace/p26-cell05-runtime-recovery-20261127-v1`.
The reviewed tools live under `tools/p26/cell05-runtime-recovery-20261127`.
Capture exclusively creates, in order, `CURRENT_RUNTIME_GUARD.json`,
`HISTORICAL_VALIDATION.json`, then `CERTIFICATE.json`. Existing or partial outputs
cause a stop; they are never refreshed or removed. A certificate is published
only after the complete raw evidence verification and fresh input/guard recheck.
The final invocation checks it again using the same read-only consumer path.

`INTERFACE.json` is the definitive invocation and JSON field contract. The first
successful capture returns full certificate/history/guard pins; the new Shape
context freezes those actual values. Every later verification must pass the
frozen certificate length and SHA256, and the consumer must also compare its
frozen history and guard pins with the returned values. An environment change
invalidates the new guard and causes a stop. It does not authorize a refresh.

## Local verification and remaining live gate

`test_recovery.py` covers exclusive outputs and externally pinned certificate
bytes/path; changed/missing original context bytes; namespace insertion and
symlinks; stale pyc and unpinned child imports; every declared workflow file;
actual remaining8 partial-index counters, reuse provenance and gaps; actual
original capture-function checks over ten temporary roots (content change,
missing file, extra hash sidecar, post-capture stat change); worker write/process
denial. The original capture function body is compiled unchanged into an
isolated test namespace with a test evidence provider. No imported original
module is patched and no live proof or cloud command is run by these tests.
The parent audit's positive process path is also exercised with a harmless
isolated worker and real stdin/stdout/stderr pipes: anonymous FIFO descriptors
are allowed, while general file descriptors and unauthorized worker arguments
are rejected. The exact recovered remaining9 source package is checked against
the complete frozen workflow/source member set, including a missing-member case.

Local tests are not evidence that live P2 recovery succeeded. The final live
gate remains root's reviewed deployment followed by a full capture after the
24,923 exact missing runtime files are recovered. All three historical stages,
their accepted source/object files, raw receipts, old provider, receiver capsule
and metadata must remain present at their original cloud paths. Failures remain
failures; none of these tools produce an original nine-owner SUCCESS or set
`P2_6_complete=true`.
