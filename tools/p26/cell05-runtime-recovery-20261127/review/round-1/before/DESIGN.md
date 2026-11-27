# Explicit post-restoration recovery protocol v1

## Scope

This new protocol preserves every historical byte. It does not make the original
live lstat validators pass. It establishes a separate current-runtime witness
after complete byte equality with the original ten-root snapshot, and validates
the original 13/39, 1/3 and 8/24 receipt chains under that explicit witness.
It executes no Lean, leanchecker, Git, source generation or old proof command.

Output is exclusive to `/workspace/p26-cell05-runtime-recovery-20261127-v1`.
`capture` and `verify` are distinct commands. `verify` never creates or refreshes
any file. Historical paths, schemas, argv, counts and guard references stay exact.
The final consumer is the separate one-owner Shape execution stage, not a resumed
or manufactured nine-owner SUCCESS.

## Components

1. `recovery.py` authenticates its supplied source manifest, runs isolated source-
   authenticated workers, and exclusively writes a current guard, historical
   validation report and certificate. Cached verification rechecks every frozen
   input byte and every current guard entry before returning the consumer view.
2. `recovery_worker.py` authenticates all files in each anchored original workflow
   before importing any original helper. A source-only finder rejects unpinned
   helper imports and ignores pyc. Each family runs in a fresh `-I -S -B` Python.
3. `protocol_core.py` contains path/pin, immutable write, pinned loader and pure
   coverage checks. `ANCHORS.json` pins the recovered remaining9 package, its two
   original run indexes, the original guard and full snapshot. The authenticated
   remaining9 boundary pins the other two original workflow families.

## Coverage mapping

| Original obligation | Recovery coverage |
| --- | --- |
| Workflow manifest and all source pins | Authenticate anchored manifest, all workflow files, source-only importer; verify module origin; preserve imported source bytes |
| Target/supplier/source manifest and import DAG | Fixed family schema/counts, original selection/source contracts, graph closure, source/audit pins; original `validate_scope` for remaining9 and `require_single_scope` for ShapeArrays |
| Fields88 source/objects/evidence | Original `fields_inputs`, `check_provider`, `field_path_map`; rebuild every original join relationship and exact frozen evidence list |
| Original103 portable chains | Original `joined_inputs`, including fields73/219, rows15/45, baseline15 and exact receiver capsule |
| Prefix13 and ShapeArrays1 provenance | Original exact anchors, original step validators, original prefix indexes/failure; original successful ShapeArrays index semantics |
| Remaining117 join documents | Original `documents`, `selected_entries` and read-only comparison of all generated expected bytes; exact selected provider namespace/pins |
| Context runtime/environment/cwd/LEAN_PATH | Same relationships as original `bind_context_to_package` and `check_context_inputs`, no project fallback namespace; compare original frozen list using original `frozen_expected_paths` |
| Current runtime | Original `runtime_evidence` and `capture_runtime_guard`, complete ten-root inventory and content equality, actual binary pins and current Mathlib commit |
| Old guard | Original document pin remains fixed; current lstat failure is recorded honestly; never updated or substituted in old context |
| New stability witness | New guard exclusively written outside all old stages; certificate binds it to the original snapshot and protocol source |
| Raw accepted chains | Original `validate_step(..., check_inputs=False)` only after new complete context validation; original raw source/object/command/result/seal/log/owned/import closure semantics retained |
| Partial indexes/no replay | Exact pilot/continuation contexts, order, disposition and counts; reject missing accepted objects; two genuine failed chains retained; no original full SUCCESS invented |
| Cached consumer verification | Certificate/history/guard/protocol pins, every frozen input and supplier byte, current guard, exact 125 dependencies and 126 project closure |

The intentional semantic difference is explicit: current lstat continuity is
provided by a new witness after full content equality. All historical document
identities and proof-chain obligations remain unchanged. No monkeypatch or
replacement function is installed in any original module.

## Local checks

Use bounded tests for same-size byte tampering, missing/extra runtime inventory,
changed historical contexts/records, executable import substitution (including
pyc), certificate cross-binding and immutable outputs. Live capture remains a
separate required gate after all 24,923 missing files have been restored exactly.
