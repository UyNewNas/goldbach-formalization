# Cell01 interface pilot input adapter

`prepare_pilot.py` assembles the existing frozen executor's input schema. Its only
execution path calls `family_run.py --validate-only --max-new-steps 0`. It neither
invokes Lean nor reproduces a proof validator.

The source package determines the exact 626-module interface closure: the new target,
624 source-matched canonical suppliers, and the accepted original-floor transport.
No finite-row supplier or row001 completed receipt body is needed. Historical
references are registered at their original paths; no evidence body is copied or
rewritten. The four original canonical closure/addendum pins remain attached.

The runtime comes from the accepted `generic-v2-r14` context and its owned
`module-byte-context.json`, with all 11 accepted complete-tree signatures and
11,517 external module identities. The frozen runner verifies actual P1 files with
the existing `GenericFloor_verify_v2.tree_signature`, then validates and installs
the suppliers. An unchanged signature in metadata alone does not grant acceptance.

Use the deployed immutable executor at
`/workspace/p26-continuation-557a12f3bcd7/cell01-family-executor-pilot-v1/family_run.py`.
Supply the frozen extracted source package and its archive via `--source-root` and
`--source-archive`. Set `--output` to a fresh metadata directory and `--stage` to a
separate persistent family stage. All roots must be disjoint in both ancestor
directions. The adapter prints the exact output pins before running the preflight.

After `VALIDATED_INPUTS_NO_PROOF_COMMANDS`, the coordinator may run the same executor,
source package, runtime, join and **same stage** with a fresh attempt name and
`--max-new-steps 3`. Keep that stage, its accepted anchors, objects, logs, per-owner
input snapshot and context. Continue the full eleven-owner sequence there so the
accepted interface is reused. Do not create a new pilot stage and rerun an accepted
owner. All artifacts continue to report `P2_6_complete_claimed: false`.

The adapter pins the reviewed pilot-v1 code manifest and the actual accepted generic
context and three seals. It requires original row000 RUN/INPUT/RESULT pins supplied
by the fixed family `SUPPLIER_DELTA.json`. Every generated JSON is create-once or
read-back-identical. A failed preflight does not authorize changing accepted bytes;
resolve the concrete mismatch and preserve the failed attempt.
