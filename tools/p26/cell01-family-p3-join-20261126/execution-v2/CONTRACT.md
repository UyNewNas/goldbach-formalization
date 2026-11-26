# Cell01 eleven new owners: fixed P3 execution

This dispatcher uses the unchanged frozen `p3-v2/family_run.py` deployed in the independently reviewed 59-member preparation v3 package. It exposes no target-selection, supplier-compilation, alternate-runtime or retry option.

## Inputs before any Lean command

The live preparation package must still equal its exact manifest (11935 bytes, SHA256 `2e5595cbea2c0de2df6724535bdb32b3557b46a50de012206669cd9c468c0f95`), including all 58 payload members and no extras. The configuration must equal its reviewed 3325-byte pin `60d612998b468f878904dfa557e0059af9f7d76102830296040cd99045c39388`.

The actual `/workspace/p26-cell01-family-p3-inputs-557a12f3bcd7/PREFLIGHT.json` must report `PASS_ALL_ELEVEN_EXISTING_SUPPLIER_JOINS_NO_PROOFS`: 791 old suppliers, eleven exact owner checks, zero compiler calls or proof credit, and no row001 body export. The per-owner old/complete closure counts must equal 625/626 for the interface, 663/665 for Block000_015, 642/644 for each of the other eight blocks, and 791/802 for the final endpoint.

The runtime and all eleven join files must match the actual preflight file references at their exact expected paths. The runtime must contain 11517 distinct external modules, use the complete-tree mode and the complete 515-module external root, and bind the exact original generic module context (12878196 bytes, SHA256 `b36a9153969abb3cbac96c3d74bea3e0c366ca3a673cdfe7456a7e655f2241c0`). All eleven joins are checked for owner order, distinct supplier counts, a combined union of 791 old modules, and the same external inventory. No imported prior pilot is accepted through this dispatcher.

The fixed proof stage is `/workspace/p26-cell01-family-p3-stage-557a12f3bcd7` and must not exist when the dispatcher starts. The fixed new dispatcher control directory is `/workspace/p26-continuation-557a12f3bcd7/cell01-family-p3-execution-v2`. Existing stage or RUN metadata stops for inspection. The dispatcher never removes or overwrites a stage, acceptance record, object, receipt or failure record.

## Two invocations of the original runner

Both invocations use the exact original source archive and source root, the same generated runtime, the fixed stage, `--rss-gib 12`, and `--wall-seconds 1800`.

1. Attempt `family11-interface-pilot-v2` receives the interface join and `--max-new-steps 3`. The original runner must return exactly one accepted owner and three accepted normal/kernel/owned steps, all newly executed, with status `PAUSED_ACCEPTED_PREFIX`.
2. Attempt `family11-complete-v2` receives all eleven fixed joins and `--max-new-steps 30`. It must return exactly eleven owners and 33 accepted steps. The first three records must retain the exact original pilot receipt references and be marked reused; the other 30 must be new. The frozen runner performs its normal accepted-history validation and refuses to overwrite/recompile missing or contradictory success evidence.

The dispatcher records each exact argv before starting the child. Any failed process or inconsistent result stops the sequence and preserves the original stage and all surviving accepted prefixes. An interrupted dispatch is not automatically resubmitted: its existing stage/control markers require inspection. Any later continuation must use the original frozen runner with the existing same-byte inputs and its preserved acceptance history; this dispatcher does not implement an alternative recovery mechanism.

## Final acceptance and export

The original runner owns all 33 normal, stock leanchecker kernel, and full-owned checks, plus final archive creation and full member readback. The dispatcher checks each resulting new-owner acceptance anchor and object, checks the exact original pilot receipt reuse, and verifies the final archive pin and new-owner manifest scope. It publishes a compact SUCCESS only after all of those checks pass.

The evidence archive stays on P3. Its frozen exporter includes only new-owner evidence and objects plus old-supplier locator metadata. The dispatcher reads no old row001 receipt/log body directly and never transfers that historical group. Both the original runner result and the dispatcher retain `P2_6_complete_claimed: false`; the scope is eleven new Cell01 original-floor owners only.

Four new synthetic gate tests passed: partial preflight, incorrect owner closure, recomputed pilot flags, and a full-success label with only three records are rejected. No old test suite, old supplier proof or Lean command was run during this local preparation.

Deployment remains subject to the actual all-eleven preflight PASS and root review of the saved dispatcher command. A P3 execution task can use the service ceiling of 13107 MiB, a 3600-second task limit and one CPU; the Lean runner itself is fixed to 12 GiB per step. Any task interruption leaves its original accepted prefix for inspection and reuse.

This frozen execution v2 changes only the active package path, exact v3 manifest/config pins, fresh control path and attempt identifiers from the nondeployed execution v1. Every function has the same AST as the version whose four new gate tests passed. No old test suite or proof was rerun to prepare these changed constants.
