# Isolated Cell05 ShapeArrays execution contract

## Current deliverable

This directory contains an executable, reviewable Python framework for exactly
`ImbalancedChen.P2OriginalSaving19Geometry05ScalableShapeArrays`. It has a new
`cell05_shape_repair_*_v1` receipt namespace, one owner, and three modes in order:
normal compilation, stock `leanchecker --verbose`, and the original complete
owned-declaration audit. It does not contain a repaired Lean source, a frozen
repair verifier, or a deployable source archive. Those inputs remain pending the
actual failed normal diagnostic and a reviewed source repair.

No part of this framework reexecutes the original thirteen accepted owners or
the 88 accepted suppliers. The old fourteen-target stage remains unchanged,
including its unsuccessful ShapeArrays candidate and failure evidence.

## Fixed supplier and runtime boundary

`BOUNDARY.json` records the original fourteen-target package/verifier pins,
the original ShapeArrays source/audit, and its exact four direct imports and
42 transitive project suppliers. All 42 belong to the original 88-provider;
none belongs to the newly accepted thirteen-owner prefix.

`origin_join.validate_origin()` reads the original frozen stage at
`/workspace/p26-cell05-connections14-stage-557a12f3bcd7`. It verifies the pinned
package, verifier, workflow and original source bytes, then calls the unchanged
fields-only join validator. The original 219 fields73 receipt checks and
baseline checks are read-only; they execute no Lean.

The supplier project and object roots remain:

- `/workspace/p26-cell05-connections14-provider-557a12f3bcd7/project`
- `/workspace/p26-cell05-connections14-provider-557a12f3bcd7/objects`

The guard must be the existing 16889262-byte file at that provider's
`evidence/RUNTIME_GUARD.json`, SHA-256
`19d5266e4e36891aa5cf07c0e95dffac30baadae2394b19aaa83dd84ac5d1081`.
The new framework has no guard-creation path. It checks that exact identity and
its stat inventory before and after each new proof command. A copied or newly
captured guard cannot replace it. Runtime binaries, package roots, and the
tracked environment come from the original accepted fields context; only the
project component of `LEAN_PATH` is relocated to the new stage.

The stage and source package must be disjoint from the original fourteen-target
stage, the original fields73 stage, and the entire provider root. All 88 old
source/object pairs are installed by exact-byte hardlink. The new owned audit
must report exactly 43 project modules: the fixed 42 old suppliers plus the
ShapeArrays target.

## Inputs required after source repair

The future source package must place exactly one new source at
`sources/ImbalancedChen/P2OriginalSaving19Geometry05ScalableShapeArrays.lean`.
The tools and original audit belong under
`tools/p26/cell05-shape-repair-20261126/`. The audit must retain its original
2732-byte identity, SHA-256
`4c255cf00501fb45b0d8d6f1e490304eb3ae356db5c2fe0aa695799fab3f123d`.

The following controls must be authored locally and pinned before deployment:

1. `SHAPE_SOURCE_MANIFEST.json`: schema `cell05_shape_repair_source_v1`, exact
   `module`, `original_source` equal to the original candidate pin in
   `BOUNDARY.json`, and the reviewed replacement `source` byte count and SHA-256.
2. `SHAPE_REPAIR_VERIFIER.json`: schema
   `cell05_shape_repair_frozen_verifier_v1`, `target_count: 1`,
   `expected_steps: 3`, `repair_source_ready: true`, exactly one `targets`
   record, and the exact `workflow_files` inventory. The target record retains
   the original module/import/dependency/audit fields and supplies the actual
   replacement source pin. Required execution and origin helpers are enforced
   by `load_configuration()`.
3. Root `PACKAGE_CONTENTS.json`: schema
   `cell05_shape_repair_source_package_v1`, counts 1/3, `accepted_steps: 0`,
   `repair_source_ready: true`, and an exact regular-file member inventory.
   It contains no `.olean` files and only the one fixed target source.

The package builder must not run on the cloud host. Missing or unresolved
controls fail before a proof command. New source/audit bytes are never generated
by this framework.

## Entry points

After a reviewed source package exists, its `stage_entry.py` accepts:

```text
--stage ABSOLUTE_NEW_STAGE
--attempt UNIQUE_ATTEMPT
--rss-gib 6
--wall-seconds 900
[--preflight-only]
[--max-new-steps 0|1|2|3]
```

There is no provider override: the original provider and guard are fixed by
the reviewed boundary. The entrypoint installs only exact package bytes and
executes the staged `verify_shape.py`. Preflight validates and installs inputs
without running Lean or producing accepted proof receipts. A budget of one or
two pauses after that many newly accepted modes with `STOPPED.json`; a later
attempt reuses those original seals unchanged.

Successful normal/kernel/owned evidence has immutable command, result, log and
accepted-seal links. Missing accepted objects, broken success links, a surviving
index naming lost evidence, and command/log remnants without a result all block
replay. Failed results and logs remain in their original attempt. A changed
source, audit, environment, runtime or input context cannot reuse an old seal.
Exactly three validated stages produce the new one-owner `SUCCESS.json`.

`export_shape.py --stage ABSOLUTE_NEW_STAGE --attempt COMPLETED_ATTEMPT --label v1`
rechecks the original supplier join, the same runtime guard, the new receipt
chain and the resulting archive. It selects exactly one new object body and no
old supplier or thirteen-owner objects. Its manifest retains the original join,
guard and stage references; the original evidence stays available at those
unchanged paths. It makes no whole-geometry or P2.6 completion claim.

## Local validation

`python3 -B test_shape_isolation.py -v` runs nine new synthetic tests of the
changed one-owner boundary, 43-module ownership closure, count restrictions,
normal-prefix reuse, missing-success and orphan-result barriers, exact guard
identity, original-stage/provider isolation, and one-object export selection.
All fixtures are non-executable synthetic data in temporary directories under
this directory, removed afterwards. The tests do not run any old test suite,
validate any synthetic fixture as a real proof, or execute Lean.
