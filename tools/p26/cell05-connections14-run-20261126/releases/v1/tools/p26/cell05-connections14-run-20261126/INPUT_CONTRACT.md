# Cell05 ready fourteen: exact execution contract

This source-only package runs the 13 existing header/field owners and existing
`ShapeArrays` owner selected by `CONNECTION_TARGETS.json`, in its exact order.
It has 42 planned new steps: normal compilation, stock `leanchecker --verbose`,
and the original full declaration-ownership audit for each owner. No source or
audit is generated or changed. The nine downstream owners that require P1 row
objects are excluded. This does not claim whole decoded geometry or P2.6 completion.

## Existing accepted evidence

`fields_only_join.py` reuses the existing original-evidence readers and validators.
It verifies all 219 original fields73 receipt chains and the original 156-step
baseline control evidence, installs the exact 88 P2 source/object suppliers by
hardlink, and establishes the original runtime guard. The selected targets use
83 of these suppliers. Every same-name source/object pin must agree. No old
supplier compilation, kernel replay, or owned audit is executed.

The unchanged original fields archive, its required baseline files, and the
original P2 runtime snapshot must remain at their pinned P2 paths in
`SUPPLIER_PLAN.json` and the runtime evidence. The original stage remains intact.
The only P1 material used here is already-copied compact runtime comparison
metadata; no live P1 path or row capsule is required.

The runtime guard first hashes the selected P2 runtime files against the original
matching snapshot. Every new proof command checks the same guard's exact file
identity and recorded inode/size/time metadata before and after execution. A
resume validates that original guard and never recaptures it. A changed guard or
runtime is an error requiring investigation, not a reason to recompile accepted
work. The entire Lean command environment comes from the accepted P2 fields
context; only the project component of `LEAN_PATH` moves to this new stage.

## Deployment and first-owner pilot

Extract the frozen source archive to a new package directory. The archive has
stage-relative `sources/ImbalancedChen/...` and
`tools/p26/cell05-connections14-run-20261126/...` members, plus
`PACKAGE_CONTENTS.json`. The package, stage, provider, and original fields stage
must be disjoint. Package and stage should share a filesystem for hardlinks.

For the assigned P2 paths, run:

```sh
python3 -B /workspace/p26-continuation-557a12f3bcd7/cell05-connections14-package-v1/tools/p26/cell05-connections14-run-20261126/stage_entry.py \
  --stage /workspace/p26-cell05-connections14-stage-557a12f3bcd7 \
  --provider /workspace/p26-cell05-connections14-provider-557a12f3bcd7 \
  --attempt ready14-pilot-v1 --max-new-steps 3 --rss-gib 6 --wall-seconds 900
```

Use `--preflight-only` to perform the same package, supplier, runtime, and recovery
checks without any Lean command or attempt receipt. The preflight may hardlink
the frozen source/object files into their new stage. A previous join-only
installation at these exact paths is supported: existing bytes must match, and
its `SUPPLIER_JOIN.json` and provider guard are preserved.

The three-step budget accepts only the first owner, then writes `STOPPED.json`
with `reason: new_step_budget` and prints `PAUSED_ACCEPTED_PREFIX`. It does not
write `SUCCESS.json`. The first owner is
`ImbalancedChen.P2OriginalSaving19Geometry05ScalableActive8EnumerationHeader`.

## Resume and full export

Run the same entrypoint and limits with a new attempt name and omit the step
budget to finish the remaining steps. Existing accepted normal/kernel/owned
chains are validated and reused unchanged. Limits are part of the context, so
changing them cannot silently reuse a different context. All accepted steps
must form an ordered prefix. Missing successful receipts or objects, a surviving
index naming missing evidence, and an interrupted command/log without its result
are restoration barriers. No such state is treated as a cache miss. Source and
object conflicts fail before compilation. A process lock prevents simultaneous
executors in one stage.

Only a complete, validated 14-owner/42-step chain produces `SUCCESS.json`.
Then retain a verified archive on P2 with:

```sh
python3 -B /workspace/p26-cell05-connections14-stage-557a12f3bcd7/tools/p26/cell05-connections14-run-20261126/export_connections14.py \
  --stage /workspace/p26-cell05-connections14-stage-557a12f3bcd7 \
  --attempt ready14-complete-v1 --label v1
```

The export revalidates the original supplier join, the unchanged runtime guard,
the exact new receipts, and archive member bytes. It contains only the 14 new
object bodies, their supplied sources/audits, new verification history, frozen
workflow/compact metadata, and the join locator. It does not include the old
88 object bodies or the full original fields evidence archive/runtime snapshot.
Printed output is a compact archive fingerprint/report; transfer is separate.

## Local validation boundary

`test_connections14.py` uses clearly synthetic, non-executable fixtures. It tests
the modified recovery, runtime-guard, exact-scope, and archive paths. These tests
are not Lean proof evidence. The source release records zero accepted new steps;
only actual P2 result and acceptance chains can change that count.
