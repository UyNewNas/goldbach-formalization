# Read-only export of the existing thirteen-owner prefix

`export_prefix13.py` is a local-authored, single-purpose wrapper for the failed
`ready14-complete-v1` attempt. It must be reviewed before any cloud execution.
No Lean command is executed. The original fourteen-target source, context,
runtime guard, receipts, failure evidence and objects remain unchanged.

The wrapper authenticates the original frozen verifier and every workflow file
before importing the original `receipt_checks`, `verify_connections14` and
`export_connections14` helpers from the original stage. It calls the existing
`load_configuration`, `bind_context_to_package`, `reject_missing_successful_objects`,
`prior`, `require_accepted_prefix` and their original complete step validators.
The original fourteen-target context is required unchanged. No modified
configuration or fabricated `SUCCESS.json` is used.

The exact accepted prefix must comprise the first thirteen owners, each with
normal, stock kernel and full owned/imports evidence. All three modes must bind
one unchanged object per owner. Pilot receipts are retained at their original
paths and reused in the continuation. The failed `ShapeArrays` normal command,
result and log must bind the original source, context and dependencies; it has
no accepted seal or object. All original failed-chain bytes are included in the
partial archive without promotion to acceptance.

## Count boundary

| Quantity | Required value |
|---|---:|
| Original context targets / intended steps | 14 / 42 |
| Accepted prefix owners / distinct accepted steps | 13 / 39 |
| Pilot new accepted steps | 3 |
| Continuation reused accepted steps | 3 |
| Continuation new accepted steps | 36 |
| Continuation failed normal commands | 1 |
| Original continuation `newly_executed_steps` | 37 |
| Accepted `ShapeArrays` steps | 0 |

The 37 raw executions include the failed normal command. They are not 37 new
acceptances. The six synthetic boundary tests check this distinction, original
14-target context retention, gap rejection, pilot identity, three-mode object
identity and exclusion of ShapeArrays acceptance. They do not constitute proof
evidence or replay any original test suite.

## Review and execution

Deploy the wrapper outside both the original stage and its output root, for
example under
`/workspace/p26-continuation-557a12f3bcd7/cell05-prefix13-export-v1`.
The fixed original stage is
`/workspace/p26-cell05-connections14-stage-557a12f3bcd7`.

After independent source review, the coordinator may invoke:

```sh
python3 -B /workspace/p26-continuation-557a12f3bcd7/cell05-prefix13-export-v1/export_prefix13.py
```

`--check-only` performs the same original-evidence validation without exporting.
Neither mode runs Lean. The existing `EXECUTION.lock` is opened read-only and
locked against an active executor. The exporter never installs suppliers,
rebuilds a guard, creates a verification attempt, or changes the source stage.

All new output goes to the independent fixed directory
`/workspace/p26-cell05-connections13-prefix-557a12f3bcd7`:

- `PARTIAL_INDEX.json`: a separate partial-result schema, the unchanged full
  original context, all 39 original seal identities, raw failure identities,
  precise acceptance/execution counts and original-path-to-member mapping.
- `connections14-prefix13-v1-evidence.tar.xz`: exactly thirteen new object
  bodies, all fourteen original source/audit inputs, the original frozen
  workflow and compact supplier metadata, original verification history with
  failure evidence, and this independently authored wrapper/index.
- `PARTIAL_EXPORT_REPORT.json`: produced only after all archive members have
  passed the original readback function, the original prefix has been validated
  again, and the source stage plus all frozen external inputs remain unchanged.

The unchanged original `write_verified_archive` and `recheck_archive` functions
perform archive construction and byte readback. Old 88 supplier object bodies,
the old full fields archive and runtime snapshot bodies are not exported.
No archive is automatically transferred. An existing output directory or a
partial output is preserved and causes refusal, never overwrite or silent
recovery. Require the final partial export report before accepting the artifact.

This export explicitly leaves the original 14-owner batch, full decoded
geometry and P2.6 incomplete. A repaired ShapeArrays source must be compiled in
a separately reviewed context, without changing this original failed stage or
replaying these thirteen successful owners.

## Frozen v1 execution boundary

The coordinator completed source-structure review before this v1 was pinned.
The actual original failure files have not yet been returned to the local
reviewer. This v1 therefore retains its strict expected failure contract:
`status == failed`, `exit_code == 1`, `termination_reason == null`, no object in
the result, and no current failed-owner object. These are requirements to be
checked against the real original stage, not claims that the local review has
already observed those fields. A mismatch fails inside `validate_prefix`
before the independent output directory or partial index is created.

It is permissible to queue this read-only evidence task after the original
failure-diagnostic task: it changes no source and cannot accept an unexpected
failure shape. If the actual failure has a different kind or retains an object,
preserve it and author a separately reviewed exporter version; do not edit this
v1, delete the object, or relax the original evidence. `CODE_MANIFEST.json`
pins this v1 and `LOCAL_VALIDATION.json` records only the six executed synthetic
boundary tests. Real prefix validation, archive creation and proof credit remain
pending until the cloud evidence task succeeds.
