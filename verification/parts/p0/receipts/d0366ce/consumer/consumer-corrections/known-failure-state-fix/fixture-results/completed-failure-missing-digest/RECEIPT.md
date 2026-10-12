# Part 0 exact core evidence receipt

Status: **FAILED_CI_WITH_INCOMPLETE_EVIDENCE**

Expected source: CONSUMER_FIXTURE_NOT_A_GIT_SHA

Expected tree: CONSUMER_FIXTURE_NOT_A_GIT_TREE

Actual requested run/job: -382 / -114 (attempt 1).

This is an offline evidence consumer. It does not execute Lean, a kernel checker, or Actions.

CI metadata status: KNOWN_FAILURE_FROM_SUPPLIED_METADATA. Evidence status: INCOMPLETE.

## Known CI metadata failure

The following source/run/job-bound supplied metadata was already non-successful. Missing evidence does not replace these observations with a pending CI result.

| Scope | Identity | Status | Conclusion |
|---|---|---|---|
| run | -382 | completed | failure |
| job | -114 | completed | failure |
| required_step | build | completed | failure |
| required_step | round4-targets | completed | skipped |
| required_step | leanchecker | completed | skipped |
| required_step | axiom-audit | completed | skipped |
| required_step | round3-types | completed | skipped |
| required_step | round4-types | completed | skipped |

These metadata conclusions are not Lean error diagnostics. Available actual raw Lean diagnostics are recorded separately.

## Pending evidence

GitHub artifact SHA-256 metadata is missing

No verified 1005-type payload or successful integrated module ledger has been produced.

## Missing or incomplete evidence

- Required input is not supplied: repo
- Required input is not supplied: artifact_zip
- GitHub artifact SHA-256 metadata is missing

## Unclosed theorem inputs

The existing final bridge remains conditional on hLower and hUpper. The analytic K and c suppliers are still required. Successful component integration does not discharge these hypotheses.

## Provenance and limits

- This consumer is not a local Lean compilation or kernel replay.
- Production object hashes are captured before/after by the actual CI type exporters; the archive need not contain every production object.
- The bundled root checker prints replay markers, not per-marker object digests. The production object bindings here were captured by the subsequent Round3/4 exporters; this consumer does not invent hashes at the earlier replay timestamp.
- The inherited 393 type strings retain prior compiler provenance. The current root replay validates their unchanged source closure, not a fresh type print for those 393.
- The eight upstream S1LowerRosser declarations are excluded from the 23 modules and 1005 types.

Relative references inside the inherited ledger retain their published fixed-source scope. Resolve them using CONSUMER_FIXTURE_NOT_A_GIT_SHA:verification/parts/p0/round4/ledger/REF_RESOLUTION.md; this output does not claim to duplicate every historical payload.
