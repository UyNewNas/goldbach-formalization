# Part 0 exact core evidence receipt

Status: **FAILED_EVIDENCE_CONSUMPTION**

Expected source: d0366ce64272e81faf6166a8a90050f56b328d38

Expected tree: e2ab22b96f76c8969386296558c626c62a581700

Actual requested run/job: 38289734671 / 114946653833 (attempt 1).

This is an offline evidence consumer. It does not execute Lean, a kernel checker, or Actions.

CI metadata status: COMPLETED_SUCCESS_METADATA_ONLY. Evidence status: INVALID_OR_CONSUMER_BLOCKED.

## First consumer failure

EvidenceFailure: Accepted production module is explicitly imported by the root: ImbalancedChen.Certificates.PairedCertificateChecker

Raw supplied evidence and any retained real Lean diagnostics remain distinguishable from this consumer failure.

## Actual required gates

| Gate | Outcome | Seconds | Exit |
|---|---|---:|---:|
| build | success | 2640 | 0 |
| round4-targets | success | 4 | 0 |
| leanchecker | success | 457 | 0 |
| axiom-audit | success | 29 | 0 |
| round3-types | success | 186 | 0 |
| round4-types | success | 187 | 0 |

## Unclosed theorem inputs

The existing final bridge remains conditional on hLower and hUpper. The analytic K and c suppliers are still required. Successful component integration does not discharge these hypotheses.

## Provenance and limits

- This consumer is not a local Lean compilation or kernel replay.
- Production object hashes are captured before/after by the actual CI type exporters; the archive need not contain every production object.
- The bundled root checker prints replay markers, not per-marker object digests. The production object bindings here were captured by the subsequent Round3/4 exporters; this consumer does not invent hashes at the earlier replay timestamp.
- The inherited 393 type strings retain prior compiler provenance. The current root replay validates their unchanged source closure, not a fresh type print for those 393.
- The eight upstream S1LowerRosser declarations are excluded from the 23 modules and 1005 types.

Relative references inside the inherited ledger retain their published fixed-source scope. Resolve them using d0366ce64272e81faf6166a8a90050f56b328d38:verification/parts/p0/round4/ledger/REF_RESOLUTION.md; this output does not claim to duplicate every historical payload.
