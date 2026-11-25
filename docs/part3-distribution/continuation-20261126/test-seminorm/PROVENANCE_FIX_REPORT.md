# P3.5 test seminorm donor provenance fix

`verification/verify_part3_continuation.py` now links the archived donor excerpts to the sources used for extraction. The verifier checks five M/R20 excerpts in the selected supplier extraction baseline and the S22 finite-constant excerpt in the actual consumer source. Each UTF-8 excerpt must be nonempty, match its recorded SHA-256, and occur at exactly one byte offset in its intended source. It rejects duplicate records and requires five distinct supplier excerpts and one consumer excerpt.

The verifier checks that the donor manifest, supplier extraction baseline, supplier candidate, and consumer are hash-bound artifacts. The selected supplier and donor candidate paths must identify their intended owned modules. The existing dependency closure and unified repair patch checks still run. The supplier excerpt check uses the frozen extraction baseline so a documented repair can change the supplier candidate.

## Verification

The commands below ran against separate disposable `git archive` snapshots of `ab0c27a7c693bafa0a2190dff3322f299297084e`. I overlaid only the amended verifier in the second snapshot. The fixture script and outputs are in `/tmp/goldbach-p35-provenance.xvYa2c`.

| Command | Snapshot | Result |
| --- | --- | --- |
| `python3 /tmp/goldbach-p35-provenance.xvYa2c/check_provenance.py` | Original base | Exit 1. The verifier accepted all nine invalid fixtures. The documented candidate-only repair passed. |
| `python3 /tmp/goldbach-p35-provenance.xvYa2c/check_provenance.py` | Base plus verifier fix | Exit 0. All nine invalid fixtures were rejected with the expected diagnostic. The documented candidate-only repair passed. |
| `python3 verification/verify_part3_continuation.py --source-only --group p35-test-seminorm --output-dir /tmp/goldbach-p35-provenance.xvYa2c/preflight` | Base plus verifier fix | Exit 0, `SOURCE_ONLY_NOT_COMPILED`, two owned modules and 55 unchanged project dependencies. |
| `python3 verification/verify_part3_continuation.py --source-only --group all --output-dir /tmp/goldbach-p35-provenance.xvYa2c/preflight-all` | Base plus verifier fix | Exit 0, `SOURCE_ONLY_NOT_COMPILED`, 17 selected continuation modules and 55 unchanged test-supplier project dependencies. |
| `git diff --check -- verification/verify_part3_continuation.py` | Shared checkout | Exit 0. |

The script exercised the actual provenance function and pointed its repository root at disposable fixtures. It refreshed the affected artifact hashes for each fixture. It checked matching changes to the supplier and baseline with an empty patch, an independent consumer edit, an incorrect excerpt digest, a correctly hashed empty excerpt, two source occurrences, an unexpected donor candidate path, an unbound donor manifest, an omitted excerpt, and a duplicate archive record. The valid repair fixture changed only the supplier candidate plus its registered patch and artifact hashes.

## Scope

An initial run against the concurrent shared working tree stopped at the existing supplier SHA-256 check because the authorized Lean repair was present before its manifest refresh. The successful source-only runs above apply to the isolated verifier change. The controller is handling the combined-candidate preflight after refreshing the patch and candidate hashes.

The independent check of upstream donor commits, complete Git blobs, and line ranges is recorded in `task-review.md`. This gate compares the hash-bound archived excerpt bytes against their intended extraction sources. The verification here was source-only and leaves strict Lean compilation, kernel replay, and the serialized declarations and transitive axiom audit to exact-head acceptance. I edited only the verifier and this report.
