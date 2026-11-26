# Cell05 rows15: P2 private receive preparation v2

**Status: locally prepared, not submitted; explicit root review and confirmation are still required.** The original P1 capsule remains intact. The checked local intermediate is `/tmp/p26-row15-transfer-557a12f3bcd7/rows15-provider-v1.tar.xz`, exactly 2397884 bytes with SHA256 `b41f83e3ec17764d06cfbd6b095c7cc499594de0c5060f78327fa0ffd351dfdd`.

## Fixed new P2 location

The receiver may write only inside:

`/workspace/p26-continuation-557a12f3bcd7/cell05-rows15-private-receive-v2`

Its final archive is `rows15-provider-v1.tar.xz` in that directory. The only other destinations are the five source/control files in `control/`, the exact 75 chunk files in `parts/`, and the new `MEMBER_PINS.json` and `RECEIVED.json` records. Each data write uses an exclusive temporary file, fsync, byte verification, and a hardlink publication that cannot overwrite an existing file. Identical existing targets are reusable; conflicting targets or incomplete pending files required for installation cause a stop. Only this receiver's fully verified temporary hardlinks are removed. Deployment refuses unknown existing files and refuses source redeployment once data files exist.

No original stage, provider, runtime guard, P1 file, or other session directory is a write destination. No cleanup of other files is implemented.

## Command size and queue policy

There are **75 chunks**, each at most **32000 raw bytes**. The maximum complete prepared command is **49396 ASCII bytes/characters**, for the source/control deployment; every prepared command is checked to be ASCII and strictly shorter than **50000 bytes/characters**. This is a conservative preparation bound requested by the root, not a claim about the service's undocumented limit.

`prepare_upload.py` saved 78 private command files: one control deployment, 75 chunk commands, one final verification command, and one optional read-only inspection command. The 77 mutation/verification steps are sequenced as deployment, chunks, then final verification; the inspection command is not an extra normal-path task. All commands carrying base64 remain exclusively under `/tmp/p26-row15-transfer-557a12f3bcd7/p2-upload-v2/`. `P2_UPLOAD_PLAN.json` contains only their paths, sizes, SHA256 values, and scoped task limits.

The root's Shape repair task has priority. After approval, the dispatcher must check fresh system information before each submission and keep global running plus queued tasks at most six, reserving at least two of the eight queue slots. It must not cancel existing jobs. An unknown submission is investigated read-only before any resubmission. An automatic approval rejection must be reported and must not trigger another route.

## Data size and terminal verification

The P2 body storage is the 2397884-byte chunk set plus the identical 2397884-byte complete archive: **4795768 bytes**, plus small controls and hash records. Deployment requires 6 MiB of available space and does not free any other files. The 267 members occupy 24427751 bytes when read in memory; they are **never extracted to disk**. Provider installation is outside this task.

Before running the receiver, each command authenticates the exact frozen `SOURCE_MANIFEST.json` and all four listed control bodies. The copied `evidence_io.py` is byte-identical to the original approved archive reader. Final verification checks the complete capsule SHA256, 267 regular members, all 266 payload member pins, the original capsule-manifest bytes, four original source anchors, the original export manifest, and all 496 mappings using their independently checked canonical digest and each embedded blob pin. Historical path strings are compared as labels; the receiver does not open their P1 or original stage paths.

The exact original 720-byte builder report is retained unchanged. Its 45 accepted steps and 5147 owned declarations describe the original builder validation. This receiver does not replay those proofs. A successful new report means `PASS_RECEIVED_CAPSULE_ONLY`, with `archive_extracted: false`, `provider_installed: false`, `complete_join_acceptance: false`, and Lean commands and new Lean acceptances both zero.

## Local evidence

`LOCAL_PREPARATION_RESULT.json` records the actual successful local preparation command. Preparation ran the final member verifier against the unchanged private capsule and checked all prepared commands syntactically and against the size bound. It submitted no P2 task. `RECEIVE_MANIFEST.json` binds the 75 exact chunks and source anchors; `SOURCE_MANIFEST.json` binds the four receiver controls; `P2_UPLOAD_PLAN.json` records their deployment and command pins. The earlier v1 candidate is preserved separately and is superseded before submission.
