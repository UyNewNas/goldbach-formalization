# Publication pack and receiver review

Review date: 2026-11-26 UTC.

Conclusion: **No blocking defect found within the reviewed publication path.**
This is a bounded source review and local verification/control-flow review.
The real P1 receiver verification and work-branch publication remained pending
the controller's execution when this review was written. This document is not
a receiver receipt or proof that the work ref has been published.

## Frozen scope

The reviewed candidate was
`2b672cdc4e5cd2b85107485762bd8a1abfa6e1d0`. The following file hashes were
independently checked before the tests and again before writing this record:

| File in `execution/` | SHA-256 |
| --- | --- |
| `receive_publish_work.py` | `526fb3c9079713381d53a56ab48c520d53836e4a67da7122fbd56bed32c06ec4` |
| `build_publication_pack.py` | `5d94e71fa3c8c5969f6bc84fd94eb9e5240f476691d6a1b9e808c1354212581d` |
| Reused `transport_group_artifacts.py` | `7652ccfee12b1496928d0ff68c28ba68929195ec1201b60f0a9cadf5aaa1c4ee` |

The publication path binds these checkpoints:

| Role | Exact value |
| --- | --- |
| Work baseline | `b3f306cc3b430fc40c3b3ec4110d323443d2f609` |
| Published artifact commit | `59cf6341935bc0b8b780526e2d9d2f12d5f1a893` |
| Artifact parent | `f86223d06127fb6a0f3394ce4f6479e1e27fcfde` |
| Work ref | `refs/heads/work/p3-6-warm-payment-20261126` |
| Artifact ref | `refs/heads/artifacts/p36-normalized-density-20261126` |

The controller reported that the artifact commit had been published and all
five files recovered and verified. This reviewer did not repeat that network
operation. The earlier destination/authentication review is recorded in
`ARTIFACT_TRANSPORT_REVIEW.md`.

This review covers pack construction, receiver validation, publication command
selection and post-write handling. It does not replace the separate review of
mathematics, original compiler evidence, whole-branch content or owner inventory.
It changed no implementation or exporter bytes, invoked no cloud tools, made no
external request and executed no Git push, including no local Git push.

## Input, object and evidence binding

The builder selects the exact `target ^ base` revision object set, then excludes
only the five explicitly named evidence blobs. It does not exclude an unrelated
artifact revision as a shortcut. Each excluded blob must have the same object
ID, size and SHA-256 in the fixed artifact tree, the target's `accepted-group`
tree and the retained artifact-publication pins. Both tree entries must be
regular `100644` blobs. The artifact must have the exact fixed parent.

`pack-objects` is given the explicit remaining object inventory. Delta reuse and
object reuse are disabled and the window is zero. `index-pack --strict` and
`verify-pack` check the pack; the resulting inventory must be exact and every
object listing must be a full-object entry. The pack header count and trailer
are recorded together with SHA-256 and size pins for all transport inputs.

The receiver first checks `PACK_MANIFEST.json` against the separately supplied
SHA-256. It then checks the fixed baseline, target and artifact fields and the
exact permitted input-name set: seven required files, with only the optional
`publication.rev` additionally permitted. Each listed input must be a regular
non-symlink file with its exact SHA-256 and positive byte count. Path traversal
names cannot enter this input map. The independently supplied manifest hash is
the input trust anchor; the builder's status and self-hash are not substitutes
for receiver verification.

The receiver rechecks the five artifact blobs and their fixed paths before
import. It requires a bare, non-shallow receiver. The object lists must be
canonical, unique and sorted; their union/difference must represent exactly
five distinct exclusions. The actual imported pack is indexed again, and its
receiver-generated index is used for the exact full-object inventory check.
The transported index and verification text do not stand in for those checks.

After import, the receiver checks all of the following against actual objects:

- Baseline, expected remote and target are exact commit objects, with
  `baseline <= expected remote <= target` by ancestry.
- The receiver's `target ^ base` walk exactly matches the complete declared
  new-object inventory, including the five excluded blobs.
- All five target evidence paths have the same regular-file mode, blob ID,
  size and SHA-256 as their fixed artifact counterparts.
- A complete target-history object walk has no missing-object markers, and
  `git fsck --full --no-reflogs --no-dangling <target>` succeeds.
- The complete baseline-to-target path diff, including order, statuses,
  modes, blob IDs, byte counts and SHA-256 values, equals `CHANGED_FILES.json`.

Replacement objects, graft files and caller-supplied shallow-file overrides
are suppressed in the receiver's Git helper. The receiver retains
`whole_p36_closed = false` and `currentVerified = false`; the publication path
does not promote the mathematical completion state.

## Destination and publication behavior

The receiver verifies the transport source's complete SHA-256 before executing
those exact bytes. It also checks the reused ref constants. The previously
reviewed `locked_destination` resolves and validates the one allowed GitHub
HTTPS push endpoint, then uses a temporary isolated carrier whose copied
configuration preserves authentication while excluding URL rewrites/includes
and disabling HTTP redirects. The prior review established its private
configuration permissions and generic error reporting. No new destination or
credential-copy implementation was introduced in the receiver.

The CLI `publish` route always performs receiver verification in that invocation
before calling the publisher. It does not accept an old success record as
authority to skip verification. The publisher reads both refs through the
locked carrier, requires the exact artifact checkpoint, and requires the work
ref to be either the independently expected ancestor or the exact target.

The sole write command is the following ordinary, single-ref push through that
same carrier, with the verified receiver object directory explicitly supplied
as an alternate:

```text
git push --porcelain --no-follow-tags --recurse-submodules=no \
  p36-validated-destination <exact-target>:refs/heads/work/p3-6-warm-payment-20261126
```

There is no force option, leading `+`, mirror operation, implicit all-ref push,
tag following or submodule push. The actual endpoint is read again before a
success record is issued. If the exact target is already present and the
artifact pin matches, publication is idempotent and makes no push attempt.

On a push error or a failed post-push check, the script attempts to retain a
`PUBLICATION_OUTCOME_UNCONFIRMED` record and explicitly says the work ref may
already have changed. The separate `readback` action performs only the locked
remote ref read; it does not install the pack or attempt another push.

## Independent local checks actually performed

The object-verification fixture used small temporary bare Git repositories and
real Git commands. Only the fixed commit constants were replaced in module
memory with synthetic fixture commits; production files were not edited. The
production transport source was loaded through its real SHA-256 guard.

| Check | Observed result |
| --- | --- |
| Real builder to receiver verification | Passed with 15 new objects, exactly 5 excluded evidence blobs, 10 full packed objects, and 9 changed paths covering additions, modification, deletion and a regular-file-to-symlink type change. |
| Full receiver integrity checks | Strict import, exact inventories, complete history walk, full fsck and recomputed changed-file metadata passed. Source and receiver refs were unchanged. |
| Wrong independently supplied manifest SHA | Rejected before import. |
| Changed input bytes under the original manifest | Rejected on the input file hash/size comparison. |
| Additional `../escape` manifest file name, with a recomputed manifest pin | Rejected by the exact permitted name set. |
| `currentVerified` changed to true, with a recomputed manifest pin | Rejected as a fixed-field mismatch. |
| Incorrect evidence SHA-256 in a repinned excluded-blob file | Rejected against the actual retained artifact blob bytes. |
| Incorrect changed-file SHA-256 in a repinned input | Rejected against receiver-recomputed tree/blob metadata. |
| Shallow receiver | Rejected before pack import. |
| Missing blob used only by an older ancestor | Rejected by the full target-history closure check. |

The receiver Git-call interceptor observed 165 actual local verification calls
across the positive and rejection cases. None invoked `push`, `fetch`,
`ls-remote` or `clone`. Temporary repositories were removed after the checks.

The publication control checks used intercepted ref reads and an intercepted
Git helper; **they did not execute a Git push or contact an endpoint**:

| Check | Observed result |
| --- | --- |
| Normal publication control path | One locked carrier was used for read, exact ordinary-FF command selection and readback. The explicit alternate-object directory matched the verified receiver. |
| Target already present | No push was selected. |
| Wrong pre-write artifact or unexpected pre-write work ref | Failed before selecting a push. |
| Post-write artifact drift | Failed with the explicit possibly-written warning and retained an uncertain-outcome record. |
| Simulated push error | Retained the same explicit uncertain-outcome handling. |
| Direct readback | Performed one locked ref read and no pack-installation/push helper call. |
| CLI dispatch | `publish` invoked verification first; verification failure prevented publisher dispatch; `readback` did not invoke verification or publication. |

All nine separately executed publication-control checks completed successfully.
Local fixture setup required correcting two test-harness assumptions (an exact
error-message expectation and a test label containing `/`); these were not
product failures and required no product edits. The individual object checks
listed above had completed successfully before the latter harness issue; the
publication-control checks were then run separately to completion.

## Limits and remaining execution evidence

The manifest SHA and exact final target commit must come from the controller's
independent frozen inputs. This review is about the byte-pinned tools, not a
particular future pack's contents. If the review record is committed afterward,
the resulting final target and pack must be regenerated and independently
pinned for that final commit.

Input files and the receiver object store are assumed to remain stable during
one invocation. The scripts do not provide a lock against a hostile concurrent
local writer. Output verification records are created exclusively and retained
instead of overwriting earlier differing records.

The pre/post work and artifact ref reads are snapshots, not an atomic lock
across both refs. An ordinary FF push protects against overwriting a divergent
remote work history, but it does not prove that the artifact ref remained
unchanged throughout the interval. Post-write mismatches are deliberately
reported as uncertain publication outcomes and require readback.

This reviewer did not test real P1 authentication, install the actual final
publication pack on P1, execute the actual P1 receiver, publish the work ref or
read GitHub afterward. Those concrete receiver checks and publication receipts
remain the controller's execution evidence. This review creates no new Lean
compilation, replay, inventory or whole-node completion claim.
