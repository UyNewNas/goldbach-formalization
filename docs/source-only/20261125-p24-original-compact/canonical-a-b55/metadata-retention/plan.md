# P24 Diagnostic Metadata Retention Implementation Plan — draft01

> **For agentic workers:** Use the existing root/subagent review workflow. The owner submits the two stages as separate jobs only after reviewing this frozen draft. No remote execution is authorized by this plan artifact itself.

**Goal:** Preserve exact, independently reconstructible copies of eleven owned diagnostic JSON files, then release only those duplicate loose copies without changing canonical evidence or any acceptance claim.

**Architecture:** Keep the existing complete 1087 and b55 gzip archives and their descriptors at their original persistent paths. Stage 1 verifies both archives completely and creates one bounded supplemental gzip for three other diagnostic JSON files. A second, separately submitted job copies all three archives into an independent `/tmp` filesystem, reconstructs every original byte, checks every hash and index, and only then unlinks the eleven explicit loose paths while leaving reconstruction markers.

**Tech Stack:** Existing Python standard library, original SHA-pinned project snapshot/verification functions, the original P2 lock, and the existing qualified native snapshot. No Lean invocation or new package.

**Spec:** Root's 2026-11-26 bounded storage task; exact input paths, bytes, hashes and exclusions are in `retention-manifest.json`. `draft01-code-freeze.json` and `draft01-review.json` bind the reviewed implementation.

## Global constraints

- Canonical source remains `b55fa93d39e6a4ddf2abd37b9b8481078e329f70` with ordered full324 fingerprint `c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f`.
- Every job takes the existing `.lake/p2-private/p24-migration.lock` without creating a replacement lock. Submit after the current A job has terminated; a busy lock causes a safe failure.
- Each job dynamically reads the **current** registry and full324 snapshot. No old `1c1929…` registry digest is a launch requirement. Source, objects, live registry, native binding, runtime, original tools, and retained conditional metadata must remain unchanged within each job.
- Only the exact eleven manifest paths are release targets. No glob-based deletion, cleanup of other tasks, or removal of current `records.json`, source, objects, qualified native files, actual compile/replay/audit logs, original receipts, or either complete evidence gzip.
- A hard-linked, symlinked, changed, replaced, missing, or already-marked original causes failure before release. The second stage rechecks the same inode/mtime/ctime and SHA observed in stage 1.
- Preserve **33,554,432 bytes** free on persistent storage throughout. Stage 1 reserves a further 16 MiB bounded supplement plus 4 MiB control budget before beginning. Stage 2 reserves a further 4 MiB control budget; its independent `/tmp` must have the computed full reconstruction size plus 32 MiB and a different filesystem device.
- Proposed outer envelope: at most 900 seconds, 13,107 MiB, one CPU. These jobs run no compiler and change no Lean options, checker budgets, audit criteria or templates.
- All results are storage diagnostics. They grant no A/B/W, compiler, replay, owned, full324, P2.4, or 6.809 acceptance.

## Exact release scope

| Group | Files | Logical bytes | Durable input after stage 1 |
|---|---:|---:|---|
| 1087 attempt: registry before/after and full324 before/after snapshots | 4 | 54,562,939 | Existing `evidence-1087.tar.gz`, Git blob `0d5b63eca23cc09afea6d4d56890737776158cde` |
| b55 attempt: the same four snapshot names | 4 | 54,590,909 | Existing `evidence-b55.tar.gz`, Git blob `7b3252c9955d39cde67b0396aa644d0a73097291` |
| Two FiniteSelector selected-records JSONs and the flags inventories JSON | 3 | 13,074,803 | New `supplement.tar.gz` and its complete descriptor |
| **Total** | **11** | **122,228,651** | All original bytes and path mapping retained |

The older large-file inventory totals 121,503,391 bytes for this group because it omits the four 181,315-byte full324 snapshots. The complete archive descriptors supply those additional 725,260 bytes. The manifest binds every individual path and SHA rather than inferring eligibility from this table.

### Excluded conditional files

The two `.lake/p24-cache-migration/attempt-001/{ORIGINAL_DONOR_RECORDS.json,MIGRATION.json}` files remain in place. The three locked original driver/audit/export tools have no direct hard-coded reads of those names, but that does not establish independence from every qualified-snapshot or historical consumer.

The old 11,997,843-byte export `manifest.json` also remains. The proven reconstruction function reads its preserved bundle copy, but the existing `retention_common.original_state` and earlier release-verification script still read the original loose path. This draft does not alter those consumers.

The original sole `preserved-members.tar.xz`, original descriptors and recipes, and every non-whitelisted file are retained. No conditional path is enabled by a command-line flag.

## Review focus and its checks

1. **Incomplete or corrupted backup:** compare complete gzip length/SHA, exact whole tar length/SHA, every unique regular member, and the complete `FILES.json` index before any release. Local corruption, missing-count and extra-member tests reject the input.
2. **Symlink, hard link, path traversal or substituted original:** fixed absolute whitelist, canonical resolved paths, no-follow opens, single-link originals, and saved inode/mtime/ctime/SHA checks. Local negative fixtures cover each class.
3. **Partial failure after an unlink:** record each successful unlink immediately; in `finally`, independently enumerate all eleven paths as missing/remaining/uninspectable. The failure receipt distinguishes successful events from actual observed missing files. A dedicated fixture covers missing files without any appended event.
4. **Changing canonical environment:** use original full324 `snapshot`, original `verify_compilation` on the accepted 321 prerequisites, current raw registry SHA, original live Mathlib pin, runtime hashes and qualified native verification before and after each stage. This is read-only validation, not a gate run or new credit.
5. **Insufficient or shared storage:** enforce the persistent reserve and a strict supplement-size bound; require a separate `/tmp` filesystem for reconstruction. Preserve all originals if preparation or reconstruction fails. Report observed `statvfs` deltas separately from logical bytes and allocated blocks.

## Task 1: Durable preparation, in one new job

**Files:** `stage1-command.sh`, `stage1_preserve.py`, `retention_common.py`, `retention-manifest.json`.

**Consumes:** Both already retained gzip archives and exact descriptors; the eleven original loose JSONs; current b55 canonical context.

**Produces:** `/workspace/p24-diagnostic-metadata-retention-20261126/attempt-001/{supplement.tar.gz,supplement-descriptor.json,stage1-receipt.json,stage1-space.json}`. The two existing gzip archives remain at their original paths.

- [x] Implement the exact whitelist and dynamic original canonical guards.
- [x] Implement full archive/member/index validation and bounded supplemental archive construction.
- [x] Verify fixture roundtrips and rejection cases locally; inspect the prepared command with `bash -n`.
- [ ] Owner submits the frozen `stage1-command.sh` after A has terminated and after review. It installs scripts only into a fresh owned directory, then runs stage 1 under the original lock.
- [ ] Owner retrieves the actual complete small task output and successful task metadata. Record the exact stage1 receipt SHA and task ID for the next job. An incomplete `.incomplete` supplement or failed receipt is never usable preservation evidence.

This stage performs **no original unlink**. Existing gzip files are fsynced and retained; their compressed bytes, complete tar streams and full per-member indices are all verified. Only the three extras require a new archive. No uncompressed tar is retained on persistent storage.

## Task 2: Independent reconstruction and explicit release, in another job

**Files:** `stage2-command-template.sh`, `stage2_verify_release.py`.

**Consumes:** The successful first task's exact metadata, SHA-bound stage1 receipt, unchanged scripts/manifest, all three durable archives, and the same eleven original files.

**Produces:** Persistent reconstruction markers beside the eleven original paths, full per-release events, a truthful success or partial-failure receipt, and actual space accounting under `attempt-001/stage2/`.

- [ ] Owner fills the template with the actual successful first task ID, exact `get_task` JSON SHA and stage1 receipt SHA; placeholders fail before workspace mutation. Submit as a separate tool job, not as a second process chained into stage 1.
- [ ] Verify all three complete gzip copies in independent `/tmp`; materialize and check all complete tar bytes and all eleven original JSONs there. Never regenerate tar metadata or substitute a newly serialized JSON object for original bytes.
- [ ] Verify every original remains the same regular single-link inode and bytes observed in stage 1. Recheck the current canonical context before any unlink.
- [ ] Write and fsync all reconstruction markers first. The only release loop visits the exact eleven manifest entries. It records successful unlink events and independently observes the final state even on failure.
- [ ] Retain the persistent archives and descriptors, check current canonical state again, and preserve the actual return code. Report successful completion only when all eleven are missing as intended and all postchecks pass.

The first task's operational status and receipt are explicit inputs. Actual separate-job submission is the owner's responsibility; the script additionally checks a fresh process and a genuinely succeeded task metadata record. It does not manufacture remote task provenance.

## Recovery

`restore_metadata.py --path <exact original whitelist path>` reads the durable marker and the SHA-bound preservation receipt, verifies the complete backing archive, reconstructs and hashes the selected member, and installs it exclusively at its original absent path. It never overwrites an existing file or symlink. An original path is only installed after a temporary sibling has been fully verified and fsynced; `link()` supplies exclusive installation, and only that newly created temporary sibling is removed.

Markers are reconstruction references, not counterfeit original JSON files. They explicitly identify the archive, complete tar SHA, member SHA and release receipt. Existing original receipts and historical failed logs are not rewritten to hide the storage transition.

## Capacity and accounting

At the prior measured 379,904,000 bytes free, even the entire logical eleven-file release leaves a **42,017,896-byte** gap relative to the 510,596,115-byte P3 serialization reference plus 32 MiB reserve. A new supplement, markers and receipts add storage cost. Canonical A's actual audit size and remaining audit/export growth remain unmeasured.

Each stage reports `free_bytes_after_all_persistent_writes` from a final `statvfs` after its own control files. The receipt also records logical bytes and actual pre-unlink `st_blocks * 512`; these are distinct from physical free-space gain. Add observed deltas for the two job intervals only, and do not attribute unrelated allocations between jobs to this workflow. No free-space gain is claimed before actual execution.

## Validation and handoff status

Eight local fixture tests pass; Python syntax checks pass. Two agents independently read the frozen main safety and restoration boundaries. A concrete unlink-adjacent failure-accounting issue was found and repaired before freezing draft01; the added negative fixture passed.

**No P2 job has been submitted. No metadata, source, object, native file, log or current registry has been removed or modified.** This is a prepared workflow, not a remotely verified release result. The separate `draft02/` design considers retaining the two complete tar streams inside a solid xz bundle and subsequently releasing the derived gzip copies; its additional steps are not covered by draft01's implementation or reviews.
