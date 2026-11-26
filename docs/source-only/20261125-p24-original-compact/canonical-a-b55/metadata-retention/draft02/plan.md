# Solid XZ preservation of thirteen exact diagnostic files — draft02

## Scope and state

This is a separate candidate; draft01 remains frozen. Root has submitted draft02's **preservation-only** stage as task `f4ea526437424a519930753257d6e725`, using the reviewed command SHA `9dae9bad3d82bbb905a3d94be6b1c0940be7cc709a7e66068f01774f680ccc2b`. The command is 31,863 bytes, below the 65,536-byte transport limit. Its nine installed files are bound by `transport-manifest.json`.

This document records preparation and local validation. It does not assert that the P2 task has succeeded. Stage 2 remains an unfilled template until root supplies the actual successful first-task metadata and exact receipt SHA. This agent has not submitted or executed either P2 stage.

## What changes from draft01

Draft01 retains two existing gzip archives and makes a third small supplement. Draft02 instead preserves **both complete decompressed tar streams**, all three extra JSON files, the exact original descriptors, original commands and blob bindings, the current recovery scripts and manifest, the gzip runtime profile, the original-file identity map and the canonical context in one solid XZ archive.

The new outer tar has 21 explicitly indexed regular members. Its two inner tar members contain the entire original 20-member 1087 archive and 23-member b55 archive, including their exact `FILES.json`, tar headers, ordering, padding and all original evidence bytes. The compressed old gzip files are not merely nested inside xz.

Only after a **different job** reconstructs and checks all thirteen original files may the exact release list expand from eleven diagnostic JSON files to those eleven plus the two derived gzip files. Original gzip descriptors, original Git blobs, the new solid xz, all original receipts and actual logs, and the three previously excluded metadata files remain retained.

| Release group | Files | Logical bytes |
|---|---:|---:|
| Eight gate snapshots and three extra diagnostic JSONs | 11 | 122,228,651 |
| Existing 1087 and b55 derived gzip files | 2 | 13,649,209 |
| **Complete explicit whitelist** | **13** | **135,877,860** |

The exact paths, sizes, hashes and member mappings are in `retention-manifest.json`, SHA `d8ec23b6d0d2aca0ffc4f24abc4693c3df7f587f23336757c37417391d5af71a`. No command-line option can add a path.

## Exact gzip reproduction

Both original archived command sources were checked: their original call is exactly `gzip.compress(tar, mtime=0)`, with no explicit `compresslevel`. Draft02 preserves that literal call. It records the actual implicit default, complete Python version and interpreter hash, gzip source hash, zlib compiled/runtime versions, the extension hash or the executable owning a built-in zlib, the signature, platform and byte order.

Stage 1 requires the current runtime to recreate **both** original gzip lengths, SHA-256 values, raw Git blob IDs and byte-for-byte contents. Stage 2 requires the identical runtime profile and performs the same reconstruction from the stored complete tar streams. It also validates every inner tar member and complete inner `FILES.json`. No gzip-header patch, new tar serialization, reserialized JSON, guessed compression setting or saved output value substitutes for this check.

The actual two gzip files have already been independently reproduced on the primary local runtime in 5.129 seconds, with exact byte equality and both original hashes. This is recorded in `primary-gzip-recipe-check.json`. It is **not** evidence that P2's two-job preservation/release has completed; P2 must perform the same checks itself.

## First job: durable preservation, no release

1. Acquire the original existing lock. Validate source pin b55, the full ordered324 closure, all fixed original tool/source hashes, live Mathlib pin, Lean/checker bytes and the qualified native binding. Read the current registry dynamically and use the original read-only verification API on the valid 321 prerequisites. Observe the current A/B/W record headers without assigning new credit.
2. Require the independent `/tmp` filesystem and enough temporary capacity. Build the complete solid xz there with preset 6 and CRC64. Record the exact whole outer-tar hash and every member/index hash.
3. Independently read back that xz, reconstruct all thirteen originals using only the xz plus the SHA-bound installed recipe/runtime, and compare every reconstructed byte to the original paths.
4. After the **actual** compressed size is known, require persistent free space for that exact size, control files and the original 32 MiB reserve. Copy and fsync the verified archive into a fresh persistent attempt directory, verify it again, and publish its descriptor and preservation receipt. Never delete an original in this job.
5. Recheck all original file identities, code/runtime bindings and the complete canonical context. The actual first job is successful only if these checks pass. A failed or incomplete artifact is not a usable preservation receipt.

The code performs an additional exact reconstruction-space check after the temporary bundle already exists: copied xz + all extracted outer members + duplicate inner JSONs + both rebuilt gzips + allocation overhead + 32 MiB. This avoids treating an initial `/tmp` estimate as proof that the later peak fits.

## Second job: independent full reconstruction before thirteen releases

`stage2-command-template.sh` deliberately contains invalid placeholders. Root must fill the actual succeeded task ID, exact task-status JSON SHA, and exact stage1 receipt SHA, and submit it as a new job. It rejects missing/failed first-task evidence and changed recipe bytes before release.

The second job uses the persistent xz to reconstruct all thirteen exact files into an independently created `/tmp` directory. It needs no original loose JSON or gzip as a reconstruction input. Originals are read only for the final independent byte comparison and identity checks. A local fixture explicitly moved all thirteen originals away before reconstruction and still recovered every byte.

After all reconstructions pass, it rechecks the canonical context and creates/fsyncs all thirteen small reconstruction markers. It then visits only the exact manifest list: eleven JSONs first, the two derived gzip files last. Immediately before each unlink it rechecks regular-file status, single-link status, inode, mtime, ctime, length and SHA.

Successful unlink events are recorded before any subsequent operation that can fail. The final receipt independently reports all thirteen actual missing/remaining/uninspectable paths, so an fsync or statvfs failure cannot hide a partial release. Success requires all thirteen intended originals absent, the solid xz and descriptors unchanged, and all canonical postchecks passing. Failure remains failure even when some safe releases already happened.

## Recovery and retained boundaries

Each marker binds the sole persistent xz, its complete outer-tar and `FILES` hashes, the exact original target and member mapping, the preservation receipt, the actual first-task ID, and the release receipt. A marker is not presented as the original JSON or gzip.

`restore_metadata.py --path <exact whitelist path>` reconstructs from xz only, validates all bytes, writes a new verified temporary sibling, then uses an exclusive hard-link installation. It never overwrites an existing file or symlink. The same b55/runtime guards currently apply to restoration; if the environment is later intentionally changed, restoration safely refuses until a separately reviewed recovery procedure handles that change. Original retained bytes do not become dependent on the deleted loose paths.

The following remain excluded: both cache-migration JSONs, the old original export manifest, original source/object/native files, current `records.json`, actual audit/compile/replay logs, receipts, all other task files, and the old sole retained `preserved-members.tar.xz`.

## Capacity and memory

Root's newer actual A serialization measurement is 485,251,971 bytes. Together with the unchanged 32 MiB reserve this requires at least 518,806,403 bytes, before remaining audits/export preservation and control files. The 377,823,232-byte free-space sample preceded the newly created 10,708,984-byte capacity gzip, giving at most 367,114,248 bytes before further owned11 gzip costs. Even an ideal zero-cost release of all thirteen logical file bytes leaves a **15,814,295-byte** gap against that sample, before the new xz, markers and later allocations. This is a lower bound, not a prediction of current free space.

The script therefore reports the actual xz size and final physical `statvfs` values; logical bytes and `st_blocks * 512` are separate fields. It records deployment cost and stage cost separately. No savings are credited before the actual release. `/tmp` is tmpfs on this P2 environment and counts against the existing 13,107 MiB job memory limit; its independent filesystem does not supply extra memory allowance.

## Validation

- Six local fixture tests pass, including full thirteen-file reconstruction with all original paths absent, changed-runtime rejection, truncated-xz rejection, incomplete inventory rejection, unexpected extraction rejection, and insufficient temporary capacity rejected before copying.
- The first fixture run exposed that this Python has a built-in zlib without `__file__`. The runtime binding now explicitly identifies that case and hashes its owning interpreter; the failed local run and correction are recorded in the local validation summary.
- Python syntax, shell syntax and the complete nine-file transport roundtrip pass.
- Two independent reviewers checked the new solid-xz dependency and release chain. The detailed review is `independent-kernel-review-draft02.json`; these are static reviews, not P2 release receipts.

All Lean source, numerical targets, compiler/audit budgets, original gates and full acceptance boundaries remain unchanged. This storage workflow grants no new mathematical or audit acceptance.
