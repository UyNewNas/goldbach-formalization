# B1 raw backup: independent all-member review

**New archive findings: 0 Critical / 0 Important / 0 Minor. The actual selected-byte backup is accepted.** This review does not repeat B1 mathematical/source QA or create new proof credit. Accepted1643 is the previously verified endpoint; source Minor M1 remains deferred, and190 core owners plus17 postfinite candidates remain unaccepted. Public-tree/README/FILES review has not yet been performed.

## Actual immutable backup outputs

Actual backup job `121f252ede44406cbd592093c41d013e` succeeded with exit0 in37.96945619100006s,184270848 B peak memory and36.88s CPU. Its safe result is `/workspace/p26-cell06-b1-raw-backup-20261128/MCP_BACKUP_RESULT.json`,1373 B/SHA256 `7e9e44d8f01da78c53fc3f22707874688051d3ed530eb609a586f03a75df924a`. The558-byte actual output binds all three measured output pins; no truncation/discard occurred. This was a raw-copy/compression job with2048MiB/CPU1/900s limits, not a proof job.

Output root: `/workspace/p26-cell06-b1-raw-backup-20261128/output`.

| Output | Bytes | SHA256 |
|---|---:|---|
| CAPSULE.json |1822|`bc94d7e746b8fddde4ca12272899dd7a01914f5617f0cf4c915d6989f6ba8270`|
| MANIFEST.json |103948|`1ef30a69f6f469db442ca0e6e9f57c47e21176aa3ea65403d112876e81eafb94`|
| evidence.tar.xz |11299424|`28582eb25723f63b719096f8b6df28818bb550a310373704697d1479079e86f5`|

All actual output bytes match these pins, and the output directory contains exactly these three regular output files. The measured archive is below the explicit90MiB cap; no fallback volume or invented prospective compression result is claimed.

Frozen controls:

| Input | Bytes | SHA256 |
|---|---:|---|
| MEMBERS.json |5596514|`2936e83fe3700bbeabc9fce5a36587efa8057f1f63421c7a8d709c56132e541c`|
| PLAN.md |4848|`24e94ccc3eb60eb302886a28e0bf9f93ad99a6cab8dd550629be718231f2427f`|
| assemble_raw_backup.py |6213|`eaeb60b69aaf53a0e1cc505f4d003257678716e824fb96ce00f195b8ef557e4d`|
| INPUT_CONTRACT_001.json |1651|`fab8396a733350e1600b57a4cd2965d09a3124919b8e57ccadf29136b003cc7d`|
| ACTUAL_BACKUP_COMMAND.txt |845|`2270cfed172d0081f04c7483d79f08a4b20a0e9956c9acedccd225eb3a6d57b0`|

The assembler source imports only hashlib,io,json,os,pathlib,stat,sys,tarfile. Static inspection found no subprocess/proof/test/collector/seed invocation. Its action is explicit original-byte reads plus exclusive metadata/tar.xz writes in the new output directory. The actual source and input pins match the frozen contract. The assembler was not rerun or mirrored by an implementation test.

## Complete streaming raw-byte comparison

The external manifest exactly equals the198 inventory entries plus the three specified controls, including original roles, aliases and raw-copy policy. The actual archive was then consumed once with streaming tar/xz reads. **Every regular member's complete decompressed byte stream was directly compared chunk-by-chunk with its declared original source file**, while SHA256/size were independently computed and checked against the manifest's full source pin. No member was reconstructed from parsed JSON or reformatted source.

| Accounting | Members | Raw bytes |
|---|---:|---:|
| Original inventory |198|126939177|
| Added inventory/PLAN/assembler controls |3|5607575|
| Payload total |201|132546752|
| Exact inner MANIFEST |1|103948|
| All regular member bodies |202|132650700|

All202 bodies matched. The198→201 transformation is exactly the approved extras, not a dropped original member or added unrelated payload. The inner MANIFEST is byte-identical to the external103948-byte MANIFEST. It describes only the201 payloads and does not list itself, the outer capsule or archive as a source member. CAPSULE is outside the archive and points to the final manifest/archive pins. This avoids a self-hash cycle without editing any original record.

All source files were regular/nonsymlink, had link count1, and lay under explicit workspace paths with no symlink ancestors or traversal. Tar member names are unique normalized relative POSIX paths with no dot/dotdot/empty component, absolute root, drive prefix, backslash or NUL. All202 entries are regular files, without symlinks, hardlinks, sparse bodies or linkname values. PAX metadata is limited to long path names; no hidden logical payloads were counted as evidence. Headers use normalized0644/uid0/gid0/mtime0; the original **body bytes**, not original filesystem permissions/timestamps, are the preserved evidence.

## Required evidence is present once and unchanged

The complete original stage is preserved:28 files/7451241 raw bytes, with exact stage-relative archive names. This includes the original three COMMAND/LOCAL_INPUTS/PROCESS_RETURN/RESULT/PENDING/log chains, the unique normal artifact, original PRE/GLOBAL_PRE/POST, seal, context, helper, selector, whitelist and BATCH. This review verifies byte preservation and full membership; it does not rerun the earlier semantic/proof checks.

The sole compiled .olean payload is the original normal artifact361888 B/SHA256 `27313d74c13b86268efeea881427a2bc1defd77331a7223d5c44a41e9b94f8c7`. It occurs exactly once. The canonical object has that same byte pin but is an explicit alias/reference, not a second archived normal body. Its metadata matches the existing actual-run QA's canonical/permanent records.

The complete typed full-owned log is603080 B/SHA256 `2ba1782ee8aec3cee58c48a0dcdd2398b4d3ca62b68b8a16dd61e8234c5375ce` and is present exactly once. The three original historical mode-formalfalse/batch_post-null/PENDING bytes are unchanged, as are no-repeat snapshots and original mode times. Their historical flags were not rewritten to resemble the final batch status.

Current acceptance is bound instead by the raw final seal40830 B/de7c08…, C*5607254 B/000ed345…, and the actual independent run QA: READBACK103174 B/ab32d2… and REPORT13848 B/2ed42b…. Both QA roles are ACTUAL_COMPLETE and both exact original bodies are archive members. The capsule/input/manifest reference those same accepted artifacts. The archive operation's formalfalse/new mathematical credit0 is consistent with previously verified1643; it does not withdraw or create mathematical acceptance.

## Previous publication and reference-only boundaries

The immutable backreference chain is consistent:

- Published parent commit `f020dccdef2f54288e5e1e403cca15c085f241ee`, path `docs/verification/20261128-p26-cell06-qualified1642`.
- Parent CAPSULE4415 B/`f84aae9aade3ef1f555305fdf29ed422d1e97f5ae88267f357bc800bc30bf197` was read as metadata and matched its pin.
- That capsule references the declared parent MANIFEST169918 B/42f9ab… and archive10529540 B/`5b42a3a58f02f504c980e3a8c895d3b7c0ed4ea1a6dc169e556a3a5903d9bb55`, together with qualified1642 context e22fc5… .

This verifies pointer consistency. The previous archive body, old public Git tree and mathematical QA were not scanned or rerun here. No new claim about those bodies is made by the backup operation.

The G catalog retains the previously verified153274/20088631248/map136bad… identity as metadata. Original G leaves, the1.849GB inherited copy payloads, runtime/555 native bodies and1642 restored-parent objects remain **references**, not new archived body validations. Full pins inside selected baseline/family/transport/certificate metadata are preserved, but a pin list is not a second raw body or fresh G pass. This package is the approved selected-evidence delta, not a standalone full1643 environment snapshot. original_full_snapshot_verified remains false.

## Credential-pattern and source-risk scope

The complete decompressed bytes of all202 members were scanned for private-key PEM headers, common GitHub/OpenAI token shapes, AWS access-key IDs, Authorization Bearer values and signed/credential-bearing query values, including chunk boundaries. There were **0 matches** under those defined patterns; matching values would not have been printed. This is a bounded pattern check, not an assertion about reference-only bodies or every possible confidential-data class.

The raw evidence intentionally contains absolute workspace/toolchain paths, module names and full mathematical types, command/attempt identities and safe worker metrics. Those are part of the authorized original-byte evidence. No credential pattern was observed. No original bytes were redacted or silently replaced.

M1 remains the existing deferred source Minor: strict_json rejects named NaN/Infinity but numeric overflow literals can become infinity. The original source/host/QA risk records are preserved unchanged. No supplied real-input issue was found, no source guard was changed and no zero-Minor claim is made for the inherited source review. This raw-copy review has no new findings and does not reopen source/mathematical QA.

## Publication boundary and review outputs

CAPSULE accurately states backup-only operation_formal_acceptance false, new mathematical credit0, proof-process calls0, G scans0, previously verified endpoint1643, source M1 deferred, and Cell06 integral/P2.6/full-snapshot false. Its independent-archive-review-pending flag is the immutable creation-time snapshot; this new report supplies completed independent readback without rewriting the capsule. Inventory's earlier request/pending flags likewise remain historical, while its current ledger1643 and two ACTUAL_COMPLETE QA entries identify the later status.

This review does **not** check the pending public FILES/README tree. Root may now add these two exact review files to the final explicit public whitelist. The separately activated public-tree check should inspect only those new public copies and claims, reusing this archive result without another archive sweep or B1 QA.

READBACK.json:114124 B, SHA256 `5e17023470fb0a888409ab55a6a1bed6d0f6fc2ef82863e9b9feac01c13231d0`. It contains complete output/input pins and all202 member-source/hash comparison records, safety/statistics, prior publication references and explicit scope/credit fields.

Reviewer calls:0 old QA,0 modes,0 G,0 assembler/producer,0 Lean/tests/Git/network/MCP. Writes are exclusive to this new review root. No provider/repository file was changed. New proof credit0; accepted1643 remains the existing actual-run result, with190 core owners and17 postfinite candidates still open.
