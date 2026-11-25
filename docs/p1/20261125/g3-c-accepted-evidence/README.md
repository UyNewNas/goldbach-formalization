# G3 C0000–C0046: one accepted literal-data owner

**Accepted scope:** `ImbalancedChen.P4AOriginalNewFifthArchiveDataC0000ToC0046` at source commit `e421f8cd5aad3d9c53933dec3c77bb530bb52f8c`, with **47 owned / 47 public definitions**, named `ImbalancedChen.P4AOriginalNewFifthArchiveData.C0000` through `C0046`.

These are the original literal definitions of `P4AOriginalNewFifthArchiveReader.Block`. This receipt does not accept `Archive94Checked`, the facade, the other partition owners, the whole G3 result or full P1. The original partition manifest remains frozen with its source-only status; the actual receipt records the narrower completed acceptance.

## Actual normal and audit evidence

| Stage | Actual task / command | Elapsed time | Result |
|---|---|---:|---|
| Normal platform task | `job_39badb024d0b42a2b594b396eb49936a` | 613.6376628875732 s | succeeded, exit 0 |
| Guarded normal build | `lake build +ImbalancedChen.P4AOriginalNewFifthArchiveDataC0000ToC0046:olean` | 589.1405560589992 s | exactly this owner built |
| Audit platform task | `job_1d2d8bc4a2854974b8513a89a91414e6` | 73.73489785194397 s | succeeded, exit 0 |
| Independent kernel replay | `lake env leanchecker --verbose` on this owner | 41.23774300099831 s | exit 0 |
| All owned types and axioms | Guarded `lake env lean` on the fixed audit program | 8.538897103997442 s | exit 0; exact 47 records |

The platform's measured normal peak was **9,085,759,488 bytes**; the audit peak was **7,262,072,832 bytes**. Both platform records are saved in `LOCAL_VERIFICATION.json` with their scratch-source hashes. These are observed measurements, not estimates. The platform task windows enclose the corresponding archived commands.

The full-owned log and `OWNED_EXPORTS.json` agree exactly: all 47 entries are public definitions with the expected `Reader.Block` type, and **every axiom set is empty**. There are no missing or additional owned names. The original successful C normal build was reused for the audit; it was not repeated.

## Source, Reader and fixture binding

The accepted C source is 5,269 bytes, SHA256 `6008e9046bd0ff9f0d4e721f7c7a34d9494e4334e6e50a0ab2f90c7a15394235`. Its 47 definition lines are byte-identical to the original monolithic Data backup. All 92 sources in the partition binding match exact e421 Git objects. Recomputing imports gives the C owner's 68-source closure, comprising the new owner and the existing Reader's 67-source closure.

The Reader was reused from its accepted AUDIT24 receipt: all 67 dependency-source hashes and its source plus five output fingerprints match. It was not rebuilt or counted as new acceptance. The old Reader runtime-state hash and the current member runtime-state hash are distinct; both are separately pinned and preserved in the frozen runtime binding, with the same audit-template hash. No resource or guard change is involved in this review.

The partition's complete 188-file fixture map equals the original inventory by path, size and SHA256. The executed driver performed its full 188-file live fingerprint gate before each phase. Each durable owner checkpoint separately records the **94 C fixture files**, representing **43,236 rows**. Their hashes and source include paths are unchanged.

Both fixture companions are linked to the exact normal/audit receipts by hash. The before/after checkpoints contain identical inputs and surround the real normal command, independent kernel replay, all-owned audit and audit readiness commands. The C source and all five output fingerprints remain identical from the normal receipt through the before-kernel snapshot and final audit receipt. The original fixture and large build-output bytes are bound by these recorded hashes; they are not copied into this lightweight evidence archive.

The recorded Git HEAD and existing dirty porcelain state are byte-identical before and after each phase. This is a preservation claim, not a claim that the worktree was clean.

## Local archive verification

`verification.tar.xz` is **122,608 bytes**, SHA256 `3f4a00c3ddab90d70a2a98b5e04713f7a3d8455d1c98a41f7f8e549c1221b73c`. Its uncompressed tar SHA256, archive-index hash, all **83 payload sizes/hashes**, and equality with the already-extracted copies were independently checked. The archive contains 84 members including `ARCHIVE_FILES.json`; its actual-result record equals `EXPORT_SUMMARY.json`.

`LOCAL_VERIFICATION.json` records the exact archive members, source and output hashes, 47 names, fixture windows, commands, platform metadata and scope. The acceptance receipt is `audits/6bd40dc2acc269011591/lane-0/VALIDATION_RESULTS.json` under the owner root, SHA256 `a6ae2cc6838baa5762c7e5c4e858febe46ff649f9b0247e6ca22d6672699ee43`.

The coordinator's cumulative archived selected-owner checkpoint at assignment is **81 owners / 1,339 owned declarations / 1,098 public declarations**. Eight additional Batch15 successes awaiting receipt export are excluded from that checkpoint. This report independently verifies only the new C contribution of **1 / 47 / 47**, and makes no whole-P1 completion claim.

This local review made no cloud call, ran no Lean/Lake/compiler/audit, changed no canonical source or existing archive, and wrote only this README and `LOCAL_VERIFICATION.json`.
