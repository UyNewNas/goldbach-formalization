# Targeted recovery of OriginalMediumPhysicalE3Block

Date: 2026-11-26. Repository observed at `b945f39a1e355ff4fcca9865ab59ffc97f2172c0`.

## Result

**No exact source was recovered in this bounded local search. No same-name alternate version was found.** No proof was implemented, no source was synthesized or installed, and no acceptance or compilation credit is claimed. All work products are confined to this evidence directory. No cloud command, remote fetch, shared Git mutation, or GitHub write was performed.

This is a new single-target lookup. `Part3OriginalMediumPhysicalE3Block` is absent from the prior 59-name / 55-digest missing-source target set. The old scan was not rerun: existing path indexes, object stores, archive manifests, and extracted bundle stores were reused for the new name and hash only.

## Exact identity

| Field | Recorded value |
|---|---|
| Module | `ImbalancedChen.Part3OriginalMediumPhysicalE3Block` |
| Installation path | `ImbalancedChen/Part3OriginalMediumPhysicalE3Block.lean` |
| Original supplier path | `.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Phase-Sol6/Part3OriginalMediumPhysicalE3Block.lean` |
| Bytes | **6566** |
| SHA-256 | `1ed9fec9d526f866fff9a29f9d8d0fa96d63def2a8b1e4e7a42ad759a8989982` |
| Required existing namespace | `OriginalMediumPhysicalE3Block.FixedBlock` |
| Direct project import | `ImbalancedChen.Part3DistributionTargets` |
| Mathlib imports | `Mathlib.Analysis.Complex.Exponential`, `Mathlib.Data.ZMod.Basic`, `Mathlib.Tactic` |

Four checked registries agree on the bytes, digest, and original supplier path:

- `docs/source-only/20261028-resume-30f/medium_poisson/REGISTRY.json`
- `docs/source-only/20261102-resume-30h/medium_poisson/REGISTRY.json`
- `docs/source-only/20261102-resume-30j/s3_cauchy/REGISTRY.json` (target record starts at line 179)
- `docs/source-only/20261102-resume-30k/s3_mask_abel/REGISTRY.json` (digest at line 443)

The final registry also records this exact author-machine path:

`E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation\.lake\proof-continuation\source-reviews\drafts\20261028-Medium-Phase-Sol6\Part3OriginalMediumPhysicalE3Block.lean`

Those registry entries are source-location evidence, not the source itself. In particular, a different module with a similar name or a replacement `FixedBlock` structure cannot establish recovery of this original contract.

## Search bounds and observations

### Local source and working directories

First searched the exact basename, including hidden and ignored files, in `/workspace/scratch`, `/workspace/projects`, `/workspace/worktrees`, `/workspace/library-files/p34-proof-work`, and `/workspace/library-files/p34-evidence-staging`. No matching path was found.

Then enumerated the same roots and stat-filtered **265,846 file paths**. Only the **33 files of exactly 6566 bytes** were hashed as differently named source candidates. None had the required SHA-256. There were no read errors in that completed pass. Dependency/build/runtime directories and Git internals were excluded from this ordinary-file pass; the exact glob exclusions and each candidate digest are retained in `local-size-hash.json`.

The Lean files sharing the size were copies of `PanProductLiuBridge.lean` and `Part3MediumPrimitivePsiSource.lean`. They have different names and different digests. They are unrelated size candidates, not alternate recovered versions or acceptable substitutes.

### Existing Git object stores

Used `git cat-file --batch-all-objects --batch-check` read-only, with `GIT_NO_LAZY_FETCH=1`. Only resident blobs of size 6566 were read and hashed. Counts below are per store and overlap; they must not be added as unique-object coverage.

| Existing store | Resident objects observed | 6566-byte candidate blobs | Exact matches |
|---|---:|---:|---:|
| `/workspace/library-files/p34-proof-work/.git` | 19,127 | 2 | 0 |
| `/workspace/scratch/e4b706aea1e3/goldbach-p31/.git` | 2,106 | 1 | 0 |
| `/workspace/scratch/dcb7c80f70a4/p34-historical/history.git` | 30,964 | 0 | 0 |
| `/workspace/scratch/dcb7c80f70a4/p34-historical/rebuild01.git` | 11,044 | 1 | 0 |
| `/workspace/scratch/dcb7c80f70a4/p34-historical/other-bundles.git` | 263 | 0 | 0 |
| `/workspace/scratch/dcb7c80f70a4/p34-delta/new.git` | 34,021 | 0 | 0 |
| `/workspace/scratch/dcb7c80f70a4/p34-delta/blobs.git` | 724 | 0 | 0 |

`history.git` and `new.git` are partial/promisor repositories. This byte check covers objects actually resident at the time; it does not claim to hash unloaded promised blobs. No lazy fetch was allowed.

Reused `path-history-all.txt`, `raw-history.txt`, and `p34-delta/new-history.txt` for exact target-name lookup. None contains the basename. The captured old historical corpus represents the previously recorded 468 branch heads and 3,484 reachable commits; no new branch-wide history scan was run. Fingerprints of the reused index files are recorded in `source-identity-and-scope.json`.

Read-only path-history queries in the main P3.4 store, P3.1 store, and rebuild01 store produced no same-name history. The newly supplied P3.1 tip `5b9a6548bf2cd18f48b2858a881701b033b6f722` has 593 tracked paths and the P3.5 tip `ce38b7e8a5a2e7d501afe3a0213e08641dfbc777` has 638; neither tree has a target-named path.

### Existing source archives and bundle payloads

Reused the prior 20-file backup inventory. **Seventeen resident archive files** were freshly checked against their recorded outer SHA-256 and their supported members inspected for this target. The checked files are the Nov 5 v1/v37/v38 artifacts, `dot-handoff-20261026.zip`, and rebuild02–14 standalone archives. The two rebuild10 split ZIP volumes were not decoded again because the identical standalone tar.gz is present and was checked. The outer rebuild01 tar.gz is no longer resident; its retained extracted `rebuild01.bundle` and existing 11,044-object Git store supplied the source-object search instead.

Using the existing historical path index and existing main/bundle object-path inventories, identified **1,435 unique candidate archive/encoded/raw Git blobs**. **1,434 were resident and inspected**, without fetching the other object. Raw source candidates were size-filtered before hashing; compressed archive members were selected by name and uncompressed size, with nested supported containers decoded as needed.

Combined archive-member work inspected:

- **11,344 tar members**;
- **1,133 ZIP members**;
- **473 gzip decodes**;
- **11 base64 decodes**;
- **1,942 selected payload streams**, including top-level containers.

These are work counters with possible duplicate content, not unique-source counts. There were **zero target-named members, zero original-digest matches, and no read/decode errors**. Bundle members were linked to the already unpacked object stores instead of re-importing packs. Full outer identities, Git object IDs, source paths, container counts, and member boundaries are retained in `archive-targeted-results.json`.

The one nonresident indexed object is:

| Field | Value |
|---|---|
| Blob | `518b8c575232e0b702e8e985c30a7ff3462fae40` |
| Recorded commit | `e008ae002d4cec5f01b127a11dbb13016be38c97` |
| Path | `docs/verification/20261125-p2-resume/reused-owner-repairs/SELECTED_OWNED_EXPORTS.json.xz` |
| Status | P2 export metadata by path; contents not read and no claim made about them |

This isolated metadata object is a disclosed coverage limit, not evidence that it contains the target source.

## Concrete remaining lookup

The parent task owns the P3 cloud queue. This subtask has not run or submitted cloud commands. The new exact target can be checked at the following six concrete locations:

1. `/workspace/goldbach-p3/.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Phase-Sol6/Part3OriginalMediumPhysicalE3Block.lean`
2. `/workspace/goldbach-p3/ImbalancedChen/Part3OriginalMediumPhysicalE3Block.lean`
3. `/workspace/goldbach-formalization/.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Phase-Sol6/Part3OriginalMediumPhysicalE3Block.lean`
4. `/workspace/goldbach-formalization/ImbalancedChen/Part3OriginalMediumPhysicalE3Block.lean`
5. `/workspace/p24-original-compact-20261125/.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Phase-Sol6/Part3OriginalMediumPhysicalE3Block.lean`
6. `/workspace/p24-original-compact-20261125/ImbalancedChen/Part3OriginalMediumPhysicalE3Block.lean`

If those exact paths are absent, the next bounded cloud command is a basename lookup under `/workspace`, including hidden draft directories:

```sh
rg --files --hidden --no-ignore -g '!**/.git/**' -g '*OriginalMediumPhysicalE3Block*' /workspace
```

For a differently named candidate, compare size 6566 first, then compare the registered digest. A retained `.olean`, an import line, registry entry, or source with different bytes is not a successful exact-source recovery.

If the parent elects to close the single local archive-object limit, it can retrieve the blob `518b8c575232e0b702e8e985c30a7ff3462fae40` through its existing authorized remote workflow and supply the raw bytes for this one-target decoder. No such retrieval was attempted here.

## Evidence files

- `source-identity-and-scope.json`: four registry records, registry/index fingerprints, old-target-set exclusion, and selected tip observations.
- `local-size-hash.json`: exact local search command, exclusions, all 33 size-filtered candidates, and read-error list.
- `git-size-hash.json` and `git-delta-size-hash.json`: per-store resident object counts and candidate hashes.
- `historical-archive-locations.json`: archive blob locations reused from the old raw history index.
- `archive-targeted-results.json`: archive identities, individual blob/member search bounds, missing object, and empty match/error lists.
- `targeted-archive-scan.py`: reproducible one-target archive decoder; no source construction and no remote operations.

The result is a source-location boundary only. Missing attachment bytes do not establish a manuscript proof gap, and no existing proof status changes because of this lookup.
