# Existing-source recovery after P3 cloud restoration

This is a source-location report for 2026-11-25. It adds no Lean proof, compilation, kernel acceptance, or board completion credit.

## Located existing sources

The restored P3 workspace retains the existing project at `/workspace/goldbach-p3`, at commit `ef1479c272bdd6b24800fa10409d793f0a2fe95c`. The observed checkout contains 440 ordinary Lean source files and has 196 commit objects in its Git object database. The separate `/workspace/goldbach-formalization` checkout is the small default-branch tree at `28f47bbb3a2e8e4a85736a505462d3ff7a5fc522`; it is not the full P3 source collection.

During the investigation another existing worktree became visible at `/workspace/p24-original-compact-20261125`. Its observed HEAD was `85c1c7a882125785e1c56a4c099e29b2adffc8e2`, with no tracked modification. Both registered **P3.4 child-1 terminal sources** are physically present there and match the recorded bytes:

| Source path relative to that worktree | Bytes | SHA-256 |
|---|---:|---|
| `docs/source-only/20261102-resume-30r/actual_spectral_energy/Part3OriginalSignedNativeCuspFourier.lean` | 10,472 | `766d00b552b66d4467d857e9e02553fc9431410d9028276fdd491f45ec747336` |
| `docs/source-only/20261102-resume-30r/oldform_continuous/Part3OriginalPrincipalTraceRow.lean` | 7,133 | `734d59fb3b38808eb64c31843464440fbb6f22c0ded12edcbaa9c899d8550650` |

These are previously known, reusable source files. They are absent from the tracked tree at the first P3 checkout's `ef1479c` commit. Finding them in a different worktree does not recover any of the previously missing imports. The source identity and the two separate observations are recorded in [source-resolution-child1-provenance.json](source-resolution-child1-provenance.json) and [source-resolution-restored-p3-cloud.json](source-resolution-restored-p3-cloud.json).

The child-1 explicit-import union remains **250 located modules, including these two terminals; 23 missing modules; and 14 names with different-byte candidates**. These are the existing static source-discovery counts, not a fresh compiler closure. No source was overwritten or rewritten to obtain this result.

## Following the board's recorded commits

The search followed the recorded source rounds instead of relying only on current branch checkouts. All **24 representative terminal files across ten P3.4 leaves** exist at the board source baseline `7f5330cace31383f5626da526b476dd4b0f43376`, with Git blobs identical to the formalization baseline `fa22a56829ee880404516a36d498ce27dcb32f92`.

The child-1 terminal files also have identical bytes in `e2a05f73d5f169fff847d72dcfcc66ec54ad4f87` and `b2c20e789cd9026661bbc11eaae0e53fba9e94e5`. These are addition records on different history lines; neither is asserted to be the globally earliest source creation. The six-spectrum and three-measure source-round commits `53e0b471d9073d630840c41d2a4710188feffd31` and `5d022fb9a5c6149a87018cf41b688290c3f2c7e8` were also checked directly. The report retains the exact commit, path, and blob for each checked terminal.

## Search for the missing imports

The target set is unchanged: **59 unresolved module names, 54 with registered byte hashes, representing 55 distinct SHA-256 values; five modules have name references only.** Within the following checked corpus, no additional matching source was found:

| Corpus | Checked extent |
|---|---|
| Restored initial cloud repositories | Current nondependency files and named archive payloads; all 1,028 Git blobs across the two initial repositories, including objects not named by reachable trees. |
| Other visible cloud files | A later pass over 20,590 nonexcluded files, with supported archive decoding; direct basename checks in the newly visible worktree. Name-only hits were import/registry references. |
| Advertised GitHub branch history | 468 recorded branch heads; 3,484 reachable commits; 19,942 Git trees parsed for target names. |
| Historical source/archive byte delta | 7,506 selected historical blobs beyond the already checked baseline, plus supported decoded payloads. |
| Known saved source backups | 20 identified files, including rebuild01–14 artifacts and both rebuild10 volumes; 12 embedded Git bundles. All blobs in those bundle packs were checked, not only the tips. |

The rebuild01 archive has SHA-256 `418de569b101ee1f6100a3aff84d9d1d06492c024be8bf6ab596b3ff21aa03ce`. Its `rebuild01/source.bundle` has SHA-256 `8c08c98ec960bc205e00f6ee6a6343177ef5264628fffb6c48e65063aa4b6be1` and tip `cfdbcd9106428af5f3a61ebbc78b6bfb55c2f083`. All 11,044 objects in that bundle were examined by type, including 8,236 blobs. Across all twelve packs, the per-pack sums are 8,429 blobs, 2,612 trees, and 340 commits; these are **not deduplicated across packs**. The rebuild10 split ZIP was reassembled, passed its integrity check, and yielded a tar.gz identical to the separately saved original. The completed byte-scan receipts report no read/decode errors.

The original author paths recorded for missing sources include `.lake/proof-continuation/source-reviews/drafts/20261026b-FrickeNonzero/Part3ActualFrickeNonzeroFourier.lean` and the `20261028-Medium-Gevrey-PhaseB-Sol6` / `20261028-Medium-Gevrey-Hard-Sol6` directories. Some original Gevrey filenames omit the `Part3` prefix; the name checks included this variant. These are provenance leads, not claims that the files currently exist. The drafts root is absent in both initial cloud repositories.

## Evidence and limits

- [Cloud tasks and source readbacks](source-resolution-restored-p3-cloud.json) retain the successful commands, statuses, task IDs, selected output records, and exclusions.
- [Historical and backup report](source-resolution-historical-supplement.json) retains the 59-module target map, registered hashes and paths, branch tips, source-round commits, known backup identifiers and hashes, and scan results.
- [Historical reproduction archive](source-resolution-historical-reproduction.zip) contains six investigation scripts, the captured branch heads, instructions, and the independent all-tree coverage receipt.

The shared cloud filesystem changed during this investigation; task counts are separate observations and overlap. They must not be summed as a count of unique sources. The historical byte pass selects the disclosed source and archive types and only decodes supported formats. It does not claim to inspect every possible opaque wrapper. For the five modules with no registered hash, arbitrary renamed definitions cannot be certified by byte identity.

Unpushed author working directories, private or unadvertised refs, PR-only histories not reachable from the captured branches, and backups outside the identified corpus remain unverified. **The 23 child-1 missing imports and the 59-module union remain unresolved in this bounded search.** A missing attachment is not evidence of a manuscript proof gap, and source presence alone is not proof acceptance. The seven-module acceptance at `3b3aa92475d0d6ab12a0652cc6cf2561afb99ac7` is unchanged.
