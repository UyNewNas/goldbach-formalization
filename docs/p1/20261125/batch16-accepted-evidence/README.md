# Batch16: two expression repairs accepted

Both selected owners at published source commit `9ea714790c06b2270f2028555d9ba774b152d536` passed actual normal compilation, independent `leanchecker`, and a complete environment-owned type/axiom audit. The archive supports **2 accepted owners, 50 owned declarations and 46 public declarations**. It does not accept the terminal P1 roots.

| Owner | Source SHA256 | Normal seconds | Kernel seconds | Owned / public |
|---|---|---:|---:|---:|
| `P1ActualVariableFifthPositiveCellLimit` | `253b929b8122ac916877afd4d04561c9b04f211d1242af57f90ba31981f822c1` | 16.050141395000537 | 11.994668584000465 | 26 / 23 |
| `P2OriginalAdaptiveSourceSplit` | `20b6c83c8dd52b05557fbcee9610536cb8c301fece24fc57ff462c72b468ead2` | 7.05297009700007 | 9.994672673001332 | 24 / 23 |

The actual task `job_2648123a71ca4576969dd4837a0c296a` succeeded with exit 0 in **97.24971866607666 seconds**, with recorded peak memory **7,445,626,880 bytes**. The joint full-owned audit took **8.919767831997888 seconds**. The one 6,479-byte output page was independently checked against its base64 bytes, offsets and untruncated EOF. All checked normal, kernel and audit command times lie within the real task interval. [Evidence: `LOCAL_VERIFICATION.json`, `platform_status`, `platform_output` and `per_owner`.]

## Archive and source bindings

`verification.tar.xz` has 132,300 bytes and SHA256 `a8eaef6ab4c09a3836c5e6cf4c56733531103e68403da4218b663f64f55d2e6d`. This review independently verified the compressed and uncompressed hashes, index digest, every one of the **80 payload** sizes/hashes, and equality of all extracted files with their archived bytes. The index is the 81st archive member.

All **269 project-source hashes** were checked against exact Git blobs at the published source commit. Recomputing the actual import graph gives owner closures of 248 and 37 sources, whose union is exactly the bound 269-source map. Neither selected owner imports the other. The map agrees with the plan, actual source record, audit source binding and both normal dependency contexts. Its canonical SHA256 is `987c96a70b7a26d4c25105f384e660953c1f5a5fefd82a020e9ea41b5522f4af`. These dependency bindings do not count as additional full-owned acceptances.

The executed caller matches both the archived bootstrap and the published caller bytes. All 11 archived input/configuration payloads match their pinned Git sources. The source configuration and existing runtime configuration remain separately bound, including the established runtime `lakefile.toml`, guard, serializer and state files. [Evidence: `LOCAL_VERIFICATION.json`, `archive`, `source_graph` and `configuration_and_tooling`.]

## Normal, kernel and full-owned evidence

Each normal log contains exactly its selected owner's successful build header and no other newly built project owner. Each normal receipt is linked to its exact command and log. Before compiling the repaired source, both target readiness probes returned exit 3; the subsequent actual normal commands returned exit 0. Those preliminary readiness holds are not failed proof results.

For each owner, the six recorded facets—source, `.olean`, `.ilean`, generated `.c`, `.setup.json` and `.trace`—are identical in the normal receipt, pre-kernel snapshot and final acceptance receipt. The audit reused those successful normals without another normal build. The archive preserves exact size/hash metadata for these output files; it does not contain the large object payloads.

The executed auditor enumerated the full environment-owned declaration inventory, including private/generated declarations. The **50 unique inventory names exactly equal the 50 emitted records and `OWNED_EXPORTS.json`**, with 34 theorems and 16 definitions. All type and expression representations are present without elisions. All transitive axioms belong to `propext`, `Classical.choice` and `Quot.sound`; the executed audit also rejects unsafe and axiom declarations. The independent per-owner kernel checks and both no-build readiness checks returned exit 0. Lane 1 remained empty. [Evidence: `LOCAL_VERIFICATION.json`, `normal_and_audit`.]

## Preservation and distinct-owner totals

The two exact earlier source preimages were backed up before installing only the two authorized repairs in the build workspace. The Git repository's HEAD and dirty porcelain status are identical before and after the task; the bootstrap snapshots agree. This is preservation of an existing dirty worktree, not a claim that no build-workspace source changed. The four protected terminal-root source hashes remain unchanged. Normal execution and all verification ran within the existing serialized validation lane.

The peer-verified historical receipt catalog was reused from `../batch15-accepted-evidence/LOCAL_VERIFICATION.json` and its exact module sets were checked for intersections. These two owners are disjoint from the earlier **80 ordinary owners**, the **one G3 C owner**, and the **12 accepted Batch15 owners**. The selected archived totals are therefore:

`(80, 1292, 1051) + (1, 47, 47) + (12, 392, 213) + (2, 50, 46) = (95 owners, 1781 owned, 1357 public)`.

This total covers the selected continuation receipts only. The normal/source graph does not establish all dependency theorem contracts or whole-P1 completion. Earlier archives and proofs were not replayed. This local review invoked no compiler or cloud task and changed no source, archive, runtime, guard or resource settings. [Evidence: `LOCAL_VERIFICATION.json`, `git_preservation`, `source_installation`, `serialization` and `deduplication_and_selected_totals`.]
