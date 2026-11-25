# P1 continuation — 2026-11-25

## Recovered baseline

The newest P1 branch found was `codex/p1-final-acceptance-20261124` at
[`99c1f8ba1dc453b21f47e30b667db0de93d73387`](https://github.com/UyNewNas/goldbach-formalization/commit/99c1f8ba1dc453b21f47e30b667db0de93d73387).
The prior sequence was `e44e941d` → `184ae92e` → `99c1f8ba`.

The latest completed acceptance batch contains **12 modules, 426 environment-owned
declarations and 392 public declarations**. This is one batch, not a total for P1.
Its normal builds, independent kernel replay and full-owned type/axiom audit
are already recorded; they must not be repeated merely to recover progress.

- [Completed result](../20261124/batch9-normal-accepted-evidence/RESULT.json).
- [Original evidence archive](../20261124/batch9-normal-accepted-evidence/verification.tar.xz),
  SHA256 `2989b7a74f1a3b606ceee9152d593fab848ce7945df6a755bbc2bc35fcca4da1`.
- The archive's actual `lane-1/VALIDATION_RESULTS.json` reports
  `PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS`, 12 modules, 426 owned
  declarations, and only the standard axioms. These fields and the archive hash
  were reread in this session. No old compiler job was replayed.

## Published sources still awaiting verification

| Input | Existing published work | Acceptance at the recovered baseline |
| --- | --- | --- |
| Ordinary Batch10 | 17 repairs from actual Batch9 failures and five exact existing donor sources | New source versions uncompiled |
| Higher moments | 53 units: Core, 51 proof units, original public facade | All new owners uncompiled |
| Original P1 terminal chain | Four existing theorem files, unchanged hashes | No terminal acceptance established |
| Same-coefficient density/count extension | `P1OriginalCompleteDensityAndCount` already exists | Source candidate; acceptance not established |

The saved Batch10 cloud preflight was read-only: 96 preimages matched, 21
postimages matched, and no unknown sources were found. The 21 postimages were
unchanged files. This does **not** establish that the new sources were installed.
See [the exact source-update boundary](../20261124/batch10-source-update/README.md).

The Higher monolith's actual failure was an interpreter `lean::memory_exception`
(Lean exit 134, outer exit 1 after 813.015 seconds). Its original proofs were
partitioned, not mathematically replaced. All 53 published canonical files match
the existing partition manifest and candidate bytes; their imports respect its
build order. The failure does not exhibit a false mathematical goal.

## Missing execution step and this continuation

The baseline publishes the sources but no Batch10 execution driver. Directly
passing its ordinary manifest into the old installer is incompatible: the old
function requires `cloud_source_mutation_required`, which these 22 rows omit.
The same installer cannot create the 52 absent Higher providers because it first
reads an existing source file. A Batch10 caller must adapt the ordinary rows and
separately gate new providers by absence or exact postimage.

The continuation under `batch10-resume/` is restricted to this execution gap.
The accepted guards, serializer and full-owned audit runner remain unchanged.
In particular, an audit with one populated lane must use `--prepare-only` and
then explicitly run that lane; the old runner's default launches both lanes,
including an empty one. No completed audit12 or old Higher probe should be rerun.

Python tests and read-only source checks validate orchestration only. They are
not Lean proof acceptance. See the continuation's usage notes and test output
for its exact implemented and tested boundary.

## Manuscript and theorem scope

The reference remains the 20261106 manuscript at
[`a988cba584d803ae2856a0de50efb582f4f3dd6a`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en).
The preserved local `argument.tex`, `sieve-appendix.tex`,
`coefficient-appendix.tex`, `numerical-appendix.tex` and `analytic-appendix.tex`
were independently matched to this commit's Git blobs.

The simplex identity `num:simplex-moment` gives the normalization used in
Higher: the integral of `lambda_i * (sum y_r * lambda_r)^k` is the weighted
complete homogeneous polynomial times `k! / (k+7)!`. No normalization error was
found in this checked passage. Current Higher work is a compilation/resource
issue pending actual Lean checking.

Three statement boundaries must remain explicit:

1. `P1OriginalCompleteFormalProof.exists_complete_original_policy` combines fixed
   finite choices, the original raw bound, pointwise majorant, bounded arithmetic
   support and actual ancestor reads. Its own statement leaves compiled density
   errors and signed PP separate.
2. `P1OriginalCompleteDensityAndCount.exists_cofinal_same_policy_same_coefficient`
   assembles the same-`q`, same-coefficient physical density and finite count
   estimate. Its count bound still contains `realPhysicalDistributionError`.
   Its beta/k witnesses cannot silently be identified with another theorem's
   independently chosen witnesses.
3. Manuscript Proposition `sv:finite-realization` additionally requires signed
   PP for that same coefficient and the correct density approximation. The
   existing P3 distribution boundary is retained; passing four P1 files alone
   cannot establish this whole proposition.

Likewise, winning-branch numerical checks do not prove all-row moment/log facts,
and stronger 4/5 replay inequalities do not prove the original 3/4 parent
floor/max equality. Generic parser correctness is not actual archive acceptance.
These are distinctions between contracts, not claimed counterexamples.

The fresh static import check of the four original roots plus the density/count
extension found **2,740 project modules**, including all 53 Higher units, with
no missing project source imports. All four protected root hashes match the
baseline. [SOURCE_GRAPH_CHECK.json](SOURCE_GRAPH_CHECK.json) records the source-map
digest. This is source coverage, not compilation, kernel or axiom acceptance.

## Dashboard boundary

The live dashboard still serves the **2026-11-23** snapshot, baseline
`7f5330cace31383f5626da526b476dd4b0f43376`. Its P1 tree has 55 nodes
(8 green, 40 blue, 7 yellow), or 46 actual leaves (7 green, 37 blue, 2 yellow).
Those figures are snapshot counts; they are not a new acceptance census.
No dashboard color or completion count was changed in this session.

## Compiler connection and fresh preflight

The user-selected P1 Private Compiler 32GB `6b053c6d` initially failed at the MCP
connection probe with **HTTP 429**, including read-only calls and `pwd`.
It recovered during this session. The live environment reports a four-core
quota, 32 GiB memory limit and the pinned Lean/Mathlib versions. Its task queue
was empty when inspected.

The fresh cloud inspection used the actual project `/workspace/blue-member-build`,
source repository `/workspace/goldbach-formalization` and existing evidence root
`/workspace/p1-complete-proof/20261124-resume`. All **75** Batch10 inputs matched
their expected preimages, none matched a changed postimage, and no unknown source
or existing target `.olean` was found. All eight Higher dependency source hashes
and the four original roots matched. The live audit12 receipt is byte-identical
to the published accepted receipt. See [CLOUD_PREFLIGHT.json](CLOUD_PREFLIGHT.json).
The source repository's dirty worktree and original HEAD were preserved.

This preflight made no project source change and invoked no Lean or Lake command.
Compilation and kernel acceptance must be reported separately from these checks.

**P1 remains incomplete.** The outstanding compiler execution and the separate
mathematical statement boundaries above are not removed by source publication.
