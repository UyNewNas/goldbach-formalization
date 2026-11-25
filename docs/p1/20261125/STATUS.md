# P1 continuation — 2026-11-25

## Current verified progress

Normal compilation, independent kernel replay and full environment-owned
type/axiom checks now passed for **80 distinct owners, 1,292 owned declarations
and 1,051 public declarations** in this selected continuation. These counts are
not a total for P1 and do not determine project-board node colours.

| Actual scope | Source binding | Normal + kernel + full-owned result |
| --- | --- | --- |
| 71 original Batch10 successes | `99c1f8ba1dc453b21f47e30b667db0de93d73387` | 71 owners; 1,012 owned / 803 public declarations |
| Four repaired failures | `220c14630ffd266f824bdbf0977147ecb740c0dd` | 4 owners; 165 owned / 159 public declarations |
| PrefixBinding, Harmonic and Ascending interiors | `c257b7ade3b82d8f3ae126ffb1ca999871e9cd57` | 3 owners; 47 owned / 24 public declarations |
| HistoryCore and Part3ActualWResidualCompletion | `4f7a975211bdbdccc76adc14734aa2de4a13b6ad` | 2 owners; 68 owned / 65 public declarations |
| Higher partition, included in the first row | Same original 53 source files | All 53 owners accepted |

The [Batch10](batch10-accepted-evidence/README.md),
[Batch11](batch11-accepted-evidence/README.md),
[Batch13](batch13-accepted-evidence/README.md) and
[Batch14](batch14-accepted-evidence/README.md) evidence archives were retrieved
losslessly and every indexed payload hash was verified locally. The newest
archive contains 292 payloads and the complete two-owner normal/kernel/full-owned
evidence. HistoryCore accounts for 33 owned / 33 public declarations; Residual
accounts for 35 / 32. The four accepted owner sets are disjoint. No successful
normal or complete audit was replayed to recover these results.

The additional HistoryCore and Residual fixes resolve the actual remaining
definitional-conversion failures without changing any public header, definition,
assumption or import. The original terminal source hashes remain unchanged.

## Current source candidates and execution

The remaining fourteen actual failed owners have been repaired and published at
[`95b96cb5fe1a26322b7ecbdc66f15c2775035138`](https://github.com/UyNewNas/goldbach-formalization/commit/95b96cb5fe1a26322b7ecbdc66f15c2775035138).
The [Batch15 manifest](batch15-repairs/SOURCE_UPDATES.json) binds the exact original
preimages, candidate postimages and complete group source maps. Its
[bounded caller](batch15-repairs/RUNNER.md) reuses the unchanged normal/kernel/
full-owned APIs and original runtime limits.

| Group | Actual failures addressed | Candidate scope | Current acceptance |
| --- | --- | --- | --- |
| Wire five | 33 complete target diagnostics | Five existing proofs; namespace, cast, finite maximum, indicator, integral and finite-sum expressions | Pending; job `job_a3a42ff2b1dd40b583401edafa88f480` queued |
| Ordinary five | 10 complete target diagnostics | Five existing P1 dependencies; qualification, case substitution and endpoint/rewrite expressions | Pending; job `job_f9d7db2673074fbfb706060f1beb1d4a` queued |
| Full87 interiors four | Seven actual parser errors | Only doc-comment / `set_option` placement; original literal proofs, numbers and options retained | Pending; job `job_aa7cdaaddbb7477286d7108d3eaf5003` queued |

All fourteen candidates passed bounded independent static review. The three
source-only caller checks at source95 passed with closures 271 / 365 / 219;
they provide no cloud compilation or proof acceptance. The accepted eighty
owners are not selected for replay. Actual failed logs are preserved in the
Batch14 archive; proof-expression notes are under `wire-repairs/`,
`ordinary-repairs/` and `interiors-syntax-repairs/`.

The [original G3 Data pilot](g3-data-pilot/README.md) reached the outer
3,600-second task limit without a target error or normal completion. Its exact
post-run snapshot found no .olean, .ilean, IR .c or .trace, but retained the
6,334,162-byte IR .setup.json. That file is preserved; it is not acceptance.

The [reviewed Data partition](g3-partition-review/README.md), published at
`e421f8cd5aad3d9c53933dec3c77bb530bb52f8c`, moves the identical 94 literal
block definitions into 24 flat providers and keeps the original Data facade's
remaining declarations unchanged. Reader and all 188 original fixture files
are reused. The [single-owner caller](g3-partition-execution/README.md), published
at `65d14498902b16b2b89798ed7a82f3e031dce1dc`, binds actual normal and audit
commands to immutable fixture checkpoints. The first C0000ToC0046 normal task,
`job_39badb024d0b42a2b594b396eb49936a`, has passed its exact 188-fixture / accepted
Reader / runtime precheck and entered compilation. No partition owner is yet
accepted. The facade requires complete normal and audit companions for all 24
providers. Downstream Archive's 94 `Checked` theorem declarations and original
integral conclusion remain separate obligations.

The [runtime-configuration review](runtime-configuration/README.md) preserves the
pre-existing 1,823-byte cloud lakefile and distinguishes it from the 394-byte Git
source file. No guard, serializer, configuration, heartbeat, memory or thread
limit was increased. No fixture was downloaded or regenerated.

The [U06 existing-source review](u06-reuse/README.md) also remains part of full
P1.5 scope. Its recorded source closure is incomplete, and its partial terminal
retains an explicit remainder and separate physical collision / signed-PP
obligations. Already located sources are being recovered from their exact prior
commits, without rewriting their proofs or claiming canonical acceptance.
The two [existing Nov23 U04 source variants](ordered-third-reuse/README.md) were
selected byte-for-byte earlier; their additional consumer chain remains deferred.

**P1 remains incomplete.** Original terminal acceptance, remaining numerical and
archive obligations, same-coefficient density integration, the U06 continuation
and the signed-PP boundary below are not discharged by these dependency results.

## Recovered baseline (before this continuation)

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

## Unverified source scope at the recovered baseline

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

## Execution gap at the recovered baseline

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
found in this checked passage. All 53 partition owners have now passed the
actual Lean acceptance described above without changing this normalization.

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

The initial preflight above is historical. The later 78-owner acceptance does
not remove the outstanding terminal compilation and mathematical statement
boundaries. **P1 remains incomplete.**
