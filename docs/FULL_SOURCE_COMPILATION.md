# Compilation-scope inventory

Exact source commit: `368736567624353986efd3b6d6c5ccef97e8b535`.
Read-only, no Lean/lake/build/checker invocation. All source/import/hash data read from Git blobs at that SHA, not mutable worktree content. Nested block comments and line comments removed before import extraction. No AGENTS.md or repository .agents skills were found.

## Counts and scopes

- 1,646 tracked `.lean` files total.
- 1,339 inside `ImbalancedChen/`, plus `ImbalancedChen.lean`: 1,340 library modules.
- 306 other Lean files: verification programs and historical/archive/third-party source copies, not additional production library modules.
- Root has 277 direct imports; its local transitive closure contains 292 modules including root.
- `UncompiledContinuation` has 586 direct imports; closure contains 1,210 including itself.
- Their overlap is 254; union 1,248. Therefore 92 library modules are outside both.
- Batch4 source manifest contains exactly 711 unique paths. Every path exists and every SHA-256 matches the exact committed blob. Its closure contains 1,218 modules.
- No missing local ImbalancedChen imports were found, even when inspecting all 1,646 Lean files. The production local import graph is acyclic. This does not check installed third-party dependencies or Lean elaboration.

## Submitted sources missed by the continuation entrypoint

Eight of the 711 manifest modules are outside both root and continuation closures:

1. `ImbalancedChen.P2AdoptedRowsActualEnclosure`
2. `ImbalancedChen.Part5OriginalOmegaGridCore`
3. `ImbalancedChen.Part5SavedParent394700Buchstab`
4. `ImbalancedChen.Part5SavedParent394700BuchstabAll32Segmented`
5. `ImbalancedChen.UncompiledContinuationV2`
6. `ImbalancedChen.UncompiledContinuationV3`
7. `ImbalancedChen.UncompiledContinuationV4`
8. `ImbalancedChen.UncompiledContinuationV5`

The first is byte-identical to `ImbalancedChen.Certificates.P2AdoptedRowsActualEnclosure`. Compile these module paths independently: importing every source into one new umbrella risks duplicate declarations and changes import-environment semantics.

## ROOT266 is not the repository root import closure

The 266-module census is preserved at:
`docs/evidence/owned-frontiers/20261024-after260-next6-v1/p/026-e8c0e21cd551fef4610e1f2214fa1c68f83f35cdf64d4dff525fa8f31e62b544.raw`.

Its 266 keys are historical owned-module accounting, not root import coverage. Only 28 occur in root closure. 201 occur in continuation closure. 65 occur outside BOTH. Their dependency closure contains 381 local modules. The census itself retains candidate/pending acceptance labels; this inventory does not independently promote its proof status.

All 711 submitted modules plus all 266 census modules plus repository root reach 1,321 library modules, leaving 19 legacy library modules outside. Thus even checking all submitted sources and historical accepted accounting is not equivalent to checking all repository library sources.

## Recommended exact build coverage

For narrow latest submitted checkpoint: explicitly build all 711 manifest module targets, or continuation plus the eight uncovered submitted module targets. Preserve separate existing root regression/audit gates. Combined root + submitted coverage is 1,256 library modules.

For user's broad “all submitted content” with robust repository regression coverage: explicitly name all 1,340 tracked production library modules as independent Lake targets. This avoids silently dropping legacy modules and does not make conflicting historical definitions coexist in one new import environment. A smaller equivalent import coverage set is root + continuation + the 92 modules outside their union. Build coverage must be recorded per actual target and failures must not be silently excluded.

Do not replace the existing root or merge every file into one aggregate. Do not treat archive-copy elaboration as production proof acceptance. Historical `.raw` payloads and source snapshots are immutable evidence, not live modules to rewrite. Continue existing verification/audit programs according to their runner scripts and pinned runtime requirements.

## Archive and duplicate classification

The 306 nonlibrary files break down as:
- 141 in `verification/proof-continuation/2026-10-15`: 140 historical audit sources, one tool.
- 120 in `verification/parts/p0`: 69 round3, 40 round4, 9 top-level audit programs, one queue template, one round5 historical producer audit.
- 5 in `docs/evidence/external-native-pnt`: external Lean/tool/source-context snapshots.
- 40 elsewhere under verification, including current audit tools and historical compilation attempts.

There are 50 exact-byte duplicate groups among all Lean files. One group has two production module paths (the P2 enclosure pair above); most other duplicates are production modules repeated in ledger snapshots or audit snapshots. Full groups, every external path, every module's imports/hash/size, and complete closure lists are in the JSON.

## Reproducible inventory CLI

Run `python3 verification/full_source_inventory.py --output inventory.json` to
record every tracked file's disposition, current SHA-256, size, and existence.
Lean records additionally include parsed imports, production module identity,
root/continuation reachability, batch711 membership, and census266 membership.
Untracked files are intentionally not described as submitted content.

Use `--revision 368736567624353986efd3b6d6c5ccef97e8b535` to read the original
checkpoint directly from Git, independent of later worktree repairs. Without
`--revision`, the report reads current tracked worktree bytes, including edits.
`--targets` prints all production module targets, one per line, for independent
build scheduling. It never runs Lean, creates an umbrella, or alters sources.

`changed_batch_hashes` records original/current hashes explicitly. Changes are
expected during repairs and do not fail inventory generation. Missing submitted
paths or missing local imports return a nonzero exit status. Neither an inventory
pass nor a matching hash is evidence of elaboration, kernel checking, or proof
acceptance. The manifest and historical census remain provenance, not new proof
claims. JSON records every tracked non-Lean file as well as all 306 external Lean
files; historical failure probes and archived snapshots are not automatically
compiled. Current verification programs must use their documented runners.

Run stdlib tests with:
`python3 -m unittest discover -s verification -p test_full_source_inventory.py -v`.

This is a provisional source scope document, not a compilation success receipt.
The initial inventory was read-only and did not invoke a compiler.

## Diagnostic builds and cache reuse

A failed source build remains failed. Optional Lake caching may retain a coherent
partial `.lake` directory only after the final runtime audit, official Mathlib
cache retrieval, source inventory and diagnostic artifact retention all succeed,
and only when the run has not been cancelled. The existing pinned cache key and
restore scope are unchanged. Lake checks source/dependency/options traces on the
next full explicit-target build; failed targets do not receive successful build
traces. This avoids repeating successfully compiled dependencies while preserving
all compilation, kernel replay, axiom and type-export gates. Cache saving is
best-effort and is never a proof-acceptance receipt.

## Required-workflow concurrency

Core and variable-envelope verification retain their push, pull-request and
manual triggers and original proof gates. Their concurrency keys are now scoped
by workflow and source branch. Push and pull-request events for the same branch
share each workflow's queue, but core and VE no longer cancel each other's pending
runs. This permits up to one active core runner and one active VE runner per
branch, using the unchanged standard hosted runner. A cancelled duplicate is not
a successful verification; final acceptance requires successful exact-head
results for both workflows.

## Intended-name resolution correction

`OriginalNodeArraysV1/Block04FullCheck.lean` originally used the unqualified
`integerInitial` in `block04_first_delayed_read_is_prefix` without opening its
namespace. Lean's `autoImplicit` therefore introduced an arbitrary implicit
`integerInitial : OriginalNode`; the accidental elaborated claim asserted that
the fixed initialized-prefix reader equalled any node and was false.

The correction explicitly names the existing
`ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.integerInitial`, rather
than changing frozen node values or weakening a generalized mathematical claim.
This intent is established by the theorem's initialized-prefix comment and the
imported `block04_first_delayed_is_prefix` lemma in `DelayedPageTransfer.lean`.
The constant is the existing node `⟨0, 0, 2^112, 2^112⟩` from
`Part4ActualThirdOriginalStoredNodeLocalChecker.lean`.

This is an unintended-name-resolution repair, not merely a proof-body edit.
An explicit full-type regression beside the theorem rejects an extra implicit
node binder. Compilation of this correction and the final complete-source run
must still be recorded; this explanation does not itself assert acceptance.

## Certificate elaboration memory

`Block20FullCheck`, `Block21FullCheck`, `Block27FullCheck`, `Block29FullCheck`,
and `Block31FullCheck` through `Block39FullCheck` exceeded the 6,144 MiB limit while
independent theorem/kernel-check tasks overlapped inside one compiler process.
Each file now sets `Elab.async false`, retaining every original theorem body,
`decide +kernel` check, frozen literal, trust level and compiler memory/thread
limit. All thirteen files passed focused guarded compilation with this scheduling-only
change. Other modules and toolchain wrappers are unchanged by this repair.

`Block31FullCheck` also referenced a nonexistent aggregation lemma. Its final
proof now invokes the already imported `readCheckBlock_of_64_pages`, whose
premise is the same 64 proved pages and conclusion the unchanged 4,096-row
check. No page check, range or frozen certificate data changed.

## Sequential CI completion plan

The first diagnostic GitHub run
[40093507664](https://github.com/UyNewNas/goldbach-formalization/actions/runs/40093507664)
reached the 240-minute build limit. Corrected event parsing identifies 399
production successes, 46 production failures and one dependency failure; the
remaining targets were not fully established. Its runtime audit and evidence
retention passed, but subsequent proof gates were skipped. Four of the five
original memory failures passed there; the external
`LiLiuGoldbachOnePlusOneNineFinite` still exceeded 6,144 MiB, although it passed
locally. Thirty-five original node full-check modules also exceeded that CI
budget. Local success is therefore not substituted for final GitHub acceptance.

CI now prepares four strictly sequential, dependency-ordered compilation shards
on unchanged standard hosted runners. The planner derives the current target
set and validates a deterministic disjoint partition, with every local dependency
in the same or an earlier shard. For the original inventory this is four groups
of 335 targets and 3,825 local dependency edges. Counts are derived, not hardcoded;
umbrella modules follow their dependencies. Simple count-balanced topological
cuts clustered all 32 original SavedParent rows into shard 1 and all 40 original
node FullCheck blocks into shard 4. The planner now derives those two heavy
families from the current graph and assigns deterministic release waves. Each
wave prioritizes its reserved targets' prerequisite closure, then fills with
ready ordinary work; future reserved targets and their consumers cannot run early.
On the current graph each shard has 8 original rows, 10 FullCheck blocks and 335
total targets. Added/removed family members are discovered dynamically. An earlier
wave depending on a later reserved heavy target fails closed for policy review.
Family membership is an unmeasured cost proxy, not a runtime estimate or guarantee;
Row31's observed long run does not establish equal timings for the other rows.
A shard may exceed the target-count quota to finish required prerequisites.
All original targets remain disjoint and exhaustive, and every local dependency
precedes its importer. A timed-out shard remains failed; an audited
partial cache may accelerate a retry but cannot satisfy the completion receipt.

Successful stages hand off cumulative project, goldbach-dependency and
LeanArchitect build outputs plus exact-head provenance receipts. Official
Mathlib retrieval establishes pinned package sources before those outputs are
restored; large reproducible Mathlib artifacts are not copied into every staged
cache. The first shard may reuse the previous full Lake cache or a prior-head staged
cache with the same guard and pins as a seed; source/dependency traces and
current-head receipts must still be revalidated. Cache
keys bind platform, toolchain/manifest, guard, exact source head and shard.
Completed-cache availability and exact matches are checked explicitly. Missing
cache space or handoff fails the staging job rather than silently starting an
unbounded cold rebuild. A compressed streaming size estimate reserves another
2 GiB for archive activity without writing a preliminary archive.

Receipts require the successful selected-target report, unchanged source hashes,
fixed guard and pins, a successful runtime audit and matching real compiler
binary hashes. They explicitly assert compilation/cache provenance only. Each
shard also recompiles one actual requested source to a temporary output under
the guard, even when all Lake targets were valid cached results. This extra check
is not a replacement for the full shard target list. The final job compares all
four receipts against its own source inventory and runtime, restores the exact
completed fourth-shard cache, and runs the explicit **entire target set** again.

The original `lean` job/check and every root kernel, axiom and type-export gate
remain. Failed or skipped staging causes that original check to run and fail
explicitly, not become a misleading skipped check. Only successful final exact-
head CI constitutes the requested acceptance; staged caches and VE success alone
do not. One core shard runs at a time; the independent VE workflow can still run
on its own unchanged standard runner.

The guarded compiler now fixes `-DElab.async=false` in addition to trust level 0,
two threads and the selected memory budget. The pinned Lean sources select the
synchronous elaborator and the same kernel declaration checker with this option;
this changes scheduling, not mathematical checking. Conflicting CLI options and
guard/state/environment tampering are rejected. Source code could explicitly
change this scheduling option; no such `Elab.async true` override was found in
the scanned production, verification or installed dependency sources. Final CI
must validate that the resource correction actually succeeds on its runners.

Build commands have internal process-group timeouts inside the stage recorder,
so a failure still produces timing and exit receipts. Absolute build deadlines
reserve time within the 360-minute job limit: warm shards stop building by minute
290 (at most 270 minutes for the command), and final validation by minute 200
(at most 180 minutes for the cached all-target command). Original final proof-gate
timeouts are unchanged. Runtime audits are independently bounded to 10 minutes,
with artifact retention following on failure. These are failure boundaries, not
permission to skip a target or proof gate and claim success.

## Explicit nonproduction outcomes

All 306 nonproduction Lean files remain individually accounted for: 5 external
evidence files, 251 historical verification/evidence files, 49 documented-runner
verification programs, and 1 template. Production build reports preserve each
file's disposition and mark `run_status=not_run_nonproduction`,
`compiled_by_this_build=false`, with the disposition as `build_reason`. Their
legacy `build_status=not_a_production_build_target` remains for consumers. These
fields mean this production build did not run them; separately executed existing
verification gates retain their own evidence and are not overridden. No aggregate
production-success flag asserts these 306 files compiled.

## Fresh rebuild authorized 2026-10-26

The earlier unpublished cloud checkout and its validation artifacts are not
available in the current execution environment. This rebuild starts from the
actual PR6 head `8d0dda4d59368402340556f8e5094414e6aad5fa`, not from a
reconstructed or recovered `23a83db` checkout. Historical success summaries
are not acceptance evidence for these new sources; all validation must be rerun.
The official scope remains 1,340 production targets with pinned dependencies,
trust0, the6,144MiB compiler budget and serialized compiler slots. Existing
proof gates and missing18 unavailable local files retain their scope boundaries.

The user explicitly approved (1) correcting the eight KL declarations from
analytic order to the intended C-infinity order, with full-type and downstream
checks and explicit statement-change disclosure; (2) restoring the omitted
positivity premise to the two StrictGram positive-definiteness theorems and
checking their callers; and (3) publishing current-task repairs/tests/config/docs
to the existing draft PR6 branch, updating its description and following CI,
without merging. The user then chose direct rebuilding from GitHub. These
approved contract changes are not described as proof-body-only repairs.

This initial checkpoint records the rebuild plan only: no new Lean compilation
or mathematical completion is claimed. The general missing Buchstab theorem
is not supplied or assumed, and TaggedRowDecoder resource failure remains an
honest outstanding issue. Meaningful subsequent milestones will be published
incrementally and separately backed up rather than retained only in ephemeral
storage. Exact-head CI results will be distinguished from local focused checks.

### Rebuild preparation checkpoint (new evidence only)

Eight KL declarations now explicitly use `((⊤ : ENat) : WithTop ENat)`;
the two approved StrictGram theorems explicitly retain `hq`. Full `@theorem`
type ascriptions accompany these proposed statement corrections. They have
not yet passed fresh Lean compilation. Ten analogous omitted premises in
`Part3ActualKGramInverseCoercive` remain unmodified pending separate approval.
Four stale imports are redirected to their actual pinned modules without
changing declarations. No mathematical completion is inferred from these edits.

The rebuilt runtime policy records project `Elab.async=false` in Lake options
(and therefore traces), while preserving verified native dependency scheduling.
This is necessary because pinned Lean setup-file options override command-line
options. Exact source allowlists, dependency bytes/config hashes, setup-file
hashes/effective options and registered probe paths are checked; unknown or
redirected source paths fail closed. Trust0, two threads,6,144MiB and the serial
compiler lock remain. Strict receipts additionally require actual project source
commands and matching scope hashes/policy across audit, state and final runner.

Dependency preparation is git-only at manifest pins. A new fail-closed verifier
resolves the production import closure, verifies Wu research source Git blobs
and stages only missing identical package-root copies. The first fresh audit
staged707 copies, found no unresolved import/cycle, and left tracked dependency
files unchanged. Source hashes and per-copy provenance are recorded, not inferred
from an earlier workspace. A tracked bounded build runner preserves actual
return codes, per-source timeout events and terminal versus interrupted state.

Fresh Python preparation tests:34 source/receipt/partition/workflow tests,
17 source-staging tests and11 bounded-runner tests pass; runtime-guard tests are
recorded separately. These are infrastructure tests, NOT Lean-source acceptance.

The user subsequently supplied a source handoff for18 formerly unavailable
files and an external three-file Buchstab proof candidate. The18 named files
are now additively integrated from their verified latest published commit
`a216a1a6f4d5febafef2280df63449dc5dee209d`, without merging that branch.
The original ZIP is historical evidence:17/18 snapshots match first publication
and16/18 match the chosen latest versions. The two version differences and all
source hashes are recorded in
`docs/evidence/rebuild-20261026/handoff18-source-manifest.json`.
The current586-import continuation is preserved with exactly18 added imports
(604 total); neither the historical603-import nor latest1472-import entry was
copied wholesale. Official production scope is now explicitly **1,358** targets,
retaining all earlier1,340 plus the newly supplied18; this expansion is not a
claim that any new source compiles. These18 are not yesterday's batch-external
repair count. Dependency pins remain unchanged.

The external three-file Buchstab candidate is not yet integrated. Its existence
does not establish theorem acceptance until exact bytes, applicable range and
transitive axioms pass isolated guarded checks. No prior missing-theorem blocker
is silently promoted to solved merely because source code was supplied.

### Actual Lake option-name correction

The first new VE run exposed a real configuration bug: quoted TOML
`"Elab.async"` was one escaped Lean name component (`«Elab.async»`), not the
registered dotted option. It is corrected to unquoted `Elab.async = false`;
the guard validates the nested TOML representation and regression tests reject
the quoted form. Runtime03 was rebuilt from the changed config/guard rather
than treating runtime02 as unchanged. The earlier evidence is preserved.

A real guarded Lake build of
`ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore` now exits0;
its generated setup JSON explicitly contains `"Elab.async": false`. The
post-run runtime audit passes with one genuine project-source command. This
single-source scheduling smoke does not establish KL/StrictGram or all1,358
compilation. Full guard tests now18; the original failed VE run remains a
failed historical CI result, pending a new exact-head run.
