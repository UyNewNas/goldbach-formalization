# P2.10 numerical certificate CI plan

This workflow builds only from the authorized public repository sources. It does not export the private P2 environment, publish compiled caches to a repository, or request write permissions. The existing private prefix remains the authority for pages 0–127 (2048 rows); none of those numerical pages or blocks 00–07 is compiled or replayed here.

## Scope and execution

The branch `codex-p210-complete-20261125` triggers `.github/workflows/p210-winner9.yml` on push. Manual dispatch is also available on that branch. The root workflow has read-only contents/actions permissions. Its three jobs are bootstrap, a matrix of blocks 08–43 (`max-parallel: 20`, `fail-fast: false`), and collection. The original compile, audit, evidence exporter and audit template are used unchanged. The YAML's embedded Python only controls the finite scope, transports and hashes artifacts, checks public historical compatibility, and invokes those existing drivers.

Bootstrap restores exactly 93 public project dependencies: the 57-module closure of `P2Winner9MaterializedLogChecker` and `P2Winner9SeedArchiveChecks`, plus `P2Winner9CompleteSeedBlock08` through `43`. Three helper objects already match their historical hashes in the existing public recovery artifact; those exact members are read with HTTP Range and reused. A fourth object, `CompleteSeedTypes`, has now been recovered with ordinary Lake and is restored together with its original Lake trace and facets. Only the remaining 89 dependency objects require environment recovery. This receives no new mathematical acceptance credit and never compiles an old numerical page. Recovery processes one logical Lake module at a time with one Lean thread. At least 13 GiB of actual available memory is required; available memory is clamped by the cgroup limit. The bootstrap job has a 180-minute timeout.

The official pinned `leanprover/lean-action` installation script and the repository's Mathlib cache mechanism establish the external environment. The fixed Mathlib commit is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; the required clean baseline is `8657cfffef159185f73c6a04ae4d31c846c0d0a9`. Absolute toolchain and Mathlib paths required by the unchanged drivers are constructed on the runner. No external goldbach/MathlibNt native cache is downloaded: this numerical closure has no native owner imports. The ordinary official Mathlib cache is downloaded for its actual Mathlib imports.

## Early compatibility gate

Before any numerical shard starts, every bootstrap source, object, toolchain, direct dependency map, recursive dependency signature and closure signature must equal its already public historical binding. The complete set is required, not merely an intersection. Closure signatures are recomputed and actual source/object files are hashed by the existing audit verifier. Lean and stock leanchecker binary hashes must equal the accepted historical environment.

The 57 shared records come from `docs/verification/20261125-p2-winner9-112-127/evidence.tar.gz`, member `context/selected-compile-records.json`, bound by its public `manifest.json`. The 36 SeedBlock records come from `docs/verification/20261124-p2-private/evidence-checkpoint-20261124.slim.tar.xz`, flat member `packages/common.tar.gz/context/selected-compile-records.json`, bound by `ORIGINAL_EXPORT_MANIFEST.json`. Archive, manifest and record-member hashes are fixed in the workflow. Shared historical records must agree. A mismatch fails bootstrap and prevents all 562 pages from starting. Old receipts are never rewritten to fit a newly generated environment.

## Per-block gates

Every block restores only the same run/commit's sealed 93-module cache; its producer attempt must be no later than the current attempt. Thus re-running a failed job can retain the original successful bootstrap. It verifies its file hashes and compilation records before invoking the existing compile driver. It verifies the same shared objects afterwards and requires the compiler's started-module list to equal exactly the block's new pages plus its Check. A missing or invalid shared cache therefore fails; it is not an invitation to recompile the common dependencies.

With at least 13 GiB actually available, a block uses two independent `-j1 -M6144` processes. Between 7 and 13 GiB, it uses one. Below 7 GiB, it fails before compilation. The three acceptance gates remain distinct receipts: strict compilation; the stock `leanchecker --verbose` kernel replay; and the complete serialized/environment owned inventory with full declaration types and transitive axiom audit. The two audit workers use disjoint module sets and independent summary names. The allowed axiom boundary is unchanged (`propext`, `Classical.choice`, `Quot.sound`). The workflow does not use the uncompiled SharedScale experiment.

The exporter returning zero is insufficient: the wrapper additionally requires exactly the requested pages and Check to be accepted, no unselected/rejected candidates, no duplicate owned declarations, and every page's precise `Checked` interval. Blocks 08–42 each contribute 16 pages and 256 rows. Block 43 contributes pages 688 and 689, totaling 18 rows; page 689 contains two rows. Overall new coverage is 562 pages / 8978 rows plus 36 Check modules.

## Artifacts and integration

Each successful block includes the unchanged exporter's full source/evidence archive and manifest. Because that exporter deliberately excludes objects, a separate archive preserves all produced `.olean`, `.olean.server`, `.olean.private`, `.ir`, and `.ir.sig` facets, original compile records for the new modules, complete original per-module audit receipts and logs, full declaration inventories and types. File hashes, source commit, workflow run/attempt and the bootstrap archive hash bind every delivery. An always-run recovery step additionally preserves partial new objects, records, sources and original receipts when compilation, audit or export fails. A failed bootstrap also uploads its partial library separately from its diagnostic records/logs. This recovery material grants no acceptance credit: its saved bindings and actual files must be revalidated by the unchanged drivers before further use.

Collection requires exactly 36 successful, disjoint block artifacts from the same commit/run/bootstrap. For each block it selects the latest available successful producer attempt no later than the current attempt, so successful blocks from an earlier attempt need not run again. It verifies every delivery hash and exact row coverage again, then retains one `p210-all-new-pages-<run>-<attempt>` artifact containing all original block ZIPs, the bootstrap archive and a complete index. This artifact is an integration input, not a claim that P2.10 or the final terminal is complete. The root can download it back into the original P2 environment, verify the preserved source/object/dependency bindings, reuse the accepted old prefix, and compile/replay/audit the combined numerical and terminal modules there. Historical receipts remain byte-for-byte preserved with their original provenance.

## Known limits

Before publication, local checks parsed the YAML, all embedded Python and every shell block. The actual source plan passed against the two checked-in public archives: all 93 reference records and current dependency sources agreed, and all 36 blocks had exactly their planned new-page closure. Targeted fixtures accepted both the ordinary 256-row block and the final 18-row block, rejected missing acceptance, altered row bindings/counts and unselected/rejected candidates, and checked same-run prior-attempt bootstrap reuse versus foreign/future provenance. These checks execute no Lean compiler or kernel replay and grant no numerical acceptance credit.

The first run, [45573208806](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45573208806), successfully compiled all 93 dependency sources but failed the historical object identity gate. All numerical jobs were skipped. The 90 historical dependencies include 17 symbolic-link sources and 73 regular sources. For the symbolic links, the bare Lean frontend inferred their physical `docs/...` module names, whereas the required historical objects use logical `ImbalancedChen...` module names. The ordinary Lake setup also records the package identity for the historical dependency objects. This changes private declaration names and macro hygiene names inside expressions as well as the package extension and serialization address. Rewriting only metadata cannot restore the historical objects. The three regular-file helper objects already have the exact required hashes and are retained.

The ordinary Lake leaf probe [45582627415](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45582627415) recovered `CompleteSeedTypes` with the exact historical object SHA256 `e1245dded95daf773f6497e870eeba17a2c6fce0eae7ef9d851abd315849a5ef`. Its 175616-byte artifact `15006284106` has ZIP SHA256 `b0e03aeb5e1f55961c3e5a5e83b65fb654835989e11c05c370c813d23e73a0d0`. The producer's actual setup has the logical module name, package `imbalancedChen`, and empty options. Its eight build artifacts, including the original trace, are restored without manufacturing cache metadata or rebuilding the leaf. This establishes one recovered dependency, not the complete bootstrap or any new numerical-row acceptance.

The correction uses ordinary logical Lake builds for the missing objects, a no-build dependency preflight, and the same historical source/object/recursive-binding gate. Original helper compilation logs are restored from their hash-bound public archive. Accepted records are not rewritten to accommodate a different environment, and no binary or expression renaming is used. Any remaining compilation failure, resource failure, trace mismatch or object mismatch stops before numerical work and retains the actual logs and successful partial Lake objects/traces. No success, speedup or final 11026-row proof is claimed until actual CI evidence and final original-environment integration pass. Re-running already successful numerical jobs should be avoided; retain and inspect their existing artifacts first. Partial failed-block recovery is deliberately not an automatic resumer: inspect its preserved compiler/audit evidence before deciding which unfinished work to resume.

The next run, [45585113447](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45585113447), reused the successful SeedTypes artifacts and compiled Affine with ordinary Lake. It stopped because the Affine object still differed from the historical SHA; no numerical job ran. The actual saved object contains the runner's absolute source filename in its persistent lint log. A subsequent fixed-input diagnostic changed only that shared lint filename string to the publicly documented `/workspace/goldbach-p2/ImbalancedChen/P2AffineSimplexMomentLaw.lean`, relocating real pointer fields as required by the string length. Its complete output SHA exactly equals the historical `5d97c37e169d8c69617c89f88a5dd471134d58ca35a5137b3ce23e82b47cfc9f`. The original-filename roundtrip is byte-identical; all other object bytes and pointer targets, including mathematical declarations, are unchanged. The original Lake object, trace and sidecars remain preserved. This diagnostic is artifact identity recovery, grants no proof/replay credit, and has not yet completed the 93-module bootstrap.

## Validated import command

`verification/part2/import_winner9_ci_artifacts.py` consumes the expanded
collection artifact in the original P2 worktree. Supply the workflow run ID,
full CI source commit and index SHA256 observed at the trusted download.
`--check-only` performs all validations without installing a compiler cache.
The normal mode validates all blocks before writing new module files and
commits the merged registry last. Existing targets or receipts are never
overwritten. Run it while this cache has no other writer.

The importer calls the original snapshot, compile-record and receipt
validators, including the original audit-log/type/axiom parsing. It preserves
source commit and receipt provenance and does not compile or replay modules.
Its syntax, archive/path rejection, coverage, collision and rollback fixtures
were checked before publication; validation against actual CI output remains
a separate required step.

The importer now limits temporary disk duplication. It first validates the old
93-module local closure, streams and hashes the actual bootstrap object bytes,
and then reuses the matching local storage. Transfers use exclusive hard links
on one filesystem and verified copies only for `EXDEV`. Stage reuses the already
validated bootstrap files; each block's temporary delivery/object/export
directories are removed only after every original gate passes and no frozen
evidence path resides there. All 36 blocks still have to pass before the final
registry commit, with no-overwrite and rollback behavior retained. Fourteen
small storage fixtures, including a real cross-filesystem transfer, passed;
the original C/A/E drivers and their validation conditions remain unchanged.

The receiving job observed 1484419072 bytes free under `/workspace` and
9441329152 under `/tmp`. Place both the incoming collection and temporary staging
under `/tmp` (the CLI supports `--staging-parent`). The final destination still
needs space for the new objects, original receipts and preserved collection
archive; this must be checked against actual successful block sizes.
