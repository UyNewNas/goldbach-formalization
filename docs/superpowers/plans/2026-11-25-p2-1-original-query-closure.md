# P2.1 original query closure implementation plan

> **For agentic workers:** Use superpowers:executing-plans for the compile/fix sequence and independent source/receipt review. User has authorized continued implementation, remote compilation, and GitHub submission.

**Goal:** Close the manuscript's P2.1 rational interval, Buchstab/Suzuki and actual public-query obligations, preserving the exact original algorithms and reporting any remaining boundary explicitly.

**Architecture:** Reuse existing source and source-identical verification evidence. Work in a separate checkout based on `work/p2-formal-proof@a929011ec95843553fc2e10b7291c8077e0952c0`; use the designated P2 private compiler. Compile only missing or changed closure members. Keep ordinary Lean compilation, stock kernel replay, owned-declaration/type/axiom audit, and external byte provenance as separate evidence.

**Tech Stack:** Lean 4.33.0-rc1; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; existing goldbach dependency `09b97db5764ade1246bfb77206baa1b124760958`.

**Spec:** User instruction in this session; 20261106 manuscript at `chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`, `paper/release-20261106/en/numerical-appendix.tex` (log enclosure and delayed/chord update), `sieve-appendix.tex` (literal-density and omega-envelope); P2.1 board snapshot and existing source interfaces.

## Global constraints

- No repeated implementation or compilation when exact adequate existing results can be reused.
- No new external theorem formalization; use existing pinned source dependencies.
- No `sorry`, `admit`, new axioms, `native_decide`, `unsafe`, or weakened target predicates.
- No mutation of other sessions' dirty worktrees or running compilation tasks.
- Historical acceptance retains its exact source, input, dependency and scope boundary.
- Do not equate P112/P160 M12 queries, historical Q80/M8 queries, or alternative Buchstab producers merely because they enclose the same analytic function.

## Review focus

- Closed interval endpoints 2 and 12, exact-grid branch, off-grid last cell, and positive integer denominators.
- Signed floor/ceiling, 112-to-160 scaling, original chord constants and delayed indices.
- Complete coverage of all 40 blocks / 163840 updates rather than a prefix.
- Matching compilation and replay context, full owned declarations and transitive axioms.
- Distinction between Lean literal recurrence equality and external historical byte provenance.

## Task 1: Reconcile scope and reuse evidence

- [x] Check current remote branch, local dirty files, private environment queue, manuscript version and board snapshot.
- [x] Locate existing roots `All40PublicQuery`, `P0RationalQueryPublicAPI`, `P2HistoricSieveStateInduction`, `P2HistoricBackendTypeAdapters`, and `P2BuchstabRationalSemantics`.
- [x] Record exact source-identical historical receipts and qualified objects available for these closures.
- [x] Record the mathematical boundary of alternative Buchstab producers without demanding duplicate proofs.

## Task 2: Compile and repair the original query closure

- [x] Reuse the existing source/dependency-bound compiler and native-cache qualification machinery.
- [x] Compile missing All40 data/check modules and public APIs; preserve any first failure as regression evidence.
- [x] Diagnose each failure against the source and manuscript, apply the smallest proof-preserving fix, and rerun the failed module plus impacted consumers.
- [x] Verify the actual Q80 backend and Buchstab interfaces to the required P2.1 boundary, reusing existing acceptance when identical.
- [x] Add a small combined public entry only if no existing module already assembles the required verified interfaces.

## Task 3: Accept and publish

- [x] Run stock `leanchecker` and complete owned/type/transitive-axiom audits for newly compiled members.
- [x] Jointly import the accepted roots under one frozen dependency context.
- [x] Save exact source hashes, commands, exit codes, inventories and an honest closure/remaining-obligation report.
- [x] Independently review changes and evidence; fix material findings and verify.
- [x] Commit and push the concrete result, then read back the remote head.

## Execution ledger

- 2026-11-25: P2 compiler currently has 16 GiB effective quota, four CPU threads and 13107 MiB per-job maximum. No active job at initial inspection. P1 compiler is busy and is not used for new compilation.
- 2026-11-25: Separate local and remote worktrees created from exact `a929011e`; other P2 worktrees retain uncommitted work. Independent Winner9 pages on `dot/p2-winner9-pages112-20261125` are outside this task.
- 2026-11-25: Historical seven-module sharp chord/literal recurrence/rational query acceptance found with matching current source hashes. Reuse it rather than reimplementing those proofs.
- Ruling: Source-only comment headers are historical labels, not proof status; current acceptance is determined from exact receipts and actual compiled closures.
- Ruling: Existing Lean theorem statements and compile failures are the regression tests for proof repairs. No duplicate test theorem is added solely to mirror a proof body.
- 2026-11-25: Source candidate published at `62c128726e05dd33c02444dd567b92f47bf1b24f`. It adds the concrete all-branch table interface and extracts unchanged generic reciprocal declarations so the Q80 branch avoids unrelated Pan/U8 dependencies. This source checkpoint is not compilation acceptance.
- 2026-11-25: First strict compilation task `893953ef8f784ae88f3a2739a6c1e93f` passed the seven original analytic/query modules and began the 40 block checks. The stored-reader composition failed at compact comparison tokens ending in `i` and the negative body after `let num`. Repair adds token separation and an explicit semicolon, preserving all formulas.
- 2026-11-25: Block00--03 and Block05 full checks passed under the initial 6144 MiB process limit; Block04/06/07 reported interpreter memory exhaustion. The next batch uses one worker with 11264 MiB, retaining the existing exact kernel checks. A resource failure is not a mathematical counterexample or proof acceptance.
- 2026-11-25: Follow-up task `0239ccc099074d5e99f6d73e8fc4a781` will fetch this branch and compile the complete all-branch, original Q80 backend and rational public API roots, reusing records that pass the source/object/dependency and native-context checks.
- 2026-11-25: Independent review checked the zero clamp, exact last node, Hhi terminal upper branch, signed numerator, positive denominator, P112-to-P160 scale, and use of actual-function monotonicity. The new `query_eq_original_all` and `public_query_encloses_all` additionally transport the all-rational result to the original public function names.
- 2026-11-25: First compilation reached Block31's final page assembly and found an unresolved local helper name. Replaced only that call with the already imported `readCheckBlock_of_64_pages`; all 64 numerical page proofs remain unchanged. Static scan found no other missing helper of this name among the 40 blocks.
- 2026-11-25: The eight-module deterministic Buchstab interval closure has no project modules in common with either the original All40 or Q80 closure. It can use a separate strictly qualified native extension without rewriting existing compilation records. The extension compiles only three existing pinned upstream Buchstab modules, grants no proof credit, and requires independent downstream kernel/axiom audits.
- 2026-11-25: Local temporary checkout disappeared during execution. Restored the exact published `1341fabf` tree to `/workspace/projects/goldbach-p21`; the remote worktree and compilation were unaffected. Recovered the only unpublished document append from its exact agent checkpoint.
- 2026-11-25: The higher-memory rerun reached the finite-state induction and reported two unclosed zero-step `Nat.rec` reductions plus an `if True` in the successor case. Added reflexivity after the existing zero-case simplifications and `ite_true` to the successor simplification. The original recurrence, invariant, table values and query endpoints are unchanged. This is an elaboration repair, pending the next actual compile.
- 2026-11-25: The same rerun passed Block06's complete numerical checks at 11264 MiB. Block04 completed its numerical pages and exposed two assembly issues: its prefix lemma used an unqualified `integerInitial` outside that definition's namespace, and the first backward rewrite by `h0` already replaced both `block00` occurrences. Qualified the intended original initializer and removed the redundant second rewrite. All 64 page statements and proof bodies are unchanged.
- 2026-11-25: Reused P2.4's existing `P2DirectedLogRounding` repair from `63fcd8691951b552078d928bb840c5eef46d0221` without byte changes. The old source exactly matches the prior CI failure at the complete-owned audit's partial-companion gate. Independent review checked unchanged imports, 22 original theorem signatures and the interval-arithmetic portion. This reuses the other workstream's repair; the new source still needs compilation, replay and the unchanged full audit. Source and preimage hashes are recorded in `SHARED_REPAIR_REUSE.json`.
- 2026-11-25: Also reused the exact `P2OriginalCompactQ80Table` provider from that P2.4 commit. Its only project import is already in this batch, so it adds one module and the distinct maximum-twelve Q80 query obligation. No compact integration tree, leaf charges or array implementation is reimplemented. No matching completed provider receipt or active provider compilation was located in the checked P1/P2 queues. `COMPACT_PROVIDER_REUSE.json` records the source identity and pending verification boundary.
- 2026-11-25: Higher-memory task `0239ccc099074d5e99f6d73e8fc4a781` finished with 110 successful project modules, reusing 82. It passed 28 additional complete block checks, including the Block31 repair; 38 of 40 full checks now have successful normal runs. It stopped after Block38 at the time budget. The two diagnosed source failures are repaired in the later published commits. Block39 and the Q80 branch were not started by this attempt. The exact full task log and metadata are retained as `attempt-002-*`.
- 2026-11-25: Buchstab task `6dc7e9d503ac4de6919e7cd4b7acce30` stopped before invoking Lean when standard-source qualification could not locate a frozen `Lake.Util.Casing` source. No extended snapshot or Buchstab proof acceptance was produced. A read-only diagnostic was queued to distinguish physical input absence from over-approximation by source-header traversal. The exact failure log is `attempt-003-compile.log`; the qualification guard remains enforced.

- 2026-11-26: Original finalization task `048eb7ed9b5141e692483cef94c6cd9d` succeeded with all 140 selected owners, 18,581 unique declarations, 26 public types and the original five-root joint probe. Both original and retained-copy archive verifiers succeeded against 1de0453b. Core original receipts are published at 5eaead58. Complete 409-part archive publication and local byte verification remain in progress; the final publication checkbox remains open.

## 2026-11-26 authorized publication and local archive verification

The user explicitly approved public release of the complete fixed evidence payload and later verification records. Push task `0e8e08b3c3254066a8cadd51cf95071e` succeeded with exit `0` in 37.71464767099678 seconds. Independent GitHub readback matched payload commit `947a5dd8fb3c32c8a2688b767f559d7ab31d46d1`, tree `14b67d3e5a4435fb02046d7d541e0d5531aff719` and parent `48b343279639cb3a289628d35cc23b2710eedd05`. Its 10,286-byte stdout is complete. The subsequent records were published at evidence-record commit [b30038ae0d5f866e01ec2d52689e8fadc6115755](https://github.com/UyNewNas/goldbach-formalization/commit/b30038ae0d5f866e01ec2d52689e8fadc6115755), tree `e94b60028986fc5b8ff9375b6f86df77d2698305`, with parent `947a5dd8fb3c32c8a2688b767f559d7ab31d46d1`. Independent GitHub commit/tree/ref readback passed; [the publication record](../../verification/20261126-p2-1/EVIDENCE_RECORD_PUBLICATION.json) preserves the actual checks. Readback of the containing code-document revision is recorded separately.

Fresh retrieval verified four transport manifests, all 409 archive parts, seven auxiliary originals and all 39 auxiliary PLAN parts. All 29 Git commands exited `0`; the complete archive is 490,564,596 bytes with SHA256 `066a46e41e34578a2adbf2a1120e8aba0470dfde44d6052bc8576d8fcb9aa212`. The unchanged local verifier then succeeded with exit `0` in 35.89830784399237 seconds against accepted commit `1de0453bee55bf1128be422787216937b8fda9c9`, checking 28,167 logical original members and 140 Git source references. See [the actual execution](../../verification/20261126-p2-1/LOCAL_ARCHIVE_EXECUTION.json) and [verification result](../../verification/20261126-p2-1/LOCAL_ARCHIVE_VERIFICATION.json).

Independent completion review passed **57 checks with no Critical or Important findings**. Its [record](../../verification/20261126-p2-1/LOCAL_COMPLETION_REVIEW.json) binds the actual push/ref/tree/parent, 29 Git-command receipts and their small I/O, four manifests, 409 part receipts, independently rehashed seven originals and 39 auxiliary PLAN parts, unchanged-verifier execution and all 140 canonical source-reference rows. One historical same-byte source path alias remains; it is not a new module. The reviewer did not reread the large archive/batch, rerun the verifier, enumerate owned names anew or execute Lean. This review checks the published immutable payload and local verification. Evidence-record publication was then independently checked and recorded separately; no readback of the containing code-document revision is asserted.

The original five-root mathematical result remains 140 selected modules, 18,581 owned and unique declarations, zero duplicates and 26 full public types. The last affected closure reused 33 of 35 normal records and rebuilt two owners. Eight historical normal-compile logs remain unavailable. Neither publication nor local archive verification runs Lean or grants additional kernel/owned-audit credit.

Preserve the original `PREPARED_ONLY` report and the earlier automatic rejection as history. The user's later approval resolved its authorization condition. Some prior raw rejection/internal-readback captures were lost; surviving hashes/reports do not recreate them, and this continuation's fresh readback is new evidence. Reproduction uses the immutable payload `947a5dd8` checkout and the local 409-part assembly plus unchanged verifier described in [P21_STATUS.md](../../verification/20261126-p2-1/P21_STATUS.md). The once-used recovery downloader required the evidence ref to equal `947a5dd8` before later record commits; it is not a generic future-branch downloader.

`full_p2_complete=false` remains unchanged. This query closure does not establish historical serialized-array identity, author Q80/4096 or N48/8192 Buchstab integer equality, adaptive trees, downstream floors or charges, all integral totals, final density constants or the manuscript's main theorem.

The code-document revision inherits baseline `48b343279639cb3a289628d35cc23b2710eedd05` and carries the lightweight reports, capsules and recovery source from fixed evidence-record commit `b30038ae0d5f866e01ec2d52689e8fadc6115755`. The archive payload remains in the [immutable payload tree](https://github.com/UyNewNas/goldbach-formalization/tree/947a5dd8fb3c32c8a2688b767f559d7ab31d46d1/docs/verification/20261126-p2-1). Its [ARCHIVE_PARTS.json](https://github.com/UyNewNas/goldbach-formalization/blob/947a5dd8fb3c32c8a2688b767f559d7ab31d46d1/docs/verification/20261126-p2-1/ARCHIVE_PARTS.json), [DIRECT_GIT_PLAN.json](https://github.com/UyNewNas/goldbach-formalization/blob/947a5dd8fb3c32c8a2688b767f559d7ab31d46d1/docs/verification/20261126-p2-1/DIRECT_GIT_PLAN.json), [LOSSLESS_ASSETS.json](https://github.com/UyNewNas/goldbach-formalization/blob/947a5dd8fb3c32c8a2688b767f559d7ab31d46d1/docs/verification/20261126-p2-1/LOSSLESS_ASSETS.json), [TRANSPORT_METHOD.json](https://github.com/UyNewNas/goldbach-formalization/blob/947a5dd8fb3c32c8a2688b767f559d7ab31d46d1/docs/verification/20261126-p2-1/TRANSPORT_METHOD.json), [original-assets/](https://github.com/UyNewNas/goldbach-formalization/tree/947a5dd8fb3c32c8a2688b767f559d7ab31d46d1/docs/verification/20261126-p2-1/original-assets) and [archive-parts/](https://github.com/UyNewNas/goldbach-formalization/tree/947a5dd8fb3c32c8a2688b767f559d7ab31d46d1/docs/verification/20261126-p2-1/archive-parts) use fixed remote links; reconstruction runs from the fixed payload checkout.
