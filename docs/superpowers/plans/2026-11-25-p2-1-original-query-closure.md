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

- [ ] Reuse the existing source/dependency-bound compiler and native-cache qualification machinery.
- [ ] Compile missing All40 data/check modules and public APIs; preserve any first failure as regression evidence.
- [ ] Diagnose each failure against the source and manuscript, apply the smallest proof-preserving fix, and rerun the failed module plus impacted consumers.
- [ ] Verify the actual Q80 backend and Buchstab interfaces to the required P2.1 boundary, reusing existing acceptance when identical.
- [ ] Add a small combined public entry only if no existing module already assembles the required verified interfaces.

## Task 3: Accept and publish

- [ ] Run stock `leanchecker` and complete owned/type/transitive-axiom audits for newly compiled members.
- [ ] Jointly import the accepted roots under one frozen dependency context.
- [ ] Save exact source hashes, commands, exit codes, inventories and an honest closure/remaining-obligation report.
- [ ] Independently review changes and evidence; fix material findings and verify.
- [ ] Commit and push the concrete result, then read back the remote head.

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
