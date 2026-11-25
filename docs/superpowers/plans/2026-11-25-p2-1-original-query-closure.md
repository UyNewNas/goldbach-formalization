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
- [ ] Record exact source-identical historical receipts and qualified objects available for these closures.
- [ ] Record the mathematical boundary of alternative Buchstab producers without demanding duplicate proofs.

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
