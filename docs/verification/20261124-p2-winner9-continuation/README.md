# P2 Winner9 continuation — 2026-11-24

## Acceptance boundary

> This is the earlier public-environment checkpoint. The subsequent private-environment results are recorded in [20261124-p2-private](../20261124-p2-private/README.md). Its historical pending counts and service blocker do not describe the current private worker.

This checkpoint continues `work/p2-formal-proof@8657cfffef159185f73c6a04ae4d31c846c0d0a9` against the 20261106 manuscript. **P2 is not complete. The full 11,026-row Winner9 integral bound is not accepted by this checkpoint.**

The prior six-row lower bound and its source are unchanged. This round strictly compiled **50 new geometry modules**, including the generic complete-archive interface, the order-composition lemma, all 44 witness data blocks, their lookup/interface modules, and the first and last block checkers. New independent `leanchecker` replay and transitive axiom audit could not be scheduled before the service reached its retained-job limit.

[VERIFICATION_RESULTS.json](VERIFICATION_RESULTS.json) gives exact source hashes, job IDs, per-module results, failed attempts, and pending source paths. All logs in [cloud-jobs](cloud-jobs) are actual captured cloud output; their JSON companions retain the exact stdout text and hash, while readable .log files normalize trailing blank lines. The listed source hashes describe the local checkpoint bytes supplied to those jobs. The cloud source/object/signature records remain in `restore-records.json` and could not be exported after the service limit; consequently the repository alone does not yet provide an independent exact-object provenance audit. The word `RESTORED` is the runner's generic success label; it does not mean that newly written modules had previously been verified.

## What was implemented and checked

| Work | Actual result |
|---|---|
| Existing original archive and physical dependencies | Missing objects restored from the pinned sources; no new mathematical credit claimed |
| `P2Winner9PullingArchiveCore` | Strict compilation passed; reuses the original pulling geometry theorem |
| `P2Winner9PullingOrderChecks` | Strict compilation passed |
| `P2Winner9CompletePullingData00`–`43`, `CompletePullingData`, `CompletePullingFlags` | Strict compilation passed |
| `P2Winner9CompletePullingCheck00` | Strict compilation passed; reuses the prior first-256 pulling checks and verifies new global bindings |
| `P2Winner9CompletePullingCheck43` | Strict compilation passed; covers the final 18 rows and final 17 adjacent-key comparisons |
| Middle geometry checks 01–42 and complete overlap assembly | Implemented in source-only; not compiled |
| Complete ledger | First repair reached a concrete recursion-depth failure in `full_literal_totals`; revised symbolic-projection repair is source-only and uncompiled |
| Complete numerical checks | 690 bounded pages, 44 block aggregators, and one complete aggregator generated: 11,026 explicit row proof obligations; not run as a complete family |
| Numerical probes on the accepted checker | Row 4/log passed in 6.958 s; row 7/Q6 passed in 11.720 s; single-block ledger arithmetic passed in 3.688 s |
| Materialized-minor optimization | First candidate failed during a Matrix/function transparency rewrite; corrected candidate retained in source-only, uncompiled |
| Closed literal-terminal assembly | Source-only candidate consumes the explicit complete numerical and geometry suppliers; uncompiled |

The 50 active new Lean files have successful strict compiler results. The **781 current uncompiled candidates** remain under `docs/source-only/20261124-p2-winner9/ImbalancedChen/`. Their presence supplies no kernel credit. This includes 43 geometry modules, 735 numerical modules, and the revised ledger, numerical-checker, and terminal candidates.

The accepted `P2Winner9OriginalPullingFlags`, `P2Winner9RowArithmeticChecker`, and `P2Winner9Terminal41SixRows` files remain byte-for-byte equal to the baseline.

## Full archive geometry

The candidate preserves all 201 original vertices, all 11,026 row ordinals, and the original 97 gates. Its pulling flags use the same 21 supporting planes as the existing first-block proof.

The geometry words store a rank and eight gate indices. The ordered words bind each rank to its original ordinal and vertex-set key. The proof first establishes every adjacent key comparison, then obtains a single global strict ordering; this includes all 43 rank-block boundaries. It uses the existing lifting-plane theorem to prove null intersections of the actual physical supports. Distinct row labels alone are not used as a disjointness proof.

An independent read-only review checked every packed word against the original row records and replayed all 11,026 finite pulling predicates in Python. It also checked the 11,025 adjacent comparisons, the rank/ordinal inverse binding, the original first-block identity, and the final partial block. Those checks corroborate source generation; they do not replace the pending Lean proofs.

Reproduce the source comparison without writing:

```bash
python verification/part2/render_winner9_pulling_flags.py --check-complete
```

The comparison accepts an active source, or its explicitly archived source-only counterpart when it has not been promoted. `--write-complete` materializes all generated candidates into the active module directory for a verification worktree.

## Complete numerical and ledger candidates

The row renderer emits no numerical answers or external proof oracle. Each leaf invokes the existing, proved `checkSelected` on the actual original archive record with `decide +kernel`. Of the 11,026 original winning branches, 5,615 are log branches and 5,411 are Q6 branches. Every original row is present exactly once; the final page has two rows.

```bash
python verification/part2/render_winner9_numerical_checks.py --all --check \
  --output-dir docs/source-only/20261124-p2-winner9/ImbalancedChen
```

The exact original selected numerator totals remain:

- log: `475182339168330434688559`;
- curvature: `475259749604404591554030`;
- mixed: `475741072397709744401965`;

all over `79228162514264337593543950336 = 2^96`. The two historical increments remain `77410436074156865471/2^96` and `481322793305152847935/2^96`. They replace the preceding stages once; the three full totals are not added together.

All 44 block triples match the original 690 pages by independent integer extraction. The full-module compile nevertheless exited 1 at the projection of the complete sum triple. The new repair projects a triple of six symbolic naturals in a private lemma, then instantiates that lemma with the actual sum equality. It preserves the original 56 theorem statements and eight definitions and keeps `maxRecDepth = 20000`. **The repaired bytes have not yet been compiled.**

## Cloud environment and blocker

The actual persistent worktree is:

```text
/workspace/p2-work-20261124
```

It uses official Lean 4.33.0-rc1 and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. The dependency objects, per-module source/object signatures, and logs are retained under:

```text
/workspace/p2-work-20261124/.lake/p2-continuation/
```

The exact runner used is preserved as [cloud-runner.py](cloud-runner.py). It reuses an object only when its source, dependency objects, flags, and pins match its saved signature. Current successful new modules used `-DwarningAsError=true`; no linter exception was added to a new proof. Several unchanged inherited modules required explicitly recorded style-linter exceptions while restoring their previous proofs. No sorry/axiom warning was suppressed.

The service now rejects new tasks with:

```text
Error executing tool run_command:
retained-job limit reached; ask owner to archive jobs
```

The advertised retention limit is 128 tasks. The currently exposed connector has no task-archive operation. No other session's tasks or workspace were deleted or cancelled. The two already-queued jobs were allowed to finish and their complete logs were saved here. See [environment-blocker.json](environment-blocker.json).

## Resume without repeating completed work

The service owner needs to archive completed task records while retaining their logs and the persistent workspace. After capacity is available:

1. Preserve and reuse the existing `.lake/p2-continuation/` object/signature cache.
2. Use a clean verification worktree containing this checkpoint and install the source-only candidates there. The previous cloud worktree still contains the failed first optimization and ledger attempts; those are **not** the corrected source-only bytes in this commit.
3. Verify the corrected `P2Winner9RowArithmeticChecker` first, then repeat the two short performance probes and compile one numerical page. Only choose a larger numerical batch after the actual result is known.
4. Verify the corrected `P2Winner9LedgerBridge`. Its original archive dependencies are already restored.
5. Compile `P2Winner9CompletePullingCheck01`–`42` and `P2Winner9CompletePullingGeometry`, reusing the 50 successful new modules.
6. Compile all numerical pages and aggregators, then the closed `P2Winner9CompleteSeedTerminal`. Keep compiler-success and whole-family-success distinct.
7. Run independent kernel replay, expanded-type checks, and a transitive axiom audit on the accepted new closure before promoting the full-family node.

The bounded pages and the cache signatures allow interrupted runs to retain completed proofs. No proof should be rewritten merely because its object was not originally present on this worker.

## Remaining full-P2 semantics

Even a successfully verified Winner9 family would leave independent P2 obligations:

- The current `terminal41Integral` is the literal-97-gate integral. It still needs an accepted identity with the original Full87 `cellIntegral (.remaining (.nine 11))`. Existing source-only proof text is in `P4AOriginalFull87SeedRefinements`, through `original_seed_integral_eq`; its receipt explicitly says remote verification was pending. Importing its whole old file would pull a large unrelated closure, so its exact definition/bridge slice should be reused.
- The same-rho positive-product supplier for `testedFibreBalance` is still absent. Existing native receivers retain the density, coprimality, signed-distribution, and small-prime terms; they do not prove the required bound by themselves.
- The original H247 bank still needs its 29 actual endpoint comparisons.
- The 20261106 manuscript fixes finite admitted families and finite queries before passing to the limit. The existing moving-box native interface has a stronger uniform quantifier order, which needs an explicit bridge. This is an interface/analytic obligation, not evidence of a counterexample to the manuscript.

Relevant manuscript sections are `prop:current-positive-product` and `eq:current-PP` in [argument.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex), and `sv:pair-base`, `sv:full-switched-mass`, `sv:finite-seed`, and the finite-query limit order in [sieve-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex).

No dashboard node was promoted to full-family or full-P2 completion by this checkpoint.
