# P1.4: exact rank/log of physical failed upper exit
Status: SOURCE_ONLY, UNEVALUATED, UNCOMPILED, ZERO FORMAL CREDIT. The P1.4 parent remains YELLOW.

Baseline: GitHub ref f651e90c4d28911b71872b437ec6c769c62ae4df of the previous failed-odd-guard branch, independently read. Dedicated continuation: chatgpt/p1-full87-physical-failure-log-20261106.
Source: docs/source-only/20261106-full87-physical-failure-log/P4AOriginalFull87FailedLogExit.lean, Git blob 6cba9449f05995dae5118f0b38f1c3478eeb023c, 273 lines. Source edits: 2886bbb (initial), 5dd478d (correct log rewrite orientation), e47d714 (preserve original before/chosen/smaller occurrence witness).
Manuscript pin: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, paper/source/manuscript-body.tex, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79, section 4. Constants c=49044063/25000000; K=8452171/1250000.

## Substantive source changes
Three Lean candidate theorem bodies:
1. failed_square_to_exact_N_log: convert the same physical finite minimum-prime square failure at R=N^beta into an exact base-N log inequality; full-product positivity follows from failure and R>0.
2. failed_square_to_history_chosen_log: exact product/log split over original historical eighth prefix and the list of successfully selected post-eight occurrences, without set conversion or new coefficient; beta <= S8 + Schosen + 3*t_rejected.
3. owned87_later_failure_exact_rank_log_exit: start from an actual owned original87 eighth-frontier rejected attempt, preserve before/chosen/rejected/smaller and both existing frozen choices; recover chosen.length=2*(m+1), so exit rank=11+2*m; use existing sum_primeHistoryLogCoordinates for exactly the original eighth Fin 8 tuple; derive hEXIT form with no caller-supplied rank, beta, positivity or log reconstruction.

This discharges a local manuscript-INTERNAL hEXIT normalization; does NOT establish all indexed prior odd hprior or hpair, ninth-rank inherited-square control, ordinary residual density or analytic errors. The earlier structural recursion used h(p)=1 and is NOT yet a physical g_N correction mean.

## Checks
Verified final source blob by GitHub file read, static forbidden-token/parenthesis scan. Independent non-Lean smoke tests: 4,000 floating-point logarithmic cases and 8,000 finite rank/product identities; synthetic, not original saved87 archive and not proof verification.
Lean/Lake NOT RUN, kernel replay NOT RUN, transitive axiom audit NOT RUN, independent review NOT RUN, saved87 archive NOT RUN, CI NOT DISPATCHED. Source proof terms remain UNEVALUATED.

## Open manuscript-INTERNAL obligations
Indexed successful odd hprior tests in the same frozen level, pairwise post-eight coordinate hpair, rank-nine inherited-square loss and payment, actual same-source Rosser residual integral, finite arithmetic/discrepancy/centre/modulus error, sixth filtering, raw/finite/filtered signed gain, full saved87 archive, changed/tagged, two distinct density/compilation reserves and same-rho assembly. No formal closure yet.
