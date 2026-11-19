# P5.6 h34 — original D6 eight-cell rational lower candidate

Date: 2026-11-19.
Incoming remote HEAD: `d43af03cec851f66ccf7a2b5fa82c2a88f7b317a` on `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Mathematical source increment

`Part5OriginalH430ActualD6EightCellRational.lean` implements one independent new internal source certificate for the ORIGINAL, full, untruncated D6 logarithmic outer interval `[50/227,100/353]` from the pinned manuscript. Eight consecutive **exact rational** cells are cut at

`50/227, 73125/320524, 37825/160262, 78175/320524, 20175/80131, 83225/320524, 42875/160262, 88275/320524, 100/353`.

The `join_actual` lemma composes actual integrals by interval additivity and inherited `continuousOn_d6OuterSlice`. Each `h0`–`h7` uses existing `d6_rational_cell_integral_lower 2`, with actual `d6CellLower`, the unchanged two-term `RationalLogCertificate` lower series, and correct per-cell lower-left / upper-right endpoints. The source does NOT introduce an assumed real integral value.

Independent exact Fraction arithmetic evaluated the eight-cell rational sum to
`0.115195589311109913066157923...`, strictly greater than `115/1000`.
This finite arithmetic diagnosis is **not Lean compilation or finite certificate replay**. The Lean candidate declarations are:

- `join_actual`: actual integral additivity on two contiguous original D6 subintervals.
- `eight_cell_mass_le_actual_D6`: eight rational cell lower payments against actual D6.
- `eight_cell_rational_arithmetic`: eight-cell exact rational sum at least 115/1000.
- `actual_d6Log_ge_115_per_1000`: D6 >= 115/1000.
- `partial_lambda_ge_118_per_1000`: seven genuine source integrals / 5 >= 118/1000, using latest original D5 >= 171/1000 and the other unchanged sources.

Relative to incoming candidate D6 >= 110/1000 and seven-source sum >= 585/1000, the added candidate D6 payment is 5/1000; seven-source sum is now 590/1000, lambda >= 590/5000 = 118/1000. Required frozen total remains 650/1000, **60/1000 short even at candidate level**. This does not claim analytic seed or CLOSED-CELL closure.

## Engineering and verification

GitHub source-only commit on the same exclusive h34 work branch; no CI configuration, dependencies, production files, other branches, frozen manuscript, c/K, root norm 7/2, row norm 12, same-Q, alpha, or 430+11 budget altered. No new external analytic input. The commit history plus REGISTRY identify this increment's provenance; no previous branch SHA was reset.

The execution container has no `lean`, `lake`, `elan`, or installed pinned import closure; native `git ls-remote` cannot resolve github.com DNS. The authenticated GitHub repository connector supports source-only commits and remote reads, but does not compile Lean. No actual Lean/Lake, kernel replay, transitive axiom audit, full finite checks, or CI run was completed. Status remains **SOURCE_ONLY / UNCOMPILED / UNEVALUATED**, never green.

## Continuing manuscript-internal obligations

1. Stage this module and exact inherited source-only import DAG with pinned toolchain; run targeted Lean compilation and correct real elaboration failures without placeholders or unproved bridges.
2. Complete original seven-source total >= 650/1000, distinguishing real support intervals and preventing double-payment; currently candidate total only 590/1000.
3. Prove actual frozen double-table Q80 seed/base and fixed 20249/1000000 analytic intercept in correct count setting.
4. Finish original all-action 430-generation retention/Buchstab/winning-bank CLOSED-CELL count induction, complete original U3/U4 selected/full/inherited source filters, root weights, owners and rejected lanes.
5. Complete manuscript-local PP/same-rho, native-history mass, integral–Theta–count matching and one causal 430+11 refinement; kernel replay and transitive axiom audit remain open.

No external proof project is started.
