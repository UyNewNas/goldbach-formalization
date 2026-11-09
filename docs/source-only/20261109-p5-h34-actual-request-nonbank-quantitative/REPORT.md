# P5.6 → h34 — actual request nonbank quantitative bridge

Date: 2026-11-09 UTC. Repository: `UyNewNas/goldbach-formalization`.
Independent branch: `chatgpt/p5-h34-actual-request-nonbank-quantitative-20261109`.
Verified incoming HEAD: `56d0c3040031e1e2fa86aab3e3da6e3e4a926c5b`.
Mathematics source commit: `95571b959dc2c0e03193583f781d2fb011ce43fa`.
Source file: `Part5OriginalH430ActualRequestNonbankQuantitative.lean`.
Source Git blob: `ffdad1a32402ba81f6e14883997971538fd7f47d` (247 lines, 6 definitions, 9 candidate theorems).

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Real previous handoff and what this packet adds

The original request-admission REPORT/REGISTRY/EXTERNAL_INPUTS and latest actual-request-all-action-partition REPORT/REGISTRY/EXTERNAL_INPUTS were read. The most recent verified HEAD was `56d0c30`, not the historical `0a3fa5a`. The prior packet partitioned the true g+1 resolver's generated Fin list into retained, Buchstab and 106 bank positions, with literal scalar versus specified-cell reads and zero unresolved contributions. It had not established that its NEW retained and Buchstab sets were the SAME positions as the older quantitative nonbank supplier.

The older `RequestedNonbankLevel` provides `retained_level_exact` and `uniform_level_buchstab_supply`; `RequestedCandidateLevel` provides `all_markedBankRead_le_candidate`. This packet binds those existing, uncompiled manuscript-local sources to the latest **actualChoice** Fin positions without counting rejected alternatives.

Nine candidate declarations:

1. `actual_retained_eq_selected_retained`: literal equality with the older actual selected-retention Finset.
2. `actual_buchstab_eq_selected_buchstab`: literal equality with the older actual selected-Buchstab Finset.
3. `actual_retention_child_exact`: authentic retention child edge value equals original predecessor-cell requestValue times physical theta and positive occurrence mark; scalar ownership is not substituted.
4. `actual_new_table_read_exact`: full new-table read equals the three selected-action masses, with unresolved positions zero.
5. `actual_new_table_read_le_bank_candidates`: bound the full true new-table read by the two still-literal nonbank reads and original 106 previously computed bank candidates. No bank alternative is duplicated.
6–8. `actual_buchstab_theta_eq_existing`, `actual_buchstab_error_eq_existing`, `actual_buchstab_row_eq_existing`: prove the actualChoice indexed physical source, its absolute row error and row mass are exactly the old immutable nonbank supplier's source (same p, same physical Q, same generation and list positions).
9. `uniform_actual_nonbank_quantitative`: choose a single threshold before N, prime, root, precision and g; carry the previous full read bound together with actual selected Buchstab absolute error ≤ epsilon*Theta, nonnegative row coefficients, mass ≤ 5*Theta, and the zero-Theta/zero-error/zero-row case. This does NOT add the Buchstab 5*Theta to bank's 12*Theta as an extra charge on one winner.

The work discharges a concrete missing *matching* step between the latest partition and older request-level retention/Buchstab quantitative proofs. It is not an iteration of a generic finite sum identity and does not assert any arithmetic U3/U4 source/count equivalence.

## Fixed manuscript and prohibited shortcuts

Manuscript stays fixed to `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. This is the pre-existing 2026-10-10 mapping, **not** a switch to the public 2026-11-06 edition. Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Original c/K, root 7/2, row 12, true alpha, physical same-Q, selected 106 rows, list multiplicities and 430+11 budgets remain unmodified.

No new external analytic theorem or custom axiom. No change to P1.4, P3.6, production modules, main branch, CI, toolchain or source files of concurrent tasks. Only this new h34-owned packet is written.

## Checks and nonclaims

The GitHub-connected source is saved on the independent branch and its exact Git blob reread. Local `command -v lean/lake/elan` found no tool binaries; also checked common installation paths. Native `git ls-remote` failed because github.com DNS cannot be resolved in this runtime. Source-only ancestor modules have not been staged in the pinned Lake import closure. Hence **no Lean parsing/elaboration, successful compile, kernel replay, transitive-axiom audit, finite 430 certificate, or green node** is claimed. Any text-level validation is NOT Lean proof validation. All proof bodies and inherited finite guards are UNEVALUATED.

## OPEN manuscript-internal obligations

- Upgrade the now matched actual nonbank/106 one-step supplier into the **genuine CLOSED-CELL count induction**, proving predecessor base/seed, fixed/switched values, correct floor/rounding and selected-child errors with the manuscript's actual inequality direction.
- Match original U3/U4 root weights and full/selected/inherited count-owner source to generated Fin history, preserving q/tag multiplicity, actual stage and physical Q.
- Bound all six original rejection lanes, collisions and signed Euler residual by the actual permitted H430 budget.
- Complete feedback-to-integral, manuscript-local PP/same-rho compatibility, native-history proper/equality/inherit mass, outer Theta/count and one nested 430+11 causal refinement.
- Stage pinned source-only imports and compile these exact targets, then kernel replay, transitive axiom audit and finite tests. Static checks cannot substitute for these.

**Next direct task:** compile the new module and pinned parents in an isolated local/source-only staging workspace (if a fixed Lean runner becomes available), fix true elaboration errors; use the same selected-action inequality in the genuine count induction without treating a prior-generation closed-cell bound as a gratuitous assumption.

**完整h34稿内证明仍未闭合。**
