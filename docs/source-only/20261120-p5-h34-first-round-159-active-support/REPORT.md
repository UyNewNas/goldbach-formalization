# P5.6 → h34 — first-round 159-cell active support

Date: 2026-11-20 (Asia/Shanghai).
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Incoming verified HEAD: `b2ae28ef4834f73c343db1aa543d387a2d20170a`.
Source: `Part5OriginalH430FirstRoundActiveSupport.lean`, 133 lines, 6 public theorem statements + 1 private scan lemma.
Git blob: `a88a174465f72e9db1bff3aa17f5dce7da7cb10d`.

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Toolchain: `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## New, bounded manuscript-internal candidate proofs

1. `original_106_targets_below_hundred`: all physical targets of the ORIGINAL 106-row literal bank have index <100, including the last 36 non-W1 rows. Proof candidate uses `fin_cases` and kernel-oriented `decide`, not `native_decide` or an oracle.
2. `original_bank_untargeted_from_hundred` and `scan_unchanged_when_no_row_targets`: a targetless scan cannot modify the actual retained decision/provenance.
3. `first_upper_round_zero_from_hundred`: first upper generation at all indices 100..199 is identically zero, since the lower seed is zero, upper ordinary action is retained, the original upper seed ends at 59, and bank targets end at 99.
4. `first_round_outside_active_window_zero` and `first_round_nonzero_only_inside_active_window`: the first Q80 round has at most 100 active upper positions (0..99) and 59 active lower positions (50..108); the other 241 Boolean-table cells are zero. This does NOT assert every active position is nonzero.
5. `inactive_first_round_floor_le_F`: at those 241 inactive cells, a CLOSED-CELL inequality reduces to nonnegativity of the unchanged analytic F at the exact closed query point. Nonnegativity of F is NOT asserted or supplied here.

There is no F base, no 159-cell positive candidate payment, no all-430 induction, no U3/U4 selected-count source or root owner completion, no seven-integral >=0.650 certification, no PP/same-rho closure, and no 430+11 nested causal refinement in this packet.

## Evidence and engineering boundary

- Authenticated GitHub connector confirmed repository push permission, branch HEAD, prior packet, original 106-row table and original Q80 producer definitions. Checked the initial admission REPORT/REGISTRY/EXTERNAL_INPUTS.
- An independent JS parse of the literal 106 target lists found 106 rows, all targets in [0,99], exactly 100 distinct targeted physical indices; the upper first-round ordinary action is identified by the prior actual source theorem, not simulated.
- No Lean/Lake/Elan executable exists on PATH in this run. The native git HTTPS probe returned `Could not resolve host: github.com`. There is no pinned compiled import closure, so no Lean compilation, kernel replay, transitive axiom audit or finite Lean certification was performed. Ordinary code/row parsing is not a formal compilation result.
- Installation order: stage the prior source-only import chain, then `ImbalancedChen.Part5OriginalH430FirstRoundSourcePartition`, then this module under the pinned toolchain. It has not been installed into the production tree.
- Scope: new source-only files under this packet only. No P1.4/P3.6, original manuscript, pinned constants, c/K, root norm 7/2, row norm 12, CI or dependency changes.

## Next substantive action

Compile this exact module and the import chain under the fixed pins. Then use the 159 active cells to reduce first-round actual bank/suffix **integer** payments, and prove the original F seed/first-round closed query envelopes. The later 429 rounds and complete h34 internal count bridge remain separate work.

**完整h34稿内证明仍未闭合。**
