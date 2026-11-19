# P5.6 → h34 — original Q80 two-round causal tail cutoffs

Date: 2026-11-20 (Asia/Shanghai).
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Incoming verified HEAD: `ad5390211865249dcc4dfa6c54993a781e309ff7`.
Source: `Part5OriginalH430TwoRoundCausalCutoffs.lean` (188 lines; 8 theorem declarations).
Source Git blob: `b6b41d9f75f96e525c339f3448c3715e0d789939`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Novel manuscript-internal finite-speed result

This packet proves CANDIDATE local facts about the exact integer Q80 producer:
- A genuinely zero old-table tail annihilates the original Buchstab weighted suffix (same pinned q/logWeights, no bound assumptions).
- Upper next-round tail cutoff is max(100, old upper cutoff, old lower cutoff+49). The constant 100 comes from the original 106-row literal targets and the actual upper-only bank scan.
- Lower next-round cutoff is max(50, old lower cutoff, old upper cutoff+49), with no bank.
- Starting from the genuine (upper,lower) seed cutoffs (60,0), an induction derives a causal cutoff for every generation.
- Specifically round 2 has ZERO upper indices 158..199 and ZERO lower indices 149..199; lower 0..49 remains zero by the already supplied all-generation invariant. Hence no more than 257 of 400 cells can be nonzero in round two.

These support restrictions are exact logical candidates; they do not claim that all 257 are positive. The cutoffs grow and become vacuous once they reach >=200. They are NOT a proof of any analytic envelope or the 430-generation CLOSED-CELL induction.

## Scope and status

No seven-integral lower bound improved: prior uncompiled candidate total is 0.590 versus target 0.650. The first-round bank/Buchstab positive candidate payment, true frozen F seed, all subsequent CLOSED-CELL numeric bounds, original U3/U4 selected-count identity and weights, PP/same-rho, native-history and 430+11 causal refinement remain unresolved.

Pinned manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean: `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
No constants, c/K, root norm 7/2, row norm12, current CI or other owners' files changed.

GitHub authenticated connection is writable. The independent local environment lacks Lean/Lake/Elan and pinned compiled dependencies; native GitHub HTTPS DNS fails. No compilation, kernel replay, transitive axiom audit, finite Lean certification or CI run occurred. Even a source-syntax or hash check is not Lean verification.

Stage after `ImbalancedChen.Part5OriginalH430FirstRoundActiveSupport` under the existing original import closure; do not install into production or change CI as a substitute for validation.

## Next substantive step

Compile the new module with its fixed dependencies when an authorized pinned toolchain is available. Then prove the REAL first-round positive bank/suffix integer bounds against frozen F, and use causal cutoffs for later action screening. Do not treat these support lemmas as numerical payment.

**完整h34稿内证明仍未闭合。**
