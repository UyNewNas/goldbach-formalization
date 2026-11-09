# P5.6 → h34 — actual resolved sieved-position source payment

Date: 2026-11-09 UTC. Repository: UyNewNas/goldbach-formalization.
Branch: chatgpt/p5-h34-actual-sieved-position-payment-20261109 (isolated due to simultaneous h34 run).
Baseline: 5a620496cb951fd3a66a30d327873920870d5a00.
Mathematical source commit: 0729f3f8d8d0beddb683d67dfb93b38f02575f80.
Verified source blob: 353c262a36fc4b024eb8e8c3edd929a09bacd610.
Fixed manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766 / paper/source/manuscript-body.tex.
Fixed Lean: v4.33.0-rc1. Fixed Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Mathematical source increment

New Part5OriginalH430ActualSievedPositionPayment.lean: 189 lines, five candidate theorem bodies, one definition.

1. actualPositionPhiTerm uses the REAL resolved List/Fin occurrence with its original positive levelMark, actual parentProduct d, root-specific physical Q, literal sourceSieveCount N d (d*N) and exact 11/5 source cutoff. It never assumes d=q.
2. actual_position_Phi_term_nonneg and actual_position_Phi_term_le_full prove a nonnegative one-position term and domination by the ACTUAL level Phi via a finite indicator sum; distinct original positions with coincident d retain their separate marks. No q-to-history injectivity is assumed.
3. actual_Phi_zero_iff_all_sieved_positions_empty proves Phi=0 exactly when EVERY real resolved historical position has ZERO source-sieve cardinality at its own cutoff. Hence a nonempty generation and positive Theta alone need not furnish positive Phi.
4. actual_unpaid_le_one_sieved_position yields an explicit quantitative original-q debt bound:
   actualUnpaidAt <= max(originalReceiver.card - 5*actualPositionPhiTerm(l), 0)
   for any real selected position l. This is strictly sharper than the ordinary whole-count envelope WHEN its genuine source term is positive.
5. actual_positive_sieved_position_strictly_shrinks_unpaid proves that a real selected position with positive source-sieve count strictly reduces unpaid debt below originalReceiver.card, provided the original receiver is nonempty.

The proof is a local finite-source contribution, not an H430 asymptotic payment. Positive source count and sufficient weight are not proved to exist uniformly at the TRUE original U3/U4 selected count owner. Neither arithmetic quotient q nor q/tag multiplicity is equated with d or one history position. No stage owner, full/selected/inherited filter, root count weight, six rejection lanes or signed Euler suffix is paid. The physical Q, true alpha, original c/K, root norm 7/2, row norm 12, and the 430+11 budget remain unchanged.

## Verification and next dependency

Authenticated GitHub owner push permission, the predecessor source handoff and original 20261105 REPORT/REGISTRY/EXTERNAL_INPUTS were inspected. A separate h34 task was recorded in_progress, so only this new independent directory/branch was written. Readback of math commit and Git blob found 189 added Lean lines, zero deleted lines, and no modification to P1.4, P3.6, production, manuscript, toolchain or CI.

Only static source checks are available here. This container has NO Lean, Lake or Elan binary, and native Git cannot resolve github.com. This source-only import closure is NOT installed under ImbalancedChen/, and existing CI does not automatically build it; no CI run was dispatched. NO Lean elaboration, compile, kernel replay, transitive axiom audit or numerical430 finite replay was performed. All new theorems are uncompiled candidates, green proof credit zero, inherited finite certifications UNEVALUATED.

NEXT: In an isolated workspace stage pinned source-only predecessor modules and compile with pinned Lean/Mathlib. Then establish true upper H430 selected history owner, source-sieve occupancy and a quantitative lower mass bound sufficient for actual original q/tag debts (including overlapping U4 payments), or retain the unpaid difference explicitly. Complete all-action CLOSED-CELL, base/seed/floor, manuscript-local PP/same-rho, native-history and common 430+11 causal refinement.

**完整h34稿内证明仍未闭合。**
