# h34 external inputs — actual resolved sieve-position payment

Scope: fixed manuscript's internal proof consumers only. New external analytic results and axioms: **NONE**.
Fixed manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766, paper/source/manuscript-body.tex.
Pinned Lean: v4.33.0-rc1; Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Existing imported facts and actual call locations:
- Mathlib Finset.sum_le_sum, Finset.sum_eq_zero, indicator sum, Nat.cast_nonneg, positivity of products and real linear arithmetic: actual_position_Phi_term_le_full, actual_Phi_zero_iff_all_sieved_positions_empty, actual_unpaid_le_one_sieved_position, actual_positive_sieved_position_strictly_shrinks_unpaid.
- Existing manuscript-local mark_pos and physical generation LevelIndex; actualPositionPhiTerm and all source-term theorems. No rewrite of the root geometry or sieve input.
- Existing manuscript-local activeProduct_Phi_exact (original occurrence-preserving pushforward) and existing sourceSieveCount/cutoff: exact Phi theorem and the one-position bound.
- Existing originalReceiver, unpaidOriginalMarkedGap and actualUnpaidAt: actual_unpaid_le_one_sieved_position and strict decrease theorem.

No PNT/Mertens/BV proof implemented; their pinned existing interfaces are not expanded. Existing Lean module imports are source-only candidates, NOT compiled evidence.
Still manuscript-internal: true U3/U4 full/selected/inherited owner and z0, real q/tag source occupancy and effective payment capacity, root weights, rejection lanes/signed Euler, all-action CLOSED-CELL, seed/floor, PP/same-rho, native-history, outer count/Theta/integral and ONE 430+11 causal refinement.
No target-equivalent or q=d assumption introduced. No kernel replay, transitive axiom audit or finite numerical verification was run.
