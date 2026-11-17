# P5.6 → h34: explicit real-table anchor defect / external-input boundary

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean: `v4.33.0-rc1`; Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New genuinely external analytic inputs: NONE.**
No PNT, Mertens, BV, prime-distribution or sieve-theoretic proof is implemented, upgraded or assumed.

## Reused fixed-version manuscript-local interfaces

- `Part5OriginalH430FixedReadDictionary`: `W1Anchor`, `w1Cell`, `originalW2At`, `w2Cell`, `floorValue`, `precedingH`. Consumed by the four new concrete finite-defect definitions, and the endpoint supremum proofs. These are original Q80 table and literal W1/W2 anchor reads, not substitute numerical data.
- `Part5OriginalH430FixedAnchorSlackPayment.FixedAnchorUpper`: consumed by `actualAnchorDefect_supplies_upper` and `actualAnchorDefect_le_any_nonnegative_upper`. The condition is now proved for the exactly defined finite deficit, not independently assumed.
- `Part5OriginalH430FixedAnchorSlackPayment.bank_fixed_slack_le_anchor_delta_theta`: consumed by `bank_fixed_slack_le_actual_anchor_defect`, retaining genuine selected Fin positions and same-Q Theta.
- `Part5OriginalH430FixedAnchorSlackPayment.frozen_root_le_anchor_delta_budget`: consumed by `frozen_root_le_actual_anchor_defect_budget`, retaining original rootRequest/rootQ, zero-generation seed, Buchstab source, positive base/feedback debt, feedback-floor credit and 430-level history.

Foundational Lean/Mathlib `Finset.sup'`, `Finset.le_sup'`, `Finset.sup'_le`, real `max`, and order transitivity are reused. No foundational backend is replaced; no new axiom, sorry, admit or unsafe proof escape is added.

## Manuscript-local obligations not reassigned as external

The finite maxima have not been numerically evaluated or upper-bounded by the h34 budget. Preceding CLOSED-CELL, original seed/fixed/switch/floor induction, genuine dynamic and Buchstab positive payments, original U3/U4 counts and owner, native-history, signed Euler, PP/same-rho, outer integrals, Theta-to-count and one nested 430+11 refinement all remain manuscript-internal and open.

No source here has passed Lean compilation/kernel replay or a transitive axiom audit.
