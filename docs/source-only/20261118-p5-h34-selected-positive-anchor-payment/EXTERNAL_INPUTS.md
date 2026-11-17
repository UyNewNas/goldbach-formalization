# P5.6 → h34: selected positive anchor payment / external boundary

Manuscript pinned at `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Toolchain pinned at Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New genuinely external analytic input: NONE.**
No PNT, Mertens, BV, prime-distribution or sieve results are proved,
reformulated, or upgraded.

## Reused manuscript-local interfaces and actual call sites

- `Part5OriginalH430ClosedCellIdealSplit.fixedReadSlack`,
  `bankFixedSlackMass`, `bankBaseIdealPositive`, and
  `frozen_root_le_ideal_balance_plus_fixed_slack`: consumed in
  `fixedReadSlack_le_actionPositiveAnchorAllowance`,
  `bankFixedSlackMass_le_selectedPositiveAnchorPayment`, and
  `frozen_root_le_selectedPositiveAnchorPayment`; original
  positive dynamic-ideal balance and CLOSED-CELL predecessor premise
  remain unchanged.
- `Part5OriginalH430FixedReadDictionary`: original `W1Anchor`,
  `w1Cell`, `originalW2At`, `w2Cell`, `floorValue` and
  `precedingH`; consumed by the literal per-action W1 and W2
  endpoint expressions.
- `Part5OriginalH430RequestedLevelBankSupply.selectedLevel` and
  `Part5OriginalH430FixedAnchorSlackPayment.bankSelectedTheta`:
  used in the real selected `Fin` occurrence sums and coarse
  uniform-maximum comparison.
- `Part5OriginalH430FixedAnchorSlackPayment.occurrenceScale_nonneg`
  (imported transitively from requested-level history):
  used to sum the pointwise positive-endpoint bounds over only
  selected original actions, at the genuine root Q.
- `Part5OriginalH430ExplicitAnchorDefect.actualAnchorDefect_nonneg`
  and `actualAnchorDefect_supplies_upper`: consumed in
  `actionPositiveAnchorAllowance_le_actualAnchorDefect`.
  This keeps the previous exact finite uniform envelope, not
  a newly selected arbitrary small delta.
- Mathlib real-order `max`, positive linear combinations, finite
  sums, positivity and linear arithmetic are reused unchanged.

## Manuscript-internal obligations retained

The new finite per-selected-action amounts have NOT been estimated
against c/K or the fixed 430+11 reserve, and the source is NOT
compiled. Original base/seed/CLOSED-CELL induction, dynamic/strict-prime
positive source payments, original U3/U4 counts and owners, PP/same-rho,
signed Euler/native-history, integral–Theta–count and one shared nested
causal refinement remain manuscript-local and open. No new axiom or
target-equivalent assumption is introduced. Exact consumers and
quantifiers are NOT reassigned to external proof inputs.
