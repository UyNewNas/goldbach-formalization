# P5.6/h34 occupied-position ledger — external boundary

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`. Fixed toolchain: Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**No newly introduced analytic inputs, no new assumed axioms, and no proof of any external analytic theorem.**

## Reused installed / pinned elementary library

- Mathlib `Finset.filter`, `Finset.mem_filter`, `Finset.sum_filter`, `Finset.sum_le_sum`, `Finset.sum_pos'`, natural-to-real cast order, `Nat.eq_zero_of_not_pos`, and real order/linear arithmetic.
- These are elementary finite-sum / arithmetic tools and are invoked inside `actual_Phi_eq_occupied_position_sum`, `actual_occupied_mass_le_Phi`, `actual_unpaid_le_occupied_mass_envelope`, and `actual_U34_unpaid_le_occupied_envelope` of `Part5OriginalH430ActualOccupiedMass.lean`.

## Existing manuscript-local / finite-source declarations reused

- `ImbalancedChen.Part5OriginalH430ActualResolvedMarkedPushforward.activeProduct_Phi_exact` and the actual `activePositions`, `activeProductSupport`, `activeProductSigma` (original physical Q, per-position marks, product collisions preserved). This already existed in the ancestor source-only chain; not re-proved or silently installed.
- `ImbalancedChen.Part5OriginalH430ActualSievedPositionPayment.actualPositionPhiTerm` at exact source blob `353c262a36fc4b024eb8e8c3edd929a09bacd610`: the original literal `sourceSieveCount` at a resolved position, multiplied by `levelMark`.
- `ImbalancedChen.Part5OriginalH430ActualUnpaidOrdinaryEnvelope.actualUnpaidAt` and `actualU34Unpaid`; `ImbalancedChen.Part5OriginalH430TrueCountMarkedGap.unpaidOriginalMarkedGap` and `originalMarkedDiscrepancy`.
- `Part5OriginalH430TaggedArithmeticReceivers.originalReceiver` and `originalBand`, with both U3/U4 tags retained, and `Part5OriginalH430RequestedLevelBankSupply`'s existing strictly positive original history mark.
- `ImbalancedChen.P2EnhancedTwentyOneSameQWeighted.Phi`, `cutoff` and its existing source-sieve count. The source count and analytic upstream dependencies remain at the repository's pinned versions; this packet proves only finite positive-cardinality consequences, not new sieve asymptotics.

The immediate source-only import closure (including prior unfinished proof candidates) has **not** been installed and compiled. The previous `EXTERNAL_INPUTS.md` mapping remains inherited, not audited transitively. All candidates are `UNCOMPILED`, and all inherited finite numerical guards are `UNEVALUATED`.

## Manuscript-internal obligations not relabelled external

The original U3/U4 selected-count source and full/selected/inherited owner; authentic q/tag-to-Fin capacity, root weights and all rejection/signed Euler payments; CLOSED-CELL arithmetic induction and its base/seed/floor; true PP/same-rho; native-history mass and the common 430+11 nested causal proof remain **internal**. The real occupied source mark lower bound does not imply any of these missing assertions.
