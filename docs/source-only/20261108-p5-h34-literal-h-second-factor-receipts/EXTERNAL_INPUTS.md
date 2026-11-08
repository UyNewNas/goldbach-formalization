# P5.6/h34 external input boundary — original h-stage q-factor receipts

Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766, paper/source/manuscript-body.tex blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79.
Pinned compiler: Lean v4.33.0-rc1; pinned Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**NEW EXTERNAL ANALYTIC INPUTS: NONE.** No PNT/Mertens/BV or other external proof implementation; no new custom axiom.

## Existing precise manuscript-local declarations consumed (not reclassified as external)

- `Part5OriginalH430OriginalSecondFactorWindow.no_post_root` is NOT assumed; this packet proves the exact `no_second_factor_iff_p_rough` equivalence using original `hasPostRootPrimeFactor` and `ChenPrimeRough` definitions.
- `Part5OriginalH430OriginalSecondFactorWindow.possible_original_second_iff`: applied in `h_second_eligible_iff_real_candidate`, `h_second_candidate_literal_window`, `h_high_receipt_no_second_candidate`; its hypotheses `z∈originalTagged N`, `ell.Prime`, `ell∣arithmeticQuotientPrime z` are supplied at those call sites.
- `Part5OriginalH430OriginalSecondFactorWindow.possible_second_factor_window`: invoked in `h_second_candidate_literal_window`, preserving the original quotient N^a roughness and real second-enumerator membership.
- `Part5OriginalH430LiteralLowerStartReceipts.h_start_stage_subset_below`, `h_start_above_no_stage` and `original_h_start_signed_three_unpaid_classes`: instantiated only at the literal ordinary LOWER h-start `literalLowerStartH N`, with `literalLowerStartH N ≤ (cap:ℝ)` explicit; used respectively for the three-bound support window, high-band impossibility and complete four-family signed partition.
- `Part5OriginalH430OriginalSecondFactorWindow.stage_second_candidate_eligibility_signed_ledger`: invoked at the actual original h-start source and reexpressed as the two finite subfamilies; this is exact q/tag arithmetic, not a one-mark root count.
- Mathlib nat/real order casts, Finset filter and finite sums, `ring`: used for finite logical and algebraic transport only.

## Unresolved but manuscript-INTERNAL

Actual U3/U4 upper count owner, actual z0 and stage, full/selected/inherited and physical-Q source correspondence, q multiplicity and root weights, correct parity/sign and Euler first-excluded payment, all unpaid receipt/erasure/rejection mass, native CLOSED-CELL arithmetic induction, base/seed/floor, PP/same-rho, outer integral/Theta/count and one nested430+11 causal refinement. These are not external interfaces and not discharged by this packet.

SOURCE ONLY / UNCOMPILED / UNEVALUATED. No kernel replay or transitive axiom audit has been performed.
