# P5.6 / h34 — external input boundary for q-fibre weighted true H430 source

Mathematics commit `0a65a12a3330dd20c80bfb828bebe8ac003dc553`; blob `f84b7ea8cfff4815d99b443254292d367351365b`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1. These pins are **unchanged**.

## Reused existing/library facts and exact call sites

- Mathlib finite `Finset.sum_sigma`, `Finset.sum_congr`, `Finset.sum_add_distrib`, `Finset.sum_mul`, real ring normalization, and `Finset.card_sigma` / cast-of-sum. These are called in `sigma_weighted_root`, `original_signed_q_source_by_prime_fibres`, `original_weighted_true_H430_by_q_fibres` and `original_U34_real_count_by_q_fibres`. They are finite algebra, not imported number-theoretic asymptotics.
- Existing manuscript-INTERNAL `original_tag_dependent_signed_overlap N hN w3 w4` on the true original U3/U4 finite tagged source; `hN : 1 ≤ N`; used in the two source-disintegration lemmas.
- Existing manuscript-INTERNAL `primeCoordinate_mem` and `U3_eq_main_on_U4` with actual original `p ∈ originalBand N .U4`, `hN : 2 ≤ N`, `primeCoordinate N p ∈ Ico a (59/250)`. Called in `original_weighted_true_H430_by_q_fibres`, including for an empty original q-fibre. Uses the genuine original H430 main branch, not H248 or a tail clamp.
- Existing manuscript-INTERNAL `original_U34_count_double_overlap N hN` and original `originalReceiver`; used in the literal arithmetic count corollary.

## New genuinely external analytic theorem

**None.** No PNT/Mertens/BV/PP result, new trust bypass, custom axiom, target-equivalent source-to-Theta license, or outside result has been introduced or proven. The manuscript's own source-to-Theta compatibility, full/selected/inherited owner, PP/same-rho matching, signed Euler payments and common 430+11 refinement remain INTERNAL and OPEN.

No numerical430 certification or Lean compilation was performed. SOURCE_ONLY / UNCOMPILED / UNEVALUATED; **not green**.
