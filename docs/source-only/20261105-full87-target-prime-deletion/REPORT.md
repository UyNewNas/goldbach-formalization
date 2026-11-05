# P1.4 — actual target prime deletion for original ordinary parity density

Base: `06e0a1e088cb2865acd62b96641afe8e5f8c7de3`. New branch: `chatgpt/p1-full87-target-prime-deletion-20261105`.

Unlike earlier repeated finite error ledgers, this packet addresses the **specific target-prime deletion factor** identified in the manuscript's ordinary parity exit-series density argument. The proof starts from the actual set of prime factors of N. It proves two independent finite facts needed for a *target-uniform* small error:

1. `lo ^ card(targetPrimeInterval N lo hi) ≤ N`. The key nontrivial step is the product of distinct target prime factors dividing N, not merely each prime separately dividing N.
2. For `lo≥3`, the real multiplier `∏_(p|N,lo≤p<hi)(1−1/(p−1))` belongs to [0,1] and is ≥ `1−card/(lo−1)`. When `N<lo^(k+1)`, the previous cardinality bound yields `1−k/(lo−1)` uniformly across all N satisfying that power gap.

At rank j on a positive compact parameter domain, the manuscript's square tests prescribe `p_last>N^δ_j`, `δ_j=β_min/(3·2^(j−1))`. Once the **actual** integer lower cutoff `lo` is connected and the power-gap proof made, one may choose a fixed integer `k>1/δ_j`, yielding a loss at most `k/(lo−1)`, tending to zero. This packet does **not** prove that last step, does not swap ceil/floor at a strict threshold, and does **not** infer equality of the unfiltered and target-deleted infinite exit-series.

The exact existing original87 terminal-density source is imported. Actual old/new sixth/eighth parity continuations and owner/trim are untouched. The new finite multiplier must still be attached to those same continuations. The factor itself is not a replacement signed measure or sieve policy; multiplying it by an arbitrary signed quantity without proof is prohibited.

## Checks and status
Finite arithmetic JS reference: 72,000 combinations N=1..1200, lo=3..45 step3, four upper cutoffs; tested exact integer power/cardinality inequalities and numerical finite-product/cardinality inequalities (no failures), and k=0..4 power-gap cases. This is independent finite regression, not Lean or original87 archive validation.

Manuscript `9731290e8f53cffda44129906cde6a965eaa869b`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Pinned toolchain Lean v4.33.0-rc1, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, goldbach-lean `09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000 and K=8452171/1250000 unchanged.

SOURCE_ONLY / UNEVALUATED: no Lean/Lake, no kernel replay, no transitive-axiom audit, no original87 certificate replay and no independent review. No full-input fixture staging, no CI dispatch, no Codex. The actual source may have elaboration/API errors until P0 checks it. This packet cannot change the parent's yellow status.

Next: square-test-specific fixed-j cutoff + power gap to finite target factor bound, then same true original87 ordinary exit-series/real residual integral; independently the primitive/centre budget, sixth filtered signed loss, original saved archive, two reserves and same-rho total remain.
