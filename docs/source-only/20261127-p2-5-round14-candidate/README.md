# Two remaining tactic errors from round 13

The round-13 normal check reached the final slot-15 identity and the monotonicity proof for the selected H3 cap. The errors that remain are localized to those proofs. Both production theorem statements, both import lists and the 377-module source graph are preserved. [Compiler output](../../verification/20261127-p2-5-resumed/p2-round13/COMPILE.log)

At slot 15 the existing splice absorption theorem has reduced both sides to the same sixth policy, with its frozen cap written once as a lambda and once as a partial application of `sixthSourceLevel`. The definition of `sixthSourceLevel` is exactly that lambda. The candidate removes the unused simp argument reported by Lean and finishes the remaining equality by reflexivity. [Definition of the sixth level](../../../ImbalancedChen/P4AOriginalActualElevenSixthCandidate.lean#L51-L58)

In the positive H3 case, unfolding `selectedCap` requires the original witness `h : selectedH3 N lambda6 pre`. The previous proof destructured `h` before simplifying the conditional. The candidate simplifies the conditional first, then destructures the same witness and applies the existing strict-improvement consequence. The accepted 174-declaration supplier remains in the prior graph and its theorem is reused. [Source delta](SOURCE_DELTA.patch) · [Witness supplier](../../../ImbalancedChen/P4AOriginalFirstFailureH3SourceSemantics.lean#L689-L697)

Both steps preserve the dependence on the actual sixth ancestor used at rank eight. The November 6 appendix gives the corresponding comparison between the inherited and selected caps. [Sieve appendix, lines 202–217](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex#L202-L217)

Round 14 retains all existing normal and owned reuse checks before and after execution. The two repaired owners retain audit priority across the complete five-root, 69-target scope. Source-only status covers the candidate until actual P2 compilation. [Selection](SOURCE_SELECTION.json) · [Configuration](RUN_CONFIG.json) · [Offline result](OFFLINE_VALIDATION.log)
