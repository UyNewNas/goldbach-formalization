# P1.4 input boundary — strict original upper quotient removes the false AP tail obligation

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes commit 9731290e8f53cffda44129906cde6a965eaa869b; paper/source/manuscript-body.tex blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79. Manuscript formula eq:current-PP was read in the previous packet. Status: MANUSCRIPT_READ_NOT_INDEPENDENTLY_AUTHENTICATED_NOT_APPLIED.

External asserted form remains the SAME-rho signed estimate
  sum_q rho_N(q) [sum_(labelled prime products congruent N mod q) W_N
                 - X_W^(q)/phi(q)] = O_(A,W)(N*(log N)^(-A)).
W_N must be fixed, smooth, admissible for labelled original primes and common geometric parameters, without a new q-dependent sharp divisibility filter. All exact coefficient, factorization, fixed-before-N quantifier and coprime-mean requirements remain outstanding; we did not prove or install this external theorem.

NEW internal finite arithmetic candidate:
The original full upper quotient interval forces 2q>N for every original admitted q=a*(p::pre).prod. The actual receiver r=N-P always satisfies r<=N. A strict proper receiver multiple q|r, q<r implies 2q<=r, contradiction. Hence the previously exposed non-shell full-q AP correction is exactly ZERO on the ACTUAL original upper quotient, separately for each allowed occurrence and each signed PLUS-beta coefficient. No geometric zero measure or cap monotonicity is involved. It is not zero for arbitrary q<=N/2 or for lower-half correction fibres.

The new physical after-lower identity is a finite, unevaluated Lean candidate with the original same parent/occurrences:
   physical_stopped - lower_once = frozen_mean(mean) + frozen_true_full_Q_AP(mean).
The function mean(b) is still arbitrary. This equality does not identify the real manuscript rho_N(q), nor ensure a common PP smooth W_N or an H_N saving. Avoid treating it as a proven asymptotic result.

No new external assumptions, theorems, axioms, or hidden target-equivalent fields. Frozen toolchain Lean v4.33.0-rc1 / mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 / native 09b97db5764ade1246bfb77206baa1b124760958; c and K unchanged. Status SOURCE_ONLY / UNEVALUATED / UNCOMPILED. lean/lake/elan exited 127.
