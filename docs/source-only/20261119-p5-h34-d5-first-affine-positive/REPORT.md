# P5.6 / h34 — D5 first affine positive source

Date 2026-11-19. Baseline \`fe9af18cb129b1da871104d8172d477e79df99c6\`.
Branch \`chatgpt/p5-h34-full-tagged-actual-fin-20261112\`.
Frozen manuscript \`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d\`.
Status PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

## New manuscript-internal proof source

On the literal first D5 affine interval [50/227,117/454], lower(u)=117/227-u and upper(u)=10/29. The proposed proof derives the exact log-argument floor 13/10 directly from geometry, checks log(13/10)>=1/4 using the existing RationalLogCertificate soundness interface with two rational terms, and uses u(1-u)<=1/4 to give an integrand floor of 1. The exact interval width is 17/454>37/1000.

The previous literal second piece [117/454,3/10] candidate has >=37/1000, and the original third piece stays nonnegative. The new full D5 candidate is >=74/1000, versus >=37/1000 previously. With the same three singleton, D6, D7, D8 candidates and the unchanged /5 normalisation, the full seven-term partial coefficient changes from >=143/2500 to >=323/5000=0.0646. This does not imply the required lambda>=0.13.

## Independent numerical feasibility diagnostic; NOT a formal proof

Independent mpmath high-precision integration and scipy.quad evaluation of the eleven actual one-dimensional pieces from the pinned P2 source agree: singleton0 ~0.1242120638603, singleton1 ~0.0119706814206, singleton2 ~0.0635323634074; D5 ~0.1805089366731, D6 ~0.1170471953127, D7 ~0.0417519208489, D8 ~0.1130122498292. Total ~0.652035411352185, lambda ~0.130407082270437. The required raw sum 0.65 is NUMERICALLY PLAUSIBLE with apparent margin only 0.0020354. This is no validated lower bound or finite Lean certification; it must not be tagged green.

## Validation and remaining work

GitHub connector verified repository permission/branch and read first-entry report, registry and external boundaries; native git HTTPS cannot resolve github.com, lean/lake/elan are not installed, and the fixed original import closure is absent locally. No Lean compilation, kernel replay, transitive axiom audit, CI dispatch or numerical finite proof certification was performed. Independent Fraction arithmetic confirmed 249700/191821>13/10, logSeriesLower(13/10,2)=3192/12167>1/4, and width 17/454>37/1000.

Outstanding internal obligations: certify the complete original seven-term 0.65 bound rigorously, fixed 20249/1000000 count intercept, frozen-F initial double-table seed, 430-round retention/Buchstab/bank CLOSED-CELL induction, full U3/U4 selected counts/root norm 7/2/owner and rejections, genuine PP/same-rho and native histories, integral–Theta–count connection, and one common nested 430+11 refinement. No manuscript, c/K, row norm 12, real alpha, same-Q, CI, toolchain or other branch is changed. Full h34 remains OPEN.

Next: build mathematically sound finite multi-cell log-integral lower certificates on the full seven true domains; compile the already accumulated Lean import chain when available.
