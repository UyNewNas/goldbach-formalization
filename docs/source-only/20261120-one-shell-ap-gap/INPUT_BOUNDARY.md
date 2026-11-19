# P1.4 input boundary — one reflected shell is not a full AP

## Manuscript pin and exact external theorem claim
- Repo \`UyNewNas/chen-imbalanced-semiprimes\`; commit \`9731290e8f53cffda44129906cde6a965eaa869b\`; source \`paper/source/manuscript-body.tex\`; blob \`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`.
- Section "From the local estimate to prime products", formula \`eq:current-PP\` (read at frozen pin). For fixed finite smooth \`W_N\` on labelled original primes, each at least \`cN^a_*\`, product \`O(N)\`, fixed geometric restrictions and admitted *signed* coefficient \`rho_N(q)\`, the manuscript asserts:
  \`sum_q rho_N(q) (sum_{p1...pk≡N (mod q)} W_N(p1,...,pk) - X_W^(q)/phi(q)) = O_{A,W}(N(log N)^(-A))\`,
  where \`X_W^(q)=sum_{(p1...pk,q)=1} W_N\`. Same \`rho_N\` in both parts. Status: MANUSCRIPT READ, NOT INDEPENDENTLY AUTHENTICATED OR IMPORTED. No new analytic theorem is assumed.
- Fixed denominator and constants: \`c=49044063/25000000\`, \`K=8452171/1250000\` unchanged. Fixed Lean/mathlib/native versions in REPORT.

## Newly proved in source-only candidates, not Lean kernel
- \`actual_full_Q_AP_eq_shell_plus_outside\`: true finite primitive AP count for \`Q\` equals the indicator at \`N-Q\` plus the *same* AP with that one shell erased.
- \`original_signed_carrier_eq_full_AP_sub_outside\`: original PLUS-beta signed room equals actual AP count term at \`Q=a*b\` minus explicit signed outside-shell term, with original \`mean(b)\`.
- \`original_signed_carrier_event_eq_full_AP_sub_outside\`, \`frozen_signed_carrier_eq_full_AP_sub_outside\`, \`physical_after_lower_eq_mean_plus_full_AP_minus_shell_tail\`: original fifth signs, true ordered sixth occurrences, sharedRankFour and frozen selector are reused; lower receiver subtracted once.

## Precise non-equivalences and still unfulfilled manuscript-internal adapters
1. \`1_{N-ab∈carrier}\` is ONE shell of \`P≡N (mod ab)\`, not the AP count. For N=70 and q=3, there are seven primitive carrier primes in the AP, but only the shell P=67. The other six terms are not geometric null sets.
2. Even the full-q \`AP_N(ab)\` counts UNSMOOTH SINGLE additive primes. It is NOT the general fixed smooth labelled-prime-product chart \`W_N\` in \`eq:current-PP\`. No identification of \`rho_N\` is established merely by q=a*b.
3. \`mean(b)\` remains arbitrary and rough-b dependent, not \`X_W^(q)/phi(q)\`. The small a factor and true complete physical modulus must be handled without changing the original coefficient or quantifiers.
4. The omitted-shell tail has signed beta and raw/licensed signs and cannot be assumed nonnegative, negligible or individually bounded by the manuscript's signed global PP estimate.
5. Actual admissible smooth chart partition, fixed-before-N parameter order, coefficient-class/factorization hypotheses, remainder cost and same-rho \`H_N\` payment remain UNPROVED; no external PNT/Mertens/BV/spectral proof is implemented.

All analytic inputs remain READ_NOT_CERTIFIED_NOT_APPLIED. The new theorems are SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
