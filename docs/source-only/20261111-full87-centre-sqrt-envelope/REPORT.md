# P1.4: elementary square-root/log envelope for the actual centre-prime bill

Continues GitHub-confirmed `d4a832ca76e33e79638dc52c4a9bd6da7f6095a3` (`chatgpt/p1-full87-centre-coprime-divisors-20261111`). This packet does not revisit the original87 geometry, replace the physical rho or create an extra discrepancy invoice.

## Substantive internal argument

The immediate prior full-modulus physical result gives, for nonprime N:
`B_centre(N) <= 2 * sum_{P prime, P|N} #(d|N-P, gcd(d,N)=1)`.

The NEW Lean candidate proves without external analytic inputs:

1. An elementary factor-pair injection into two intervals yields `tau(m) <= 2*(floor(sqrt(m))+2)` for all m, including zero.
2. The *literal* `centreDivisorPrimes N` is a subset of the distinct entries of the existing `Nat.primeFactorsList N`. Every entry is >=2. Therefore `2 ^ (centreDivisorPrimes N).card <= N` indirectly via the full factor list, giving `(centreDivisorPrimes N).card <= Nat.log 2 N` for N!=0.
3. Monotonicity `sqrt(N-P) <= sqrt(N)` and a finite sum supply the actual **uniform, non-asymptotic** estimate

   `B_centre(N) <= 4 * (floor(sqrt(N))+2) * floor(log_2 N)`   (N != 0).

4. This particular bound is substituted into the previously established SAME sixth-minus-eighth sharp receiver identity. The two original policy-specific signed sharp PP estimates remain independent premises. The modulus-prime term already cancelled during sharp recentering is not paid again.

The numerical constant 4 here refers to the finite combinatorial invoice, NOT the manuscript reserve coefficient K or the Chen c. No sign or occurrence is altered: the previous full87 physical-rho exact fibre identity is still the source of the bill.

## Normalized scale, deliberately separated from Lean verification

The frozen manuscript defines `H_N = C_N * N / (log N)^2` and `C_N = C_2 * product_{odd p|N} (p-1)/(p-2) >= C_2 >0`. Thus the new finite envelope, **once elaborated**, is mathematically `O(sqrt(N)*log(N)) = o(H_N)` for even N -> infinity, because `log^3(N)/sqrt(N) -> 0`. This is elementary calculus and finite arithmetic, not PNT, BV or Mertens. The Lean file does **not** pretend to contain a fully typechecked `isLittleO` proof at the exact frozen `H_N` definition, which remains to be supplied and checked. No numeric reserve amount is paid at this stage.

This closes the *paper* growth-order bottleneck for the finite centre correction, but DOES NOT establish either old/new sharp PP admission, ordinary source-to-integral asymptotic, actual weighted parent-gap, saved87 witness or any full P1.4 success.

## Fixed provenance and checks

Pinned paper: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; fixed Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000.

Pinned mathlib source inspected for `Nat.lt_succ_sqrt`, `Nat.sqrt_le_sqrt`, `Nat.le_log_of_pow_le`, `Nat.prod_primeFactorsList`, `List.toFinset_card_le`, `Finset.card_image_le`, `Finset.card_union_le`. Exact matching signatures still require Lean elaboration. Local tool check has no lean/lake/elan or pinned .lake closure. Level SOURCE_ONLY / UNEVALUATED / UNCOMPILED; no kernel replay, transitive axiom audit, independent review or CI. No synthetic stress test is treated as proof.

## Remaining exact obligations

- Elaboration and actual compilation of the NEW combinatorial lemmas and entire dependency closure at fixed pins; remove any type errors found.
- Formal real-valued and asymptotic bridge of the true frozen `C_N, H_N` (C_2 positive and factors >=1), including parameter order. No reserve value has been numerically or kernel-certified.
- Each actual physical sixth/eighth signed sharp PP admission: full-q support cutoff, fixed smooth-singleton, integer X, endpoint and SAME normalization; external PP theorem REGISTERED_NOT_PROVED/NOT_CALLED.
- Ordinary continuation asymptotic to actual parent residual integral, weighted parent gap, saved87 witness replay, lower/upper q, raw/finite/filtered, rank9, changed/tagged and TWO independent compiler/density reserves.

P1.4 parent remains YELLOW.
