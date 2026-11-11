# P1.4: actual centre-prime invoice at the frozen C_N / H_N normalization

Base: 995bcb97375d434c023f38d9e61e4698d71b0744 on chatgpt/p1-full87-centre-sqrt-envelope-20261111. Task branch: chatgpt/p1-full87-centre-frozen-hn-20261111.
Proof candidate: P4AOriginalFull87CentreFrozenHN.lean.

## Actual mathematical increment

The previous candidate establishes the original full87 physical centre invoice
B_centre(N) <= 4*(Nat.sqrt N+2)*Nat.log 2 N. Here the denominator is no
longer an arbitrary H: it is the exact frozen manuscript normalization.

The fixed native module MathlibNt/SieveTheory/Arithmetic/LiuSingularSeries.lean
defines liuSingularSeries N = liuUniversalProduct * liuCorrection N, where
liuUniversalProduct is the genuine odd-prime infinite product C_2 > 0 and
liuCorrection N is the product over DISTINCT odd prime divisors p of N of
(p-1)/(p-2). This is exactly manuscript 9731290e §statement
eq:current-normalization C_N. Native theorems liuUniversalProduct_pos,
liuUniversalProduct_le_liuSingularSeries, and one_le_liuCorrection provide
the denominator's positivity and uniform lower factor.

WARNING: the older native 'singularSeries N' is a finite, sieve-normalized
proxy. At even N it is twice the genuine odd-prime series divided by an
Euler tail. Using it uncorrected here would change the frozen H_N. The NEW
source imports the genuine native Liu product explicitly.

For N>=4 the actual invoice has the stronger real upper bound
  B_centre(N) <= (8/log(2))*sqrt(N)*log(N).
The candidate proves the pointwise frozen-scale estimate
  B_centre(N)/H_N <= 8/(C_2*log(2))*log(N)^3/sqrt(N).
The final candidate proof uses the pinned mathlib lemma
isLittleO_log_rpow_rpow_atTop for log(N)^3=o(N^(1/2)).
This is an all-target eventually-zero result, stronger than restricting
to even N. There is NO new PP or Mertens/BV supplier.

No numerical reserve was paid: the statement is only centre-prime error
o(H_N), not the total sixth/eighth sharp-PP or ordinary saving.

## Verification and exact limits

Level: SOURCE_ONLY / UNEVALUATED / UNCOMPILED. The execution container
has no lean, lake or elan and cannot access the fixed dependency tree;
no type checking/kernel replay/transitive axiom audit/independent review.
The source is a candidate and can contain Lean elaboration errors. Static
formula and mathlib/native theorem source inspection are not compilation.
No CI, Codex or additional resources were invoked.

Fixed paper pin 9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/manuscript-body.tex blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79.
Lean v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1;
native subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958.
c=49044063/25000000; K=8452171/1250000. No pins changed.

Still open: actual source-only import placement and fixed Lean compilation;
two independent old/new signed sharp PP admissibility and quantitative
bounds; ordinary continuation to actual residual integral; parent-gap
weighted invoice; saved87 numerical witness; finite/raw/filtered,
rank9, changed/tagged; independent compiler/density reserves and same rho.
P1.4 remains YELLOW.

## This run: actual environment and synthetic bounds check

- Executed `lean --version`, `lake --version`, `elan --version` on the available execution container; each returned exit code 127 (command not found). No source-only dependency closure was mounted. The new source was NOT elaborated, kernel-replayed or axiom-audited.
- Remote readback confirmed the exact source Git blob 3e8c7c57d392c531562c1eb2753a73ac01431705 and all four accompanying packet blob hashes; branch HEAD at initial source commit 2ddba3208f2a8c24c4e0a99ae833530f004c769f.
- Independently enumerated 999 even N=4,...,2000. The finite centre coprime-divisor invoice satisfies the explicit real sqrt-log bound and frozen H_N-ratio envelope on all tested cases, zero failures. For this synthetic check only, C_2 was numerically truncated at odd primes below 15000 (0.66016598342102); this is NOT the native infinite product certificate, nor saved87 replay, nor a proof of convergence.
- Read the exact native LiuSingularSeries source at the fixed pin: liuUniversalProduct_pos, liuCorrection, liuSingularSeries_source_formula and the explicit warning that the finite proxy differs by a factor of two. Read matching mathlib isLittleO_log_rpow_rpow_atTop and Nat.pow_log_le_self. No input boundary changed.
