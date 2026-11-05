# P3.6 — exact labelled original W_T / HB physical-source bridge

Base commit: `79d5ad9e166f553dc4377097d63e4d941a8e5b3b`.
Branch: `chatgpt/p3-internal-original-w-20261105`.
Manuscript pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`.
Source directory: `docs/source-only/20261105-p3-physical-original-w/`.

**SOURCE_ONLY / UNCOMPILED / KERNEL-UNVERIFIED / P3.6 STILL YELLOW.**

## Actual mathematical increment

The previous source-only packet at 79d5ad9 gave a finite mixed-Leibniz
product bound for *arbitrary chart-space* W: R^d -> R, provided W itself
has genuine compatible, continuous, uniformly bounded partial derivatives.
It did NOT construct a manuscript-original W_T on labelled prime variables.

The pinned prime-product completion, section 1, fixes a W_T on the
ORIGINAL k labelled prime variables, not on individual post-HB slots or
modulus-dependent filters. Section 2 retains the same group labels after
HB and uses individual slot coordinates z_i = log(n_i/U_i). This new packet
keeps those labels and defines the physical pullback, without changing
what the arbitrary original W_T means:

  P_j(n) = product_{i:group(i)=j} n_i,
  n_i(z) = U_i exp(z_i),
  W_pull(z) = W_T( (P_j(n(z)))_j ).

It proves algebraically (in uncompiled Lean proof bodies) that:
- Every n_i>0 with U_i>0 is recovered from z_i=log(n_i/U_i).
- The true individual dyadic rectangle U_i<=n_i<=2U_i maps to
  0<=z_i<=log 2; the fixed compact extension is unchanged.
- Original group log coordinates are exactly
  log P_j(n(z))=log groupBase_j + sum_{group(i)=j} z_i.
- Every original group gets ALL of its HB slots, including empty
  groups, and product_j P_j = product_i n_i exactly.
- The old withOriginalW *with W=W_pull* equals W_T(P(n)) times the
  existing physical U5/group-hat/complete-trim/HB log-ratio multiplier
  on the genuinely admitted scalar core.
- The same equality holds directly at physical n, after applying
  the genuine logarithmic inverse, and under arbitrary finite signed
  arithmetic tests F(q,t) with the SAME rho(q) on both sides.

The new `exactCoprimeTest` records the precise algebraic
count-minus-coprime-mean kernel, with phi(q)=Nat.totient q and the
complete ORIGINAL labelled product; the natural-group product identity
shows both count and mean use the same complete HB product.
In actual PP use q>=1 and (q,T)=1. This does not claim an HB
factor tuple is a tuple of primes, or prove the convolution coverage.

## What is deliberately NOT proved

This is the previously missing *physical original W_T pullback* and
positive-scale inverse, not a proof of the uniform derivative class.
The old budget D_(W*HB)<=C M (m+1)^(2d), or its E+2dB polylog form,
remains conditional on primitive W mixed-derivative hypotheses.
The original manuscript's allowed integrated Euler derivative norms
versus the stronger existing pointwise norm class still need an exact
per-family comparison. No arbitrary original W_T is declared smooth
simply by passing to logarithmic variables.

Fourier transform/inversion/tail, full signed modulus sum, the b=T
exact-product exception, causal/whole-atom licence, full HB coefficient
coverage, empty Gamma mother words, high-rank/enhanced cases and final
same-rho PP assembly remain manuscript-INTERNAL obligations.
No external theorem is newly implemented or postulated.

No physical/auxiliary modulus-level substitution, no changed rho,
no replacement W by a residual quotient, no changed strict endpoint,
no change of smoothing order or hidden relative root-fibre requirement.

## Checks and evidence

Two new Lean proof files: P3PhysicalOriginalW.lean and
P3PhysicalOriginalWInsertion.lean. Both are uncompiled. The GitHub
blobs were fetched back and scanned after creation: zero forbidden
proof-escape tokens in comment-stripped content, and balanced (),[],{}.
An independent reproducible Python finite model, run in the container,
passed 750 deterministic cases (positive slot inversion, empty groups,
genuine group sums, nonlinear arbitrary W, complete-product conservation,
and the EXACT totient coprime count-minus-mean kernel). An independent
JavaScript implementation passed another 750 cases. These tests only
check finite algebraic models, NOT the Lean elaboration or the analytical
conditions. A GitHub tree/commit/ref confirmation is required separately
before calling this packet published.

No Lean, Lake, CI, kernel replay, theorem audit, numerical producer,
Codex or PR was run; no green status. No toolchain, manuscript, older
packet, production module, full87 code, tracker or other automation changed.

## Next concrete manuscript-internal action

Read the exact W_T families actually consumed by the finite PP compiler,
including their signed scalar labels and normalized/log Euler derivative
norms. Map each one to the new `pulledOriginalW`, distinguishing the
pointwise-supremum subclass of 79d5ad9 from the manuscript's integrated
norm class. Prove the appropriate product inequality rather than assuming
the desired whole-chart D norm; then implement Fourier (F) with the
correct transform normalization and absolute tail. Keep the b=T term
separate when paying the FULL modulus sum.

## Scoped status

    蓝｜positive slot scale/log inverse and actual dyadic chart source
    蓝｜unchanged original labelled W_T physical HB pullback
    蓝｜all group products / complete modulus / exact coprime kernel algebra
    蓝｜same-rho signed finite insertion on admitted physical source
    黄｜actual original W_T derivative family admission / stronger-vs-integrated norms
    黄｜Fourier (F), arithmetic summation and exact-product b=T branch
    黄｜causal, full HB coverage, empty words, high-rank and total PP
    稿外｜only recorded; not implemented
