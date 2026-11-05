# P3.6 — signed full-modulus Fourier-tail transport (manuscript internal)

Base: ce5966dee57006353d23cc5960cbc24fa6ee38f5. Existing continuation branch: chatgpt/p3-internal-original-w-20261105.
Pinned paper: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, paper/source/modules/distribution-prime-product-completion-20261010.txt §4, (F), lines 153–171.

SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. P3.6 remains yellow.

## Actual new mathematical slice

The preceding ce5966 packet provided a W×HB real integrated derivative ledger. The manuscript first uses (F) to obtain a UNIFORM pointwise geometric Fourier cutoff error, and only then charges it AFTER the complete SIGNED modulus sum, separately at product b=T and b≠T. The latter arithmetic moment is NOT inferred from Fourier smoothness.

The new Lean candidate P3FullSignedModulusTail.lean defines the genuine previously-used exactCoprimeTest T q originalProducts, meaning

  1_(b ≡ T mod q) - 1_((b,q)=1)/phi(q)

with b equal to the COMPLETE original-group product. Define the positive kernel mass by adding the two nonnegative terms without dropping the coprime restriction. For finite admitted tuples t with signed coefficient c(t), one and the same rho(q), and two geometric weights w(t),v(t), the central source-only candidate is:

  |sum_q rho(q) sum_t c(t) w(t) K(q,t)
   - sum_q rho(q) sum_t c(t) v(t) K(q,t)|
    <= eps * sum_q |rho(q)| sum_t |c(t)| K_mass(q,t),

provided eps>=0 and |w(t)-v(t)|<=eps on the ACTUAL retained source.

This is proved in source from two finite triangle inequalities and the genuine kernel bound. The right hand side is a concrete count+coprime-mean mass, NOT an assumed PP error estimate. There is no individual sparse-root relative-error obligation. Signed coefficients and rho are not replaced by positive versions on the left side.

An exact finite source split isolates b=T from b≠T BEFORE using any arithmetic moment. At b=T and (q,T)=1, K(q,t)=1-phi(q)^(-1), which requires a distinct cardinality/coefficient bound; tau(0) is never evaluated. The previous exactCoprimeTest_after_HB identity is re-exposed so the source product stays equal to all HB slots multiplied exactly once.

No Fourier transform has been implemented in this packet. In particular, the pointwise eps estimate itself is not assumed as a proof of (F): it is an explicitly outstanding geometric input to the finite reduction. The shifted-divisor mass and exact b=T mass are manuscript-INTERNAL work, not new external axioms.

## Evidence

One additional 220-line Lean candidate with 11 definitions/theorems (including helpers) is stored as a Git blob. A fresh fetch of that blob found zero proof-escape tokens in comment-stripped code and balanced (),[],{}. A genuinely independent deterministic JS finite model ran 1,924 signed-source error cases and 1,924 exact/off-product mass splits; 650 models included at least one complete product exactly T. It preserved the exact count-minus-coprime-mean test and signed rho. These checks do NOT demonstrate Lean compilation or prove Fourier bounds.

No Lean/Lake, CI, Codex, kernel replay, axiom audit, new external input proof, PR, merge, manuscript edit, dependency change, or excluded 87-domain edit was performed.

## Next work

Prove the actual Fourier factorization: with non-2pi frequency xi, the manuscript uses exp(-i<x,xi>), D=sum_S ||∂_(2S)w||_1, |what(xi)|<=D∏(1+xi_j²)^(-1), integral |what|/(2*pi)^d<=D/2^d, and sup|w-w_H|<=dD/H. Pinned Mathlib uses exp(-2*pi*i<x,eta>) in its standard Fourier transform, so xi=2*pi*eta must be explicit if reusing it. Apply the genuine eps=dD/H once proved; then pay the separate full signed mass bounds, including product exactly T. W_T class admission and all other P3.6 yellow nodes remain open.

## Source-only status tree

BLUE: integrated W×HB derivative budget [ce5966].
BLUE: finite exact same-rho signed-error transport, explicit coprime kernel [this packet].
BLUE: mass decomposition by b=T versus b≠T without tau(0) [this packet].
YELLOW: actual W-family uniform admissibility; Fourier (F) integration and 2*pi normalization; full signed arithmetic mass bounds; source/causal/empty word/high rank; final same-rho PP.
EXTERNAL: recorded only, no implementation, no axioms.
