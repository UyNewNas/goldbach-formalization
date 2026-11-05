# P3.6 — genuine Fourier inversion/cutoff and first derivative-decay factor

Base commit: `4120ebe4d4948e7b7da81cc092e69bf27a82731c` (same-rho signed full-modulus tail).
Continuation branch: `chatgpt/p3-internal-original-w-20261105`.
Source packet: `docs/source-only/20261105-p3-fourier-inversion-seed/`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`;
`paper/source/modules/distribution-prime-product-completion-20261010.txt`, §4, equation (F).
Pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED. P3.6 remains YELLOW.**

## Actual new manuscript-internal proof bodies

1. `P3FourierCutoffIdentity.lean` uses the REAL pinned Mathlib Fourier transform on a
   finite-dimensional real inner-product space, the actual Fourier inversion theorem
   (which requires integrability of both f and its transform), and the measurable
   set decomposition of a Bochner integral. It establishes that the unretained
   inverse Fourier frequencies give the *exact* truncation error, and hence
   `norm(f(x)-truncatedInverse(f,s,x)) <= integral_(s-complement) norm(F(f)(xi))`.
   There is no assumption that this tail satisfies the required bound. The
   completely original `signedSource` and `fullModulusMass` are reused in
   `same_rho_signed_fourier_cutoff`: the REAL PART of the actual Fourier
   truncation is passed into the original count-minus-coprime-mean signed sum,
   with precisely the same rho, originalProducts, and admissible finite source.
   The explicit geometric tail-mass premise is not an arithmetic distribution
   premise and is not renamed PP.

2. `P3FourierOneDimDecay.lean` proves the genuine one-variable analytic
   derivative identity using the pinned
   `Real.fourier_iteratedDeriv` theorem. It derives

       (1+(2*pi*eta)^2)*norm(F f eta)
           <= integral norm(f) + integral norm(iteratedDeriv 2 f)

   for C² f with actual derivatives of orders 0,1,2 integrable.
   The exact frequency mapping `xi=2*pi*eta` yields the manuscript
   `(1+xi^2)^(-1)` factor with no missing 2*pi. The coordinatewise
   equality of the d-factor denominators is also supplied as finite algebra.
   The one-variable Cauchy integral is imported from pinned Mathlib:
   integral_R 1/(1+xi²) = pi.

These are genuine Fourier prerequisites, not an arbitrary abstract
`FourierDecay` structure with the desired conclusion as a hypothesis.
No separate Fourier approximation axiom was introduced.

## Important scope boundary

The full manuscript (F) still requires constructing the **multivariate**
coordinatewise repeated integration-by-parts / Fourier derivative identity for
the actual compact supported `Point d` chart, matching that chart with
`EuclideanSpace ℝ (Fin d)`, deriving
`|what(xi)| <= D*product_i(1+xi_i²)^(-1)`, and proving the
Fubini/product-tail integration and frequency-box measurability. The exact
normalization should be integral hat/(2*pi)^d <= D/2^d and
sup error <= d*D/H. These are NOT proved by this packet.

The first theorem requires integrability of the transform, not merely
`ContDiff`; the required integrability for each actual physical W×HB
chart is still to be discharged from the full multivariate derivative
budget. There is no Fourier-driven arithmetic mass estimate and no
charge for the product=T exception. The primitive source class admission
of every original W_T family, whole-atom/causal licences, HB coverage,
empty Gamma mother word, high-rank/enhanced cases and actual same-rho
PP assembly all remain internal open items.

No external prime distribution, PNT, Mertens, BV, SW, spectral,
Kloosterman, shifted-divisor, or medium convolution theorem is implemented.
The inherited external analytic input remains recorded only.

## Verification, provenance and limits

The exact previous branch HEAD and commit tree were read; the previous
report, finite signed kernel file, integrated-W budget and pinned paper §4
were inspected. The pinned Mathlib FourierTransformDeriv, FourierTransform,
Inversion, and ImproperIntegrals APIs were checked. In particular pinned
Mathlib has the one-variable global `integral_univ_inv_one_add_sq`, but does NOT
have the later convenience result `integral_univ_inv_one_add_mul_sq`;
the latter is deliberately not used.

The two new candidate files were checked via source comment-stripped scans
for prohibited proof escapes and delimiter balance. 2,048 deterministic
floating-point cases checked only the frequency coordinate identity;
these are independent arithmetic spot checks, not Lean or analytic proofs.

NO Lean/Lake compilation, kernel replay, transitive axiom audit, CI,
Codex, PR, merge, production edit, mathlib upgrade, manuscript edit,
or excluded full87 edit was performed. `VERIFY.lean` is unexecuted.
Full P3.6 remains yellow; new nodes are at most blue SOURCE ONLY.

## Next concrete action

Prove the multivariate mixed-coordinate Fourier-derivative relation
in the manuscript xi normalization, then derive the actual D product
majorant, its integral and the maximal-frequency tail (paying the
2*pi^d normalization and all boundary factors). After that, feed the
genuine eps into the already-written same-rho signed source lemma
and complete the separate b=T and b!=T arithmetic mass estimates.
