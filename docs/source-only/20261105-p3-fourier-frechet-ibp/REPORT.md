# P3.6 — genuine finite-dimensional Frechet Fourier IBP

**BASE:** c25de11034e671315b53bd9ee7894ba8ee855e24
**BRANCH:** chatgpt/p3-internal-original-w-20261105
**PAPER PIN:** UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, distribution-prime-product-completion-20261010.txt §4 (F).
**MATHLIB PIN:** e4c91783ca8e6a7c693ae624ade32fd22d4e43c1
**STATUS:** SOURCE_ONLY / UNCOMPILED / KERNEL-UNVERIFIED. P3.6 remains YELLOW.

## Manuscript-internal mathematical change

The previous c25de11 packet identified a precise open analytic dependency,
CoordinateFourierIBP, for the older ordered repeated coordinate derivatives.
This increment proves its genuine FRECHET-DERIVATIVE analogue rather than
assuming a higher-dimensional Fourier derivative relation.

For any n ordered directions v_j in EuclideanSpace R (Fin d), any
ContDiff R n complex function f with integrable Frechet derivatives of
orders 0,...,n, the theorem fourier_directional_derivative proves

    Fourier(x |-> (D^n f)(x)[v_1,...,v_n])(eta)
      = (-2*pi*I)^n * product_j (-<eta,v_j>) * Fourier(f)(eta).

It uses the pinned Real.fourier_iteratedFDeriv theorem and the pinned
Real.fourier_continuousMultilinearMap_apply theorem, so this is true
Fourier integration by parts on the actual Euclidean Fourier domain,
not finite-polynomial stand-in calculus and not a conditional assumed
Fourier-transform equality.

subsetDirections uses the exact older doubled S list with a unit
coordinate vector for EVERY occurrence; subset_frechet_fourier gives the
genuine n=2|S| Fourier formula and inner_basisDirection identifies the
real coefficient with the physical coordinate eta_i. The previous
pointwise D ledger is deliberately untouched.

## What this does not close

- Frechet directional derivatives must STILL be identified with the
  original ordinary coordinateDeriv/mixed functions on Point d (and
  complexification of the original real w).
- The doubled-list multiplier must be simplified into exactly
  (-1)^card(S) * product_i in S (2*pi*eta_i)^2. Numerical regression
  is not the missing Lean equality.
- The integral/measure bridge EuclideanSpace R (Fin d) versus Point d,
  compact-support integrability/ContDiff instances for actual original
  W x HB, and the physical originalWD L1 budget are NOT established.
- Product Fourier L1/Fubini and box H-tail, actual W_T family admission,
  signed full-modulus arithmetic mass including product=T, causal,
  all HB sources, empty Gamma words and final same-rho PP are open.
- No Fourier decay, arithmetic distribution or equivalent PP assumption
  has been added as a new axiom, fact, or structure field.

## Validation

The source contracts and exact scalar algebra were checked independently:
the even-order 2S directional coefficient was tested for all subsets in
d=0..6 over a finite set of integer coordinate frequencies, including
zeros and negative values. Static comment-stripped forbidden-proof-token
and balanced-delimiter checks were run. CHECKS.json records counts.

The exact pinned definitions were read at
Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:
  Real.fourier_iteratedFDeriv,
  VectorFourier.fourierPowSMulRight_apply;
Mathlib/Analysis/Fourier/FourierTransform.lean:
  Real.fourier_continuousMultilinearMap_apply;
Mathlib/Analysis/InnerProductSpace/PiL2.lean:
  EuclideanSpace.single and inner_single_right.

There is NO Lean/Lake elaboration, CI, kernel replay, transitive axiom
audit, independent reviewer, or new green node. The local source-only
import path still needs the separately controlled build environment.
This packet does not alter other files or the excluded full87 work.

**NEXT:** Prove true coordinateDeriv ↔ directional Frechet evaluation
by coordinate shifts and differentiability, then exact signed-square
multiplier and Haar measure bridge; apply to originalWD, and only then
integrate the H-tail and feed the same-rho full-modulus ledger.
