# P3.6 — finite-dimensional Fourier D subset algebra and genuine pointwise L1 bridge

Base: `87675003e0bb9f889225e7cc853bdf979886f2b9`.
Branch: `chatgpt/p3-internal-original-w-20261105`.
Packet: docs/source-only/20261105-p3-fourier-multidim-D/
Manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, prime-product completion §4 (F).
Mathlib pin: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. P3.6 remains YELLOW.**

## Actual manuscript-internal increment

1. `P3FourierSubsetExpansion.lean` proves for every finite dimension (including d=0) the exact finite subset expansion

    prod_i (1+xi_i^2) = sum_(S subset Fin d) prod_(i in S) xi_i^2.

   Also proves strict positivity, the analogous complex expansion, complex denominator norm equal to the real positive denominator, and the exact physical xi=2*pi*eta normalization. This uses the **pinned** Mathlib Finset.prod_one_add. No radial (1+|xi|^2) replacement is made.

2. `P3FourierDPointwise.lean` uses **genuine** Mathlib Fourier transforms over EuclideanSpace R (Fin d). The actual multivariate Fourier norm is bounded by the L1 integral of the transformed function from Real.fourier_eq and unit norm of the Fourier character. Then the signed sum of all doubled-coordinate derivative transforms plus the subset expansion yields the actual D-ledger inequality

    prod_i (1+xi_i^2) * ||Fourier(derivative_empty)(eta)|| <= sum_S integral_x ||derivative_S(x)||,

   and hence the physical-frequency product denominator bound. The numerator is the actual finite sum of derivative L1 integrals, NOT a postulated Fourier norm. The module defines actualMixedFamily in terms of the existing ordinary mixed (doubled S) derivative on Point d and states an exact specialization.

## Deliberately unproved internal obligation

The pointwise ledger theorem has the explicit hypothesis **CoordinateFourierIBP**:
for each subset S, the Fourier transform of the actual 2S mixed derivative equals (-1)^card(S) times the physical frequency square monomial times the Fourier transform of the base function. This is the manuscript's required coordinatewise Fourier integration-by-parts identity. **It has NOT been proved here**. It is not a new Lean axiom or a hypothesis equivalent to the final distribution estimate; it is a specific still-open differential/Fourier identity.

The EuclideanSpace/Pi Haar-measure conversion to the original physical Point d integrated W/HB budget is also still open, as are transform integrability and the Fubini/product-Cauchy and frequency-box H-tail calculation. The full manuscript (F) conclusions D/2^d and dD/H are NOT claimed. Actual W_T family membership, complete signed full-modulus arithmetic costs, exact product=T exception, causal/whole-atom permission, HB coverage, empty Gamma mother word, high-rank/enhanced cases and same-rho PP final assembly remain internal and open.

Source-only import paths are not production library registrations. P3.6 is not closed. No manuscript, toolchain/lock, production code, previous packet, PR, CI, main branch, full87 excluded work or external tracker is changed.

## Checks and resume

336 independent exact-rational subset and signed complex-frequency cases for dimensions 0..6 passed; an intentional wrong-sign negative control was rejected. 2,048 numerical checks of the 2*pi coordinate scaling passed. Static comment-stripped forbidden-proof-token and balanced-delimiter checks passed on both new Lean source modules. CHECKS.json is the receipt. These checks **cannot** verify Lean syntax, elaboration, continuous integration, kernel validity, or analytic Fourier identities. Lean/Lake, kernel replay, CI and axiom audit were NOT RUN.

Next: prove CoordinateFourierIBP for actualMixedFamily by repeated true coordinate Fourier differentiation using pinned Real.fourier_fderiv / fourier_iteratedFDeriv, and the EuclideanSpace/Pi Haar bridge. Then apply the pointwise lemma to the exact physical originalWD, integrate its product denominator with Fubini and pay H-tail. The resulting genuine epsilon may feed the existing same-rho full-modulus approximation only after its distinct arithmetic mass ledger is paid.
