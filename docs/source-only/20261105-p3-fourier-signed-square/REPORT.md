# P3.6 — signed-square frequency multiplier for original doubled S

**BASE:** 02b1f8bfeb6b4b3ad4dc8bbfe74696728cb67d10
**BRANCH:** chatgpt/p3-internal-original-w-20261105
**PAPER:** UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, prime-product completion §4 (F).
**MATHLIB:** e4c91783ca8e6a7c693ae624ade32fd22d4e43c1
**STATUS:** SOURCE_ONLY / UNCOMPILED / KERNEL-UNVERIFIED. P3.6 YELLOW.

## Manuscript-internal increment

The preceding 02b1f8b packet supplied genuine finite-dimensional Frechet Fourier differentiation, but did not prove the literal (-1)^card(S) multiplier for the older doubled-list order. This packet defines the physical one-coordinate Fourier wave and proves its square is the **negative** physical frequency square. The recursive doubled-list proof retains the exact two copies of each coordinate. The finset theorem then gives

    prod_{i in doubled(S)} (2*pi*i*eta_i)
       = (-1)^card(S) * prod_{i in S} (2*pi*eta_i)^2.

The empty subset and zero frequencies are included. The proof uses only elementary complex algebra, the pinned Complex.I_sq identity, and Finset.prod_map_toList. It does not assume a Fourier transform identity, derivative bound or PP estimate.

New declarations: coordinateWave, coordinateWave_pair, coordinateWave_from_real_phase, doubled_wave_list, doubled_wave_finset, signed_square_is_frequency_monomial.

## Actual boundary and next work

The multiplier here is exactly the one obtained by multiplying the previous single-coordinate factor in the Frechet Fourier formula. The older Point d / ordinary mixed equals EuclideanSpace Frechet directional derivative is STILL OPEN. The equality between the preceding theorem's scalar powers and the corresponding ordered Fin-indexed product is also to be wired to the actual transformed function. The Haar/measure bridge, mixed-L1 ledger equality, full Fourier (F) L1 and H-tail, original W_T family admission and complete-modulus arithmetic mass (including product=T) are OPEN.

No changes to original rho, physical coefficient, geometric label, modulus, mean or causal history. No external analytic inputs are proved or reclassified. The excluded full87 work is untouched.

## Checks

An independent integer-complex model checked 127 exhaustive dimension/subset masks for d=0,...,6 using signed imaginary wave factors; 52 wrong-sign controls were rejected. Source-string delimiter and forbidden proof-token checks succeeded. These finite tests are not a Lean elaboration or a proof of the analytic bridge.

Lean/Lake, kernel replay, trust audit and CI were NOT RUN, by scope instruction; no green node. Next task: prove the Point d coordinate shift/Frechet bridge, then connect this signed-square equality to the earlier CoordinateFourierIBP on the original mixed functions, followed by measure and Fourier H-tail.
