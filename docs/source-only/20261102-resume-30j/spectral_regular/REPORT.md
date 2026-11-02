J / spectral_regular — actual cusp-one source and regular finite-cut payment

Status: substantive local source/proof candidates written; full original regular Eq24 target OPEN. Both Lean files are uncompiled, kernel_verified=false, formal_credit=0. This is author source inspection, not independent review. Only J/spectral_regular was written. No compiler, build, CI, finite certificate execution, Git operation, subagent or quota call was used.

The task row, batch README, current manuscript at lines 116–255, detailed medium module at lines 299–405, classical correspondence at lines 20–139, explicit regular-polynomial derivation, and the I spectral_eq24 and H medium predecessors were read. The original global c=49044063/25000000 and K=8452171/1250000 are unchanged. The variable K in the new analytic file is a spectral height cutoff, not that global sieve constant.

What is proved locally

`Part3OriginalNonzeroCuspOneSource.lean` starts from the existing physical frequency

    (D/c) * psihat(m*D/c) * S(m*inverse(z),a*y;c).

For each actual physical unit u modulo c, it constructs integers

    alpha = representative(inverse(z)*u),
    k = -representative(inverse(u)),
    A*c - z*k*alpha = 1,

and the literal integral matrix [[A,alpha-A],[z*k,c-z*k]]. The determinant equation is derived in ZMod from the original c,z coprimality gate. Its Gamma0(z) membership is proved, and its normalized cusp-one lower-left entry is exactly sqrt(z)*c, positive for c,z>0. The right parabolic is proved equal to the existing cuspOneMatrix conjugate at the actual width z.

`physicalRepresentative_surjective_double_cosets` and `physicalRepresentative_injective_double_cosets` prove that these physical units enumerate the genuine positive-modulus double cosets. They reuse the already implemented zero-cusp classification via right multiplication by the integral T; they do not merely call a newly defined sum a generalized Kloosterman sum. The representative is not required to match the earlier arbitrary Bezout representative literally.

`physical_kloosterman_eq_cuspOne` proves the exact reverse chart conversion

    S(m*inverse(z),n;c) = e(-n/z) * cuspOneMatrixSum(z,c,m,n).

Every phase on the right is evaluated on the actual normalized real matrix. Consequently `physical_frequency_eq_cuspOne` retains the exact D/c multiplier, psihat argument, signed m and y, and moving residue. Its norm theorem removes only a proved unit-modulus phase. `original_nonzeroKernel_eq_cuspOne` is a direct consumer in I's actual complementary nonzeroKernel: the original smooth c carrier, original c-unit gate and every m!=0 are retained. This identity does not require truncating or rearranging an unproved series. It does not repay I's m=0 or y=0 branches.

`Part3RegularCumulativeShellPayment.lean` proves the internal regular height summation from two positive cumulative quadratic-form bounds and pointwise transform estimates. There is no bilinear spectral-return or Eq24 hypothesis. If the two cumulative energies at height T>=1 are at most

    (T^2+u)*A2,   (T^2+v)*B2,

write G=sqrt(((K^2+u)*A2)*((K^2+v)*B2)). On high heights assume only the classical transform shape C*(t^(-5/2)+Y*t^(-3)), expressed with positive denominators. The shell (4^j*K,4^(j+1)*K] is bounded by

    16*C*G * [ (1/2)^j/(K^2*sqrt(K)) + Y*(1/4)^j/K^3 ].

The two exact geometric series give a total high-shell bound

    C*G * [ 32/(K^2*sqrt(K)) + (64/3)*Y/K^3 ].

The proof uses finite Cauchy on the two quadratic forms, derives the shell supremum from the pointwise transform estimate, proves the finite geometric bounds, and proves exact endpoint ownership in the telescoping cutoff identity. Fourfold height intervals collect every other ordinary dyadic shell; they do not change the source or discard any height.

For K=max(1,2Y), the tail cost is at most 128/(1+Y), and K^2<=4*(1+Y^2). Including the low-height bound C*(1+abs(log Y))/(1+Y) gives `regular_R1_finite`:

    norm(sum on |t|<=4^J*K of H*A*conj(B))
      <= 516*C*(1+abs(log Y))/(1+Y)
           *sqrt(((1+Y^2+u)*A2)*((1+Y^2+v)*B2)).

This holds uniformly in every finite spectral cut and J. The constant 516 is absolute and introduces no residue, auxiliary-index or height power. The finite absolute-sum theorem is stronger than the displayed complex-sum bound. A continuous-measure exhaustion and an infinite automorphic sum are not silently inferred.

The new consumer uses the existing `PacketData.completed` and `signedCoefficient(modePacket ...)`, not substitute coefficient sequences. `originalM_coefficient_norm` proves the m coefficient energy is exactly card(mCarrier). `originalN_coefficient_norm` preserves the original transformedCoefficient energy, with both cusp signs and smooth Fourier labels. The original completed phase is k1/(64*V), shared by every row. `original_packet_regular_cutoff` applies the proved shell payment to these literal functionals, retaining their primitive cumulative hypotheses explicitly.

`original_level_cauchy` initially retains the full actual row count. `original_level_average` only replaces this by 2Z after a fixed-auxiliary-index level map is injective and its positive levels satisfy z<=2Z. It proves the cardinal bound and hence the sqrt(2Z) cost from those gates. It does not identify arbitrary (nu,z) rows with levels. The endpoint range Z>=1/2 is retained; no Z>=1 rounding is assumed.

Classical boundary checked

[Pascadi v3](https://arxiv.org/html/2404.04239v3), Proposition E, Lemmas D/H, was read directly. D provides the two transform bounds for compact smooth tests with controlled scaled derivatives. H is a cumulative quadratic-form estimate for arbitrary complex coefficients, with nonempty length at least 1/2. The low bound in this delivery explicitly includes height zero; its limiting-transform identification still has to be supplied at the automorphic interface. The primitive constants and u,v are not silently simplified to absorb selectable powers.

[Drappeau, Proposition 4.7](https://drappeau.perso.math.cnrs.fr/documents/divtm-siegel.pdf), pp.15–16, was also read directly. It fixes the sqrt(n)*rho normalization, trivial-character specialization, cusp density 1/z, positive Maass cosh weight, holomorphic weight and cusp-summed continuous measure. Thus the intended actual inputs are u=M^(1+epsilon)/z and v=L^(1+epsilon)/z with the classical constants in A2,B2. For holomorphic height k-1, the cumulative k-cut has to be shifted to T+1 and its absolute factor paid. No individual Eisenstein series is treated as an L2 vector.

The two new files introduce no named external axiom or assumption asserting the original estimate. Their conditional cumulative hypotheses are primitive positive quadratic forms, with their full analytic meaning still pending. The actual source identity is unconditional apart from its original integer positivity/coprimality gates.

Exact remaining blockers

1. The normalized automorphic Kuznetsov identity connecting the new actual matrix-phase c sum to the actual regular/holomorphic/continuous spectral objects is not installed as a supplied theorem. The current genuine Gamma0 Hilbert/operator, physical Hecke and radial KL results were inspected. The quotientRealK R(n) supplier covers real order (exceptional and threshold), while radial KL Plancherel identifies the radial physical measure. Neither is the required full regular automorphic decomposition. This distinction is preserved.
2. The source common nonzero-m truncation, signed-block orientation, actual smooth-test seminorms and their summation need to be connected to each physical nonzeroKernel. Existing PacketData has the correct common phase and coefficients, but this delivery does not prove that every original nonzero physical term has already reached that PacketData.
3. The two cumulative hypotheses must be supplied for the actual normalized basis/fibre, including its positive weights, exact scale supports, regular t=0 value and the holomorphic k-1 convention. `Rinf` and `Rone` in the finite consumer remain explicit coefficient maps, not an asserted automorphic realization.
4. The continuous ABL quadratic form and positive-measure version of the shell/exhaustion argument remain open. The finite result has not been promoted to an infinite spectrum or an arbitrary measure by definition.
5. The coprime ABL packet with (a,z)=1, height-independent transformed coefficient and squared Maass cost (abs(a)*nu)^(7/32), fixed-nu level source association, auxiliary sum and exact physical outside Kuznetsov factor remain to be assembled with these steps. No lambda_v has been treated as common to all oldform dilations.
6. The regular Eq24 P0 polynomial itself, its attachment to the already proved production Eq24-to-Eq25 algebra and H actual counted polynomial, and the full regular physical return are still OPEN. Exceptional work belongs to the other J owner. The subsequent two-root/retained-phase/dispersion assembly remains open.

No contradiction in the original manuscript was found. This delivery removes a real source-class/cusp-phase dictionary and the finite positive-norm regular summation; it does not claim the complete requested estimate. The explicit primitive and source-identification boundaries cannot be relabeled as a new external Eq24 theorem.

Installation and verification

The new filenames install as their corresponding ImbalancedChen modules. The source module depends on the exact I `Part3ActualZeroPoissonKernel.lean`, which is currently a source-only file; its G signed-counting predecessor is also source-only. REGISTRY pins those paths, all direct production imports, relevant current objects, predecessor manifests, manuscript segments and the Mathlib revision. No production file was copied over to satisfy a missing installation target. The two new files are independent of each other; neither imports the exceptional owner's draft.

Only static text, mathematical and source/hash inspection was performed. The proof bodies need independent review and user-owned elaboration. No compilation, kernel verification, or broad mathematical completion credit is asserted.
