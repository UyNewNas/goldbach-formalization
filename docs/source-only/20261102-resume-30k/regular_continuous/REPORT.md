# K regular_continuous: positive-measure exhaustion of the original packet

Status: **SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT**. The local continuous integration and source-normalization step has strict proof bodies. The full task, actual regular Eq. (24), and `P3.5.uniform_spectral` remain **OPEN**. No compiler, Lean/lake/build, CI, certificate replay, finite mathematical execution, Git operation, subagent, or quota call was used. Only this assigned K directory was written.

## Original obligation and predecessor

The target is the regular part in the original medium-completion Eq. (24), not radial Kontorovich–Lebedev Plancherel. The relevant manuscript passages are `manuscript-body.tex:116–255`, particularly `197–252`; `distribution-medium-completion-20261010.txt:299–405`, particularly `349–380`; `final-classical-input-correspondence-20261010.txt:20–139`; and `spectral-regular-polynomial-derivation-20261010.txt:55–155`. The original global parameters remain `c = 49044063/25000000`, `K = 8452171/1250000`, and `theta = 7/32`. The variable `K` in the spectral lemmas is a height cutoff and does not replace the original sieve parameter.

The current J `spectral_regular` source, registry, report, and independent review were read. Its narrow source review covers the actual cusp-one physical-source dictionary and finite cumulative shell calculation. J explicitly leaves positive-measure continuous integration and infinite exhaustion open. Its `Part3RegularCumulativeShellPayment` is reused at its exact draft path, without installing or editing it. Its physical cusp-one module is pinned as source context; the new integration module does not import that uninstalled physical module or claim to close its remaining trace-formula connection.

## Substantive step supplied

`Part3RegularPositiveMeasureExhaustion.lean` works on an arbitrary positive measure with a measurable real height. For the actual cut `abs(t) <= T` it assumes local `MemLp` membership and the two positive cumulative quadratic forms for **every real `T >= 1`**. Its conclusions are derived as follows.

1. Integral Cauchy–Schwarz gives the product bound from two local L2 norms. A pointwise bounded transform then gives local L1 membership, as well as the absolute integral estimate.
2. The measurable shells are exactly `4^j K < abs(t) <= 4^(j+1) K`. The source proves disjointness, cutoff union, and endpoint ownership. It transfers each cumulative bound at the upper shell endpoint using positivity of the squared norm. The transform decay pays a shell by the two geometric factors `2^(-j)` and `4^(-j)`.
3. Exact set-integral addition gives every finite continuous cutoff a bound independent of the cutoff index. Its tail cost is `32/(K^2 sqrt(K)) + (64/3) Y/K^3`.
4. The actual cut sets increase to the entire space. Monotone exhaustion of the nonnegative ENNReal norm integral proves global L1. Thus the full Bochner integral is used only after integrability is established; a totalized nonintegrable integral cannot satisfy the premises vacuously.
5. With `regularBase Y = max 1 (2Y)`, J's elementary scalar inequalities give

   `integral norm(H*A*conj B) <= 516*C*(1+abs(log Y))/(1+Y) * sqrt(((1+Y^2+u)*A2)*((1+Y^2+v)*B2))`.

   The genuine cutoff Bochner integrals then converge to the full integral. Neither global L1, spectral convergence, a bilinear return bound, nor Eq. (24) is a premise.

This is a positive-measure proof, not a renaming of the finite theorem: local integrability, measurable shell additivity, monotone nonnegative exhaustion, and Bochner convergence are new deductions. The same measure theorem can later be applied to positive discrete spectral measures, but no Maass/holomorphic basis or holomorphic height supplier is constructed here.

## Actual continuous carrier and packet coefficients

`Part3OriginalContinuousPacketExhaustion.lean` uses Mathlib's actual finite cusp-orbit quotient of `Gamma0(z)`, with the group viewed as a subgroup of `GL(2,R)`. The continuous carrier is **all** these cusps times the full real line. Its measure is counting measure on the cusps times `dt/cosh(pi*t)`. With trivial character every cusp is singular; no selected cusp subset or finite-height proxy is substituted.

The file derives the full cusp sum and its exact finite-height quadratic form by Fubini and the with-density integral identities. It retains the factor `1/(4*pi)` outside the measure in `continuousKuznetsovValue`. This definition is the normalized continuous expression; it is **not** asserted equal to the original physical Kloosterman sum.

The integer matrix `[[1,0],[z,1]]` belongs to the actual Gamma0(z) and sends infinity to `1/z`. Together with the denominator-one representative of cusp one, the printed classical arithmetic density `gcd(w,z/w)/z` is exactly `1/z` for both relevant cusps. This establishes the density calculation; it does not itself establish the Fourier scaling matrices or a trace identity.

The consumer takes the existing literal `PacketData`, the actual level equality `z = (P.packet r).level`, the common mode `k`, and **the existing `P.Y0`**. It does not permit a second independent packet scale. The two raw Fourier maps are kept explicit until their actual automorphic realization is supplied.

- `normalizedR` is exactly `sqrt(n)*rho(n)`. Its norm square is `n*norm(rho(n))^2`, and `normalizedR_pair` reproduces the exact `sqrt(m*n)*conj(rhoInf(m))*rhoOne(n)` trace factor.
- The infinity factor is `conj(originalMFunctional P (-k) ...)`. Conjugating the reflected completed phase gives the original positive-`k` common phase `e(k1*m/(64*V))`. The proof uses the existing production theorem `completed_weight_neg_frequency`.
- The cusp-one factor is `originalNFunctional P k r ...`. Its coefficient is the original complex `beta(nu*n,z)`, the original coprimality gate, the original plus/minus `n/z` cusp phase, and the original `k2,k3` mode phase. No reality of beta and no conjugation of beta is used.
- `signedRho` chooses frequency `-n` exactly when the same original `P.negativeCusp` flag is true. The arithmetic phase sign and Fourier sign are not independent choices.
- `originalTraceIntegrand_eq_source` expands to the literal finite m,n source with the infinity Fourier coefficient conjugated. The existing J exact coefficient identities reduce its two original energies to `card(P.mCarrier)` and `originalNEnergy P r`; Fourier normalization does not insert an `n` into the arithmetic coefficient energy.
- Measurability of the packet functionals is derived from measurability of the raw Fourier maps and the finite source sums. The existing packet's residue-level coprimality is retained, with `z` substituted by the explicit level equality.

The main `original_packet_continuous_exhaustion` specializes the positive-measure theorem to these actual objects. It concludes L1, the explicit continuous regular bound with `V^(1+epsilon)/z` and `(U/nu)^(1+epsilon)/z`, genuine integral exhaustion, and the original residue-level coprimality. The constants are fixed before the local hypotheses quantify over **every** real height `T >= 1`. The result is for a fixed original packet and level; a common choice of constants over the full level/residue/nu family is not silently inferred.

## Precise classical interface checked

The checked primary statements are Drappeau, *Sums of Kloosterman sums in arithmetic progressions, and the error term in the dispersion method*, [author PDF](https://drappeau.perso.math.cnrs.fr/documents/divtm-siegel.pdf), pp. 12–16, especially Lemma 4.5, (4.16), (4.18), and Proposition 4.7, (4.25). Pages 14 and 16 were rendered and inspected to check the conjugation and measure. The exact downloaded PDF and page renders are pinned in the registry.

For trivial character and weight zero, the continuous normalized trace term has the all-cusp sum, the fixed `1/(4*pi)`, `sqrt(m*n)`, the conjugated infinity coefficient, the signed cusp-one frequency, and `dt/cosh(pi*t)`. Proposition 4.7 uses arbitrary complex coefficient sequences supported on a dyadic interval, `T >= 1`, interval size `N >= 1/2`, and the Fourier normalization `sqrt(n)*rho(plus/minus n,t)`. Its density is `mu(a)`, and the arithmetic calculation above gives `mu(infinity)=mu(1)=1/z`.

The primitive hypotheses in the new theorem are precisely raw Fourier measurability, local L2 membership, the two literal all-cusp finite-height quadratic-form bounds, and low/high transform bounds. The local L2 hypotheses are intentionally explicit rather than deduced from totalized Bochner inequalities. No external theorem is installed as an axiom or asserted instance. Classical instantiation at the actual dyadic supports, the uniform constants, and the Fourier normalization still require source proof.

Pascadi's [arXiv:2404.04239v3](https://arxiv.org/html/2404.04239v3), Lemmas D and H and Proposition E, was also read. Its continuous formula uses a different displayed coefficient convention involving `n^(it)*phi`. That coefficient is **not** silently identified with the raw Whittaker rho used above. The normalized transform conventions, including Drappeau's factor-four convention, must be reconciled in the actual smooth-test supplier. Pascadi's printed low-height transform bound excludes zero; the new theorem explicitly requires its low bound at `t=0`, leaving the corresponding limiting-transform proof open.

## What remains open

1. Realize the raw maps by the actual critical-line Eisenstein Fourier coefficients for the full Gamma0(z) cusp family with the specified scaling matrices and trivial character. Existing production full-level scattering and right-half-plane level-Eisenstein modules were inspected; this delivery does not infer the required full critical-line, all-cusp identification from them.
2. Supply the normalized classical Kuznetsov identity from J's actual infinity/cusp-one matrix sum, preserving all signs and the fixed constants. No radial KL theorem is substituted for it.
3. Instantiate the primitive local L2/cumulative bounds using the precise classical theorem and the **actual** packet supports. Generic `PacketData` does not itself prove positive `nu`, positive frequency carriers, dyadic support of length at least `1/2`, or the common constants over the level/residue family. These are not erased from the full task by the conditional integration theorem.
4. Construct the actual smooth test and its transform, prove its measurability, low bound including `t=0`, high decay, and original derivative-seminorm payment. Complete the global nonzero-m truncation, signed dyadic/common interval, and physical-source-to-`PacketData` association.
5. Supply the actual discrete Maass and holomorphic spectral data/weights and their exhaustion, the holomorphic `k-1` convention, and the coprime/oldform source match required by the original ABL application.
6. Perform the original fixed-nu level and auxiliary sums with the correct common constants, coefficient counting, and outside `C*sqrt(Z)` restoration. Attach the resulting regular Eq. (24) to the original P0/H counted-polynomial consumer. Full two-root bare-source, retained phase, E2/dispersion, K/PP, and medium targets remain open.

## Static verification and installation boundary

Both candidate modules contain explicit strict proof bodies. Author-only static review checked comment/string closure, balanced delimiters, and absence of forbidden proof escapes outside comments. This is not elaboration, compilation, kernel checking, or independent acceptance. The registry records `compiled=false`, `kernel_verified=false`, `formal_credit=0`, exact raw hashes, declaration names, and import/source paths.

The candidates are not installed in `ImbalancedChen`. Their J dependency remains at its draft path. Direct Mathlib import sources and the specific measure/Holder/cusp APIs used were read from exact primary source archives at the pinned mathlib revision because the expected local `.lake/packages/mathlib` source directory was absent. The archived `.lean.txt` files are references, not additional candidate modules. No full recursive import closure or inherited formal verification is claimed. Independent source review is pending at author freeze.
