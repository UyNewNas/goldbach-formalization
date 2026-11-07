# J / spectral_regular independent source review

**SOURCE_REVIEW_PASS for the two frozen local modules. The original regular Eq24 task remains OPEN.** The accepted scope is the actual cusp-one source dictionary, the finite discrete cumulative-to-shell calculation, and the literal packet-energy and guarded level-count consequences. This is static mathematical/source review: `compiled=false`, `kernel_verified=false`, `formal_credit=0`.

| Artifact | Raw SHA-256 |
| --- | --- |
| `spectral_regular/Part3OriginalNonzeroCuspOneSource.lean` | `d7ad7167a966bff0e7dee4cb706152330df1a71faff700da61b3c63e9b753230` |
| `spectral_regular/Part3RegularCumulativeShellPayment.lean` | `f20f597f6eff9be4814c58eb1ecc2aca6c03aaf443761c1333b198947956471e` |
| `spectral_regular/REGISTRY.json` | `d54dada9856c9cd2db36ab74161fa2b5875ce5cda5cb5a7688b34c0943a7b6ab` |
| `spectral_regular/REPORT.md` | `ff4f67a2a6d4d996f231f58fb56fc92446e12d47cbe78ffe99d45fc42f8a68fe` |

All four frozen hashes and all 35 registered local pin entries match the current bytes. I read the J README/task row, manuscript lines 116–255, the original medium module lines 299–405, the classical cusp/input correspondence, the regular-polynomial derivation, and the I/H predecessor reports and registry boundaries. The actual physical frequency, I `nonzeroKernel`, current Gamma0 cusp and parabolic objects, and literal `PacketData` definitions were checked. Registered hashes are provenance checks, not proof validation.

The physical residue construction is substantive. For a unit `u` modulo `c`, it chooses representatives `alpha = z^(-1)u` and `k = -u^(-1)`. Their congruence gives an integer `A` with `A*c-z*k*alpha=1`. Thus `[[A,alpha-A],[z*k,c-z*k]]` is a genuine integral determinant-one matrix in the existing `Gamma0(z)`, rather than a record with a desired cusp identity as a premise.

The orbit argument is complete at its stated positive modulus. Right multiplication by the actual integral `T` carries the cusp-one two-sided translation action to the existing cusp-zero action. The resulting classification is equality of the bottom-row sum `c` and congruence of `k` modulo `c`. Conversely, an actual Gamma0 matrix with this row sum supplies the unit `u=z*(g00+g01)`; its inverse is `-k`, so the constructed representative belongs to its orbit. If two representatives share an orbit, their inverse residues coincide, hence the units coincide. The surjectivity and injectivity statements do not depend on literal agreement with an earlier arbitrary Bezout representative. On the positive-modulus sector, central signs do not produce an additional class or multiplicity.

The normalization is exact. Infinity has width one; the right parabolic is `cuspOneMatrix*T^(z*v)*cuspOneMatrix^(-1)`, with the existing width characterization giving width `z`. The normalized lower-left entry is `sqrt(z)*c>0`. The old and new lower-right ratios differ by `1/z`, so the old matrix sum is `e(n/z)*S(m*inverse(z),n;c)`. Reversing the identity gives the required `e(-n/z)`, and substitution `n=a*y` gives `e(-a*y/z)` without restricting the signs of `m` or `y`. This matches the stated infinity/one scaling specialization of [Drappeau, Lemma 4.3](https://drappeau.perso.math.cnrs.fr/documents/divtm-siegel.pdf).

`original_nonzeroKernel_eq_cuspOne` consumes I's actual source. It retains `D/c`, the Fourier argument `(D/c)*m`, `smoothModuli C = Ioc 0 floor(3C)`, the original scaled cutoff, the `c.Coprime z` filter, and every `m != 0`. Its infinite-sum equality is termwise congruence, so it neither rearranges a series nor assumes a new summability or truncation theorem. The arithmetic identity only needs `gcd(c,z)=1`; the separate original condition `(a,z)=1` remains necessary at the later ABL interface. This does not repay either the `m=0` or `y=0` branch.

The finite height argument also removes a real internal calculation. Write

    G = sqrt(((K^2+u)*A2)*((K^2+v)*B2)).

Finite Cauchy and the cumulative bounds at the upper endpoint of `(4^j*K,4^(j+1)*K]` give a coefficient cost `16*4^(2j)*G`. The pointwise transform bound then gives

    16*C*G*((1/2)^j/(K^2*sqrt(K)) + Y*(1/4)^j/K^3).

The finite geometric sums are bounded by `2` and `4/3`, yielding the high cost `32/(K^2*sqrt(K))+(64/3)*Y/K^3`. The endpoint identities partition the finite cut exactly: height zero and each lower seam belong to the preceding cut, while each shell owns its upper seam. For `K=max(1,2Y)`, the displayed tail is at most `128/(1+Y)` and the base norm comparison costs four. Adding the low-height logarithmic bound gives `4*129=516`. All signs, nonnegativity hypotheses and denominator directions agree with this calculation; no residue, auxiliary-index or spectral-height power is absorbed into 516.

The quantifiers remain appropriately limited. The result is conditional on two positive cumulative estimates for every real `T>=1` and on the low/high transform bounds, for a specified finite set `S`. It is uniform in `J` with those same constants. It does not construct uniform automorphic instances across levels, original scales or all finite sets. In particular, the low hypothesis includes `t=0`, whose limiting-transform identification still needs proof. [Pascadi v3, Lemmas D/H and Proposition E](https://arxiv.org/html/2404.04239v3) support the intended compact-smooth transform and cumulative interfaces; they also distinguish the actual basis, weights and holomorphic height `k-1`. [Drappeau, Proposition 4.7](https://drappeau.perso.math.cnrs.fr/documents/divtm-siegel.pdf) explicitly supplies the `sqrt(n)*rho` convention, lengths `N>=1/2`, and positive cusp-summed continuous form. These are checked interfaces, not installed J theorem instances.

The packet specialization uses existing objects. Its m energy is exactly `card(P.mCarrier)`, with the single common interval and phase `k1/(64*V)`; it does not silently replace that cardinality by the spectral length. Its n energy is exactly the squared norm of the original `transformedCoefficient`, including either cusp sign and the smooth Fourier labels. `Rinf` and `Rone` remain explicit maps awaiting automorphic identification. The row Cauchy theorem first retains the full `card(P.rows)`. Replacing it by `2Z` requires an injective level map and the upper bound `level<=2Z`; positivity comes from the actual `CoprimePacket`. This pays `sqrt(2Z)` for `Z>=1/2`, including the sub-unit endpoint range. It does not identify arbitrary `(nu,z)` rows with levels or prove the required fixed-nu source association.

The following are still required for the original target:

- The normalized automorphic Kuznetsov identity for the actual matrix-phase modulus sum, with spectral basis/fibres, signs, positive weights and physical outside normalization. The current Gamma0 scalar spectral bundle is an abstract spectral measure model; the actual real-order K coefficient covers exceptional/threshold order, and the physical Hecke result preserves the classical PDE. The radial KL Plancherel identity is not an automorphic Kuznetsov formula.
- Actual regular Maass and holomorphic cumulative instances, with their exact dyadic support and constants, `u=M^(1+epsilon)/z`, `v=L^(1+epsilon)/z`, the `t=0` limit, and the shifted cumulative cutoff for height `k-1`.
- The continuous ABL quadratic form, positive-measure shell proof and justified infinite spectral exhaustion. A finite-cut inequality alone does not establish those conclusions.
- The original global nonzero-m cutoff, signed block orientation, common interval/phase and smooth-test seminorm summation connecting each physical kernel to `PacketData`.
- The coprime ABL packet and oldform/fibre source identification, with `(a,z)=1`, height-independent coefficient and squared Maass cost `(|a|*nu)^(7/32)`; actual fixed-nu level association, original auxiliary family and uniform selectable subpower payments.
- Restoration of `C*sqrt(Z)`, the regular Eq24 `P0` polynomial and its connection to the existing Eq24-to-Eq25 algebra and H counted polynomial, followed by the original two-root/retained-phase/dispersion assembly. Exceptional work remains separate.

No local mathematical source blocker or manuscript contradiction was found. No Eq24 or equivalent bilinear estimate has been promoted to an external assumption. The global `c=49044063/25000000`, `K=8452171/1250000` and `theta=7/32` are unchanged; the analytic file's `K` denotes a height cutoff. Installation must use the exact pinned I/G source-only predecessors, and no recursive import-closure or elaboration claim is made.

Only `reviews/spectral_regular.json` and `reviews/spectral_regular.md` were written. No compiler, build, CI, finite decision/certificate replay, Git operation, quota call or subagent was used.
