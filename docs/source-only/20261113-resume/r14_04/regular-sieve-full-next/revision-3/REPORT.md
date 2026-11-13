# Same-cusp oscillatory quadratic forms for the original regular large sieve

Six Lean source candidates estimate the literal damped, square-root-twisted Kloosterman form at infinity. They also pay the full initial progression of moduli `c=z d` with `H² z D ≤ M`. All statements are uncompiled. The all-height three-measure large sieve remains open. This work adds no spectral parameter range and changes no original status.

## The two arithmetic conclusions

Let `E(a)=Σ_{M≤m≤2M}|a(m)|²`, `e(x)=exp(2πix)`. For every integer `M≥1`, every integer `1≤c≤M`, every `λ≥0`, every `0<θ≤2`, and two arbitrary independent complex sequences, `twisted_form_bound` gives the following source inequality.

    |Σ a(m)b(n) S(m,n;c) exp(−λ√m√n) e(2θ√m√n/c)|
      ≤ exp(4π) √[244 c M(1+log M)/θ] √E(a) √E(b).

Both sums run over the full integer interval `[M,2M]`. The sequence may vanish at any indices. Taking `b=conj(a)` and zeroing the left endpoint gives the physical form in Drappeau (4.21). A real packet `L<n≤2L` has its integer indices in `[M,2M]` for `M=⌊L⌋+1`. For `L≥1/2` this satisfies `M≤3L`. The logarithm involves only the coefficient length. Neither the constant nor the logarithm depends on a spectral cutoff. The proof uses the standard positive complete sum on every positive modulus, including composites and 1. [Drappeau, Lemma 4.6](https://arxiv.org/html/1504.05549v4#S4.SS2.SSS1)

For `H≥1`, `z≥1`, integers `D≥0` with `H² z D≤M`, `τ>0`, weights `|w_d|≤H`, `λ_d≥0`, and `τ≤θ_d≤2`, `short_modulus_sum` gives

    |Σ_{1≤d≤D} w_d B(λ_d,θ_d;zd,M)/(zd)|
      ≤ 2 exp(4π) √[244(1+log M)/τ] (M/z) √E(a) √E(b).

The offset variable in the Lean statement is `j=d−1`. The proof sums `d^(−1/2)` by the elementary endpoint bound `Σ_{d≤D}1/√d≤2√D`. The factor `H√D` is paid from the actual cutoff. This is a complete finite progression for this range of moduli. It gives no bound on the other moduli of a spectral window.

## How the nonseparable phase is estimated

1. Write `m=M+s c+h` with `0≤h<c`. The anchor `A_s=M+s c` ranges up to `2M`. The right analysis matrix has rows indexed by both `s` and the additive residue `j`. Its entries are `e(jn/c+2θ√A_s√n/c)` for `M≤n≤2M`. The Gram matrix sums over every original integer in that interval.
2. The phase increment between distinct residue rows is an integer-residue difference divided by `c` plus an error of magnitude at most `5/(6c)`. The bound follows by rationalizing `√(n+1)−√n`, using `√2≤17/12`, and `θ≤2`. Cyclic distance `d=min(|j−k|,c−|j−k|)` gives the Gram bound `12c/d`. Within one residue, distinct block indices have increment at least `θ|s−t|/(12M)`, with conjugate symmetry covering both orders. Their Gram bound is `24M/(θ|s−t|)`. Both monotonicity directions use an existing discrete first-derivative estimate. The true diagonal contributes `M+1`.
3. Two injections for each signed distance and reflection of the nonzero residue interval give a logarithmic row sum. For `l=1+log M`, the diagonal is at most `2Ml`, different residues contribute at most `96Ml`, and other blocks in the same residue at most `48Ml/θ`. Since `θ≤2`, the complete row sum is at most `244Ml/θ`. Finite Gram duality gives this squared norm for the common right vector. The complete left DFT has squared norm `c` on each block. Only the unit group is permuted by inversion.
4. Put `x=√M`, `y=√m`, `v=√A_s`, `w=√n`, and `t=(w−x)/x`. The residual rank-one series comes from `exp(Zt)` with `Z=−λx(y−x)+4πiθx(y−v)/c`. The retained right amplitude `exp(−λx(w−x))t^j` has norm at most one. The complete left majorant is `exp(−λM)(λM+4π)^j/j!`. It sums to `exp(4π)`, uniformly including `λ=0`. A finite-sums/HasSum exchange, followed by the natural quotient–remainder bijection with the padded terminal block, restores the literal physical form.

## Exact sources reused

Paths are relative to the workspace. `REGISTRY.json` records the bytes, raw SHA-256, import and staging path of each new file, both direct OAI suppliers and their checked-out source dependencies. The 18 OAI modules in the transitive source closure have no paths at their `OAI/...` names in the ordinary source tree of `680fc11a`. The original OAI tree specifies Lean 4.34.1 and mathlib `d13f23b7`. The selected continuation records Lean 4.33.0-rc1 and mathlib `e4c91783`. A compile job needs those exact source bytes staged under the recorded `OAI/...` names and the continuation pin. Compatibility with that pin has not been compiled or checked by the kernel.

| Source or supporting declaration | Its role here |
|---|---|
| `OpenAI-Math-2026-10-06/lean/OAI/NumberTheory/EgyptianFractions/DiscreteFirstDerivative.lean` · `phase`, `phase_add`, `phase_neg`, `first_derivative_sum_bound_either_succ` | Unit-interval first derivative estimate with endpoints and both monotonicity directions |
| `OpenAI-Math-2026-10-06/lean/OAI/NumberTheory/CubicMoment/Estimates/GramOperator.lean` · `finite_gram_operator_le` · its `DispersionAlgebra.lean` ancestor's `complex_bilinear_rows_sq` | Complete finite Gram duality and Cauchy–Schwarz |
| `goldbach-proof-continuation/ImbalancedChen/Part3IntervalHarmonicPairBound.lean` · `reciprocal_reflection_sum`, `reciprocal_sum_le_one_add_log`, `real_reciprocal_sum_eq_harmonic` | Exact reflection and harmonic price |
| Same directory, `Part3FiniteUnitInverseL2.lean` · `dft_energy`, `sum_unitGate_eq_units`; `Part3PhysicalSmoothReciprocalPoisson.lean` · `Physical.kloosterman_eq_zmod` | The complete physical modulus and its actual unit inversion |
| Same directory, `Part3OriginalKloostermanOperatorL2.lean` · `originalOperator_eq_two_dfts`, `originalOperator_vectorNorm_le` | Checked the earlier complete unweighted operator. Its DFT factor is reused at the individual physical block. |

## Outstanding original analytic interfaces

* **Holomorphic spectrum.** The published T21 `positive-petersson-next/Part3OriginalPositivePeterssonTrace.lean:petersson` pairs the infinity and cusp-one frames. Its moduli are those of that mixed pair. A same-observation positive Petersson sum needs its own same-cusp identification, followed by the *summed* odd-order Bessel window with `ℓ=k−1`, positive spectral weight dominating `1_{ℓ≤K}`, and diagonal `O(K²)`. For example a smooth bump on one dyadic order interval may be used away from the initial R2 range. Its actual transform still needs the short-modulus representation and its complementary-`c` cancellation. A direct `O(K)` bound for each Bessel window summed over all `c≤M` leaves a factor `K`. The new progression estimate uses the specific restriction `K²c≤M`. It imposes no such cutoff on the actual Bessel transform. [Drappeau, Proof 4.4 and its reference to DI pp. 258–261](https://arxiv.org/html/1504.05549v4#S4.SS2.SSS2)
* **Maaß and continuous spectra.** The source in `goldbach-proof-continuation/ImbalancedChen/Part3CompactCuspQuotientGeometricPairing.lean:193` unfolds two compact tests at infinity with a support-dependent finite modulus cutoff. The operation at an individual positive modulus comes from `output/resume-20261112/t04/kuznetsov-next/Part3ActualMarkedBruhatTest.lean:orbit_integral`. These identities do not give the DI pre-Kuznetsov spectral multiplier `H(t,r)` on its prescribed noncompact test or the complementary-modulus estimate. The R2 `Part3OriginalRegularCumulativeMellin.lean` integral has its own multiplier. To use either route one must keep that multiplier, all incoming cusps, both signs of real t and the continuous measure `dt/(4π cosh(πt))`. One-variable Mellin decay does not pay the remaining mixed frequencies in the corresponding geometrical kernel.
* **Second observing cusp.** `goldbach-proof-continuation/ImbalancedChen/Part3ActualFrickeCuspPhase.lean:sigmaOne_fourierCoeff_fricke_phase` supplies the horizontal phase and exact Fricke coordinate. The square of a fixed-phase reweighted sequence has the same coefficient energy. The new arithmetic proof at infinity still requires transporting the specified discrete/continuous spectral resolution, or proving the same-cusp geometric trace there, before one can claim either native cusp-one square. The same applies to transport of the complete Petersson ONB.

Thus a length logarithm from the physical Kloosterman estimate can be absorbed into the allowed length power. The residual obstructions are the prescribed same-cusp energy test and the estimate of its complementary range of moduli, including the holomorphic middle regime `K>2, L^ε<K<L/z`. No new upper bound for any of the three full spectral measures is asserted.

## Second source review generation

The independent static review identified the reserved lambda token in three files, three applications of an addition monotonicity lemma with the host's reversed naming convention, and an image-sum lemma absent from the pinned host. This generation writes the parameter as `lam`, uses the host's correct addition orientation, and supplies the needed injection comparison from `sum_image` and `sum_le_sum_of_subset_of_nonneg`. The first-generation bytes are retained separately. Check all donors against the stated host pin during any later compilation.

## Third source review generation

One additional host tactic step now explicitly supplies the nonnegativity of theta from its interval membership. The raw OAI PrimeFactors source uses a later name for the finite product inequality at line 74. The separately pinned `../donor-host-port/REGISTRY.json` selects the one-symbol correction to the exact host theorem at line 38 of `Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`. The remaining 17 OAI files preserve their exact donor bytes. Their compatibility with the host stays uncompiled.
