# The marked weight-zero trace at the manuscript cusps

The four Lean source candidates give the arithmetic and spectral evaluations of the same marked spatial inner product at every positive source level $z$. The terminal theorem is `OriginalMarkedArithmeticTrace20261112.original_marked_arithmetic_trace`. Its continuous factor uses all native singular cusps at this same level. It retains the common $m$ interval and phase, both Poisson signs, the signed primary row, the complete cuspidal sum, and the actual hyperbolic quotient measure.

For positive $p$ and signed nonzero $h$, the geometric term at the positive integer $d$ coprime to $z$ is

\[
\frac{S_{\infty,1}(p,h;d\sqrt z)}{d\sqrt z}\,
\Phi_{\psi,\phi,\operatorname{sgn}h}
 \!\left(\frac{4\pi\sqrt{p|h|}}{d\sqrt z}\right).
\]

Here $S_{\infty,1}$ is the existing matrix-defined cusp sum. The complete modulus series is summable. The separate diagonal can occur at $z=1$ and $p=h$, with its true radial overlap. Multiplying by the original `traceBeta` cancels the cusp phase and gives the original ordinary `sourceKloosterman` with the unconjugated `modulatedBeta`. The separate theorem `original_modulus_phase` makes this last identification at each actual denominator. [Original signed arithmetic input](https://github.com/UyNewNas/goldbach-formalization/blob/794fe55a2136e8f502eae426095631f64f596f7f/docs/source-only/20261102-resume-30r/actual_kuznetsov/Part3OriginalSignedTraceInput.lean)

## The signed pairing and its induced test

The actual identity $\sigma_1=T W_z T_{1/z}$, quotient Fricke invariance of the measure and the spatial Fourier pairing give

\[
\langle P_{1,h}\phi,F\rangle
 = e(h/z)\langle P_{0,h}\phi,F\rangle
\]

for every spatial $L^2$ test $F$. Using $F=P_{\infty,p}\psi$ reverses the previously available geometric pairing. Conjugating the integral and applying the real classical Kloosterman sign identity give the positive starting frequency $p$ and the original signed $h$. The high-denominator vanishing follows from the two compact positive-height support floors on the original fibers. This justifies the sum over all positive moduli. [Quotient geometric pairing](https://github.com/UyNewNas/goldbach-formalization/blob/794fe55a2136e8f502eae426095631f64f596f7f/ImbalancedChen/Part3InfinityZeroActualQuotientGeometricAssembly.lean) [Physical cusp phase](https://github.com/UyNewNas/goldbach-formalization/blob/794fe55a2136e8f502eae426095631f64f596f7f/docs/source-only/20261102-resume-30r/oldform_continuous/repairs/Part3ActualFrickeCuspPhase.lean)

Both seeds in the marked pair carry the earlier normalization $|h|^{-1/2}\phi(|h|y)$. Put $s=\operatorname{sgn}h$, $e(x)=\exp(2\pi i x)$, $u=4\pi\sqrt{p|h|}/(d\sqrt z)$, and $k=(u/(4\pi))^2$. The substitution $X=p x,\ Y=p y$ in the actual double Bruhat integral yields

\[
\Phi_{\psi,\phi,s}(u)
=\frac{4\pi}{u}\overline{\int_{\mathbb R^2}
  \frac{\overline{\psi(Y)}}{Y^2}
  e(-X)\,e\!\left(\frac{-s kX}{X^2+Y^2}\right)
  \phi\!\left(\frac{kY}{X^2+Y^2}\right)\,dX\,dY}.
\]

This is the function `orbitTest`. The scaled orbit integral equals $\Phi(u)/(d\sqrt z)$. Positive-height supports allow the kernels to be extended by zero. The Jacobians and both factors $1/\sqrt{|h|}$ from the two physical seeds enter the proof. The outer conjugation comes from the spatial order $\langle V_N,V_M\rangle$.

## The spectral density

Let $P_\psi(t)=\mathtt{radialProbe}(1,\psi,t)$, with the physical $2\sqrt y K_{it}(2\pi y)$ radial function. The corresponding spectral test is

\[
H_{\psi,\phi}(t)=\cosh(\pi t)\overline{P_\psi(t)}P_\phi(t).
\]

The continuous summand is the full native-cusp sum of $\overline{M(R_a)}N(R_a) H_{\psi,\phi}(t)\$ divided by $4\pi\cosh(\pi t)$. The bounded analysis and marked projection identity supplies absolute integrability for the resulting integrand. Each $R_a$ is the actual unit-leading spatial Eisenstein Fourier coefficient in the $2\sqrt y K_{it}\$ expansion. The complete cuspidal sum retains its native basis orders and the two `orderProbe` factors. The underlying projection proof is recorded separately. [Normalized marked projection](../projection-next/REPORT.md) [ABL normalizations in §3](https://arxiv.org/pdf/2005.13915v1#page=7)

## The remaining manuscript step

The manuscript specifies `spectralTest` from its common cutoff and finite Fourier phases. The result here applies to the displayed two-height-probe transform. To use the manuscript's particular test, one must identify its signed Kuznetsov inversion and the corresponding Bessel transforms. The same-sign arithmetic formula also involves the holomorphic spectrum. The available weight-zero Hilbert decomposition alone does not justify this step. The fixed-level, regular and exceptional large-sieve bounds and their all-cost $7/32$ estimate remain separate. [Distribution argument, §10](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L463-L483) [Normalization correspondence, §§2–4](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/final-classical-input-correspondence-20261010.txt) [Pascadi, §3.3](https://arxiv.org/html/2404.04239v3#S3.SS3)

The repository already contains compact pointwise Kontorovich–Lebedev inversion. Its variables and the prescribed two signed arithmetic kernels still have to be identified. The external Trace Formula Project lists its congruence-level volume as planned. Its current public implementation does not supply the missing finite-level theorem. [Existing pointwise inversion](https://github.com/UyNewNas/goldbach-formalization/blob/794fe55a2136e8f502eae426095631f64f596f7f/ImbalancedChen/Part3ActualKLCompactPointwiseInversion.lean) [External project status](https://stevenecreech.github.io/trace-formula/)

## Source selection and verification

For staging, `api-selection/SELECTION.json` includes the exact old and selected Git blobs for 14 historical modules. The 83 old qualified Fourier references now resolve to their pinned mathlib declarations. The one pointwise use of the Fourier coefficient identity evaluates its function equality with `congrFun`. Three existing published repairs are referenced at their original bytes. These changes add zero mathematical claims. The earlier projection package's selection for the `centered_cross` declaration remains required when staging it.

The four new mathematical modules, the selected dependencies and the source comparison have received static inspection. Formal credit is zero pending same-source Lean kernel verification and the recorded transitive staging requirements. The author performed no local proof execution, numerical check, remote write or CI dispatch.
