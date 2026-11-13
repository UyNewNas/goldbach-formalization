# The holomorphic part of the original positive marked trace

For a licensed positive mark \(p,b\), positive level \(z\), and the prescribed complex period-64 test \(\Phi=\mathtt{spectralTest}\ \ell\ Y\), these seven source modules give

\[
 \sum_{d\ge1}\mathtt{modulusTerm}(\Phi-\mathtt{residual})\,z\,p\,b\,d
 =
 \sum_{j\ge0}\Gamma(2j+2)\dot\Phi(2j+2)
    \sum_{f\in\mathcal B_{2j+2}(z)}
       \overline{R_{f,\infty}(p)}\,R_{f,1}(b)
 +{\bf1}_{z=1,\ p=b}\frac{1}{2\pi}\int_0^\infty J_0(q)\Phi(q)\,dq .
\]

The physical endpoint `positive_mark_holomorphic` uses the old signed integer argument of `modulusTerm`. `original_holomorphic_projection` selects \(b\) from the block’s `traceIndex`, proves \(b>0\) from the original sign and residue, and supplies absolute convergence over both the modulus–weight product and the dependent sum of all Petersson basis vectors. The test may be complex. All constants may depend on its fixed parameters and markings.

## The modulus and weight sums

Write \(n=2j+1,\ k=n+1,\ C=d\sqrt z\) and \(q_d=4\pi\sqrt{pb}/C\). The original cusp-one matrix sum includes its phase. The terms vanish on \((z,d)>1\). Multiplying the fixed-weight Petersson identity by

\[
 \frac{n\dot\Phi(k)}{4\pi},
 \qquad
 \dot\Phi(k)=4i^k\int_0^\infty J_n(q)\Phi(q)\frac{dq}{q}
\]

yields the displayed \(\Gamma(k)\dot\Phi(k)\) times the full basis sum because the unscaled Petersson factor is \(4\pi\Gamma(k-1)\). The factors \(i^k(-i)^k\) multiply to one. The geometric term is exactly the original matrix sum divided by \(C\), times \(2n\,\mathtt{moment}(n,\Phi)J_n(q_d)\). Summing the latter factor gives the defining positive holomorphic projection \(\Phi-\mathtt{residual}\).

The joint proof keeps one inverse power of \(d\) from every positive odd order of \(J_n(A/d)\), with \(A=4\pi\sqrt{pb}/\sqrt z\). The Gamma series gives a single numerator bound at \(A\). The fixed-first-mark estimate therefore bounds the geometric terms by a constant times

\[
  \frac{B_p(d)}{d^2}\;n\,|\mathtt{moment}(n,\Phi)|.
\]

The first factor is summable by the fixed-mark Euler majorant. The second is summable by the prescribed-test bound \(C_{\ell,Y}(8Y)^n/n!\). This proves the exchange of the two infinite series at weight two as well as every higher even weight. Summing the identity coefficient with the original diagonal theorem gives \(-\mathbf1_{z=1,p=b}\mathtt{diagonalMoment}(0,\Phi)/(2\pi)\) on the spectral side of the Petersson identity. Solving for the off-diagonal holomorphic geometry gives the positive sign in the displayed formula.

## Absolute convergence inside the finite bases

For either original normalized cusp frame, and in fact for any integral frame \(g\) of cusp width \(w_g\), the region \(0\le x<1,\ y\ge1\) maps into \(w_g+1\) translates of the closed modular domain after applying \(g\operatorname{diag}(\sqrt{w_g},1/\sqrt{w_g})\). Each translate moves by one element of \(\Gamma_0(z)\) into the chosen finite carrier. The invariant Petersson integrand is positive, so overlap gives the bound \((w_g+1)\|f\|^2\).

At fixed \(y>0\), the unit-period q-coefficient identity and Cauchy–Schwarz give \(e^{-4\pi my}|a_{f,g}(m)|^2\le\int_0^1|(f|g_{\rm norm})(x+iy)|^2dx\). Integrating above height one against \(y^{k-2}dy\) retains at least \(e^{-4\pi m}\Gamma(k-1)/(4\pi m)^{k-1}\). This follows by putting \(y=t+1\) and using \((t+1)^{k-2}\ge t^{k-2}\) for \(t>0\). The original \(a\)-to-\(R\) normalization and the actual Riesz vector of the Fourier functional then yield

\[
 4\pi\Gamma(k-1)\sum_{f\in\mathcal B_k(z)}|R_{f,g}(m)|^2
       \le (w_g+1)e^{4\pi m}.
\]

The proof first bounds the functional on every form and evaluates it on its own Riesz vector. Applying the two bounds to \(|R_{f,\infty}(p)R_{f,1}(b)|\) leaves a constant times \(n|\mathtt{moment}(n,\Phi)|\). Thus the absolute sum over \((j,f)\), with the finite index type depending on \(j\), converges before the basis vectors are grouped by weight.

## Source interfaces and verification

| Installed module after the prefix `ImbalancedChen.` | Supplied interface |
| --- | --- |
| Part3OriginalHolomorphicProjectionPrices | `weighted_moments`, `odd_bessel_uniform`, `joint_absolute` |
| Part3OriginalWeightedPetersson | `weighted_basis`, `weighted_geometry`, `diagonal_sum`, `weighted_petersson` |
| Part3OriginalHolomorphicProjectionMarks | `oddProjection`, `holSpectrum`, `positive_mark_holomorphic` |
| Part3OriginalPeterssonHighStrip | `high_strip_energy` on the original level carrier |
| Part3OriginalHighStripFourierMass | `horizontal_square`, `strip_fourier_mass` |
| Part3OriginalHolomorphicBasisMass | `fourier_functional`, `basis_mass` |
| Part3OriginalHolomorphicWeightSum | `holomorphic_absolute`, `original_holomorphic_projection` |

T04 supplies the finite outer Poisson and source contractions and the scalar remainder. `REGISTRY.json` binds the exact dependency choices, seven source byte streams, original manuscript and formalization repositories, and the pinned mathlib version. This is an uncompiled source submission. Verification here consists of reading the proofs, checking the physical source equations and normalization against the predecessors, and checking the recorded hashes.
