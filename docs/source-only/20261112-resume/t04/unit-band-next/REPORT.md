# Unit spectral bands for a nonzero Fourier mode

For each positive level \(N\) and signed frequency \(m\ne0\), the six source candidates give one finite constant \(C_{N,m}\). In `native_unit_band` it controls all of the following quantities. The basis coefficients \(R\) multiply the actual \(2\sqrt y K_\nu(2\pi |m|y)\) in the normalized frame. [Native Fourier coefficients](https://github.com/UyNewNas/goldbach-formalization/blob/32d541884c85748e3fb18f7a83801b2f8b16e359/docs/source-only/20261102-resume-30s/S/s20_normalized_kuznetsov/Part3ActualCuspBasisWhittakerCoefficients.lean)

- For every normalized integral observation frame \(g\) and \(T\ge0\), the sum of \(\lvert R_j(g,m)\rvert^2/\cosh(\pi t_j)\) over \(T\le t_j\le T+1\) is absolutely convergent and at most \(C_{N,m}(1+T)\). Here \(\lambda_j\ge1/4\) and \(t_j=\sqrt{\lambda_j-1/4}\). This includes \(\lambda_j=1/4\).
- At each of the two observation cusps used by the manuscript, infinity and one, the integral over \(T\le |t|\le T+1\) of \(\sum_a |R_a(m,t)|^2\,dt/(4\pi\cosh(\pi t))\) is absolutely convergent and at most \(C_{N,m}(1+T)\). The sum runs over all singular incoming cusps of this level. The negative band uses the same lower bound on the probe. Each individual continuous coefficient retains its actual value there.
- At every normalized integral frame the unweighted sum of \(|R_j(g,m)|^2\) over \(\lambda_j<1/4\) is absolutely convergent and at most \(C_{N,m}\). Nonnegativity of the native eigenvalue puts \(\sqrt{1/4-\lambda_j}\) in \([0,1/2]\). A strictly positive probe on that whole interval bounds every finite subsum.

## The spatial estimate

The absolute value of the signed periodization is bounded pointwise by the zero-mode periodization of a nonnegative envelope in the same normalized frame. The latter has a continuous component and a constant component with coefficient \(|\mathrm{actualVolume}(N)|^{-1}\). The physical Gram and residual identity give the squared-norm bound \(2\|\mathrm{logVector}(\eta)\|^2+|\mathrm{actualVolume}(N)|^{-1}|\mathrm{moment}(\eta,0)|^2\). It applies to every continuous compact signed seed dominated by the smooth height profile \(\eta\). [Normalized zero-mode synthesis and its constant component](https://github.com/UyNewNas/goldbach-formalization/blob/32d541884c85748e3fb18f7a83801b2f8b16e359/docs/source-only/20261112-resume/t04/projection-next/api-selection/Part3ActualHorocycleSynthesisBound.lean)

With \(c=2\pi |m|\), use the compact height seed

\[
  \sqrt y\,(cy)K_0(cy)\,(cy)^{iT}\,\chi_k(\log(cy)).
\]

The smooth cutoffs satisfy \(0\le\chi_k\le1\) and eventually equal one at each fixed log height. The modulation has absolute value one. The squared log norm of the uncut envelope involves \(\int_0^\infty q K_0(q)^2\,dq\). Its absolute constant moment involves \(\sqrt c\int_0^\infty q^{-1/2}K_0(q)\,dq\). Both are finite by the existing Mellin integrability theorems. This gives a spatial squared-norm bound depending only on \(N,m\) for every cutoff, central height and integral frame. [Two-factor Mellin calculation](https://github.com/UyNewNas/goldbach-formalization/blob/32d541884c85748e3fb18f7a83801b2f8b16e359/ImbalancedChen/Part3ActualComplexTwoKMellin.lean)

The cutoff probes converge to \(2J_T(\nu)\), where \(J_T(\nu)=\int_0^\infty q^{-iT}K_0(q)K_\nu(q)\,dq\). The factor two comes from the physical Fourier mode and the substitution \(q=cy\). At \(T>0\), the existing four-Gamma integral and the half-argument and unit-argument reflection formulas give

\[
 |J_T(it)|^2=
 \frac{\pi^3}{4}
 \frac{\sinh(\pi T)}
 {T\bigl(\cosh(\pi T)+\cosh(\pi t)\bigr)^2}.
\]

For \(T\ge1\) and \(\bigl||t|-T\bigr|\le1\), this bounds \(1/\cosh(\pi t)\) by a universal constant times \(T|J_T(it)|^2\). The choice \(\max(1,T)\) also covers the initial band. For exceptional orders \(\alpha\in[0,1/2]\), the real quantity \(J_0(\alpha)=[\Gamma((1+\alpha)/2)\Gamma((1-\alpha)/2)]^2/4\) has a positive minimum. The native discrete Bessel inequality acts on every finite subset of the actual basis. The continuous inequality uses the previously identified physical orthogonal projection and the true measurable compact-seed coefficients. Fatou's lemma transfers its uniform bound to the uncut probes. [Physical continuous projection](https://github.com/UyNewNas/goldbach-formalization/blob/32d541884c85748e3fb18f7a83801b2f8b16e359/docs/source-only/20261112-resume/t04/projection-next/Part3OriginalProjectedContinuousCovariance.lean)

## Scope in the original trace

The result supplies local spectral mass for the actual frequencies used by the two marked sums. Finite linear combinations and Cauchy–Schwarz can use it to bound a mixed coefficient product. The original source assigns the infinity observation to the first packet and cusp one to the signed second packet. Its \(\overline{M(R)}N(R)\) and \(dt/(4\pi\cosh(\pi t))\) agree with the weight-zero convention of Drappeau (4.11), (4.14) and (4.18)–(4.19). The prescribed-test expansion of the complete automorphic trace, the same-sign holomorphic and \(J\) terms, and the level- and packet-uniform large-sieve estimates with all \(7/32\) costs remain open in this package. [Original opposite-sign two-probe trace](https://github.com/UyNewNas/goldbach-formalization/blob/32d541884c85748e3fb18f7a83801b2f8b16e359/docs/source-only/20261112-resume/t04/bessel-next/Part3OriginalOppositeMarkedKuznetsov.lean) [Drappeau, §4.3](https://arxiv.org/pdf/1504.05549v4#page=11) [Manuscript §10](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L463-L483)

The files have source, dependency and hash checks. Same-source kernel verification and the inherited staging obligations remain outstanding. Formal credit is zero.
