# The positive scalar density for the prescribed test

For every original period-64 marking \(\ell:D4\to\mathbb Z\) and \(Y>0\), the thirteen sources construct a smooth even density \(h\) for the positive-sign, weight-zero test. Its Fourier transform, its integral representation after every holomorphic row is subtracted, and its diagonal value use the same \(h\). The definitions take the original complex function \(\Phi(q)=\mathrm{spectralTest}(\ell,Y,q)\). The estimates are at fixed \(\ell,Y\). The proof text accompanies the sources in [STRIP_PROOF.md](STRIP_PROOF.md). [Original spectral arguments and prescribed modes, lines 156–185](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-S1-Poisson-spectral-return-20261010.txt#L156)

## Geometric test

Write \(n=2j+1\), \(m_n=\int_0^\infty J_n(q)\Phi(q)\,dq/q\). `OriginalPositiveStrip20261112.original_projection` identifies the following two functions at every real \(q\ge0\).

\[
 \Phi(q)-\sum_{j\ge0}2n\,m_n J_n(q)
     =\int_{\mathbb R}h(w)\cos(q\cosh w)\,dw .
\]

The \(J_n\) are the original integer orders of the Gamma-series Bessel function. Multiplying its two exponential Taylor series gives the odd Jacobi–Anger identities at \(Z=i e^z\) and \(Z=e^{i\theta}\). The second identity gives the low interval \(s=\sin\theta\) of ordinary cosine inversion, with the factor \(\cos\theta\) from its derivative. The quarter rectangle for \(\exp(i(q\sin z+n z))\) gives the remaining odd moment exactly. Its right vertical edge contributes \(-(-1)^j\int_0^\infty e^{-nw}\cos(q\cosh w)\,dw\). This calculation includes \(q=0\). On the upper interval \(s=\cosh w\) the actual Jacobian is \(\sinh w\). Absolute integration and summation use \(\sum_j n|m_n|<\infty\) and the upper majorant \(e^{-w}\). [DLMF 10.12](https://dlmf.nist.gov/10.12)

## Scalar spectral weights

Set \(P(w)=\int_0^\infty\Phi(q)\cos(q\cosh w)\,dq/q\) and use \(\widehat f(\xi)=\int_{\mathbb R}f(w)e^{-i\xi w}\,dw\). `complex_strip` gives

\[
 \widehat h(\xi)=\frac{\xi}{\pi}\tanh(\pi\xi/2)\widehat P(\xi),
       \qquad |\operatorname{Im}\xi|<1 .
\]

The two entire representations of the corrected exponential test handle complex \(\Phi\). On the closed horizontal strip in the integration variable the source proves a uniform \(Ce^{-|\operatorname{Re}z|}\) estimate. For every frequency in the stated open strip it makes both vertical sides of the actual rectangle tend to zero. Integration by parts on its lower boundary supplies the factor \(i\xi\). At frequency \(2t\) the original Mathlib real Fourier frequency is \(t/\pi\).

`regular_read` and `exceptional_read` identify the original positive \(J\)-numerators with \(4\widehat P(2t)\) and \(4\widehat P(2i\alpha)\). After division by the original \(\cosh(\pi t)\) or \(\cos(\pi\alpha)\), `native_regular` and `native_complementary` give respectively
\[
 \frac{2\pi\,\widehat h(2t)}{t\sinh(\pi t)}
 \quad(t\ne0),\qquad
 -\,\frac{2\pi\,\widehat h(2i\alpha)}{\alpha\sin(\pi\alpha)}
 \quad(0<\alpha<1/2).
\]
`threshold_second_moment` identifies the continuous original value at \(t=0\) as \(-4\int_{\mathbb R}w^2h(w)\,dw\). Two dominated differentiations in the real parameter \(t\) supply this value at the original frequency \(2t\). `zero_mass` and `first_moment` give the zeroth and first vanishing moments. `smooth` and `OriginalPositiveStripDensity20261112.h_jets` give \(C^\infty\) regularity and \(C_{r,\ell,Y}e^{-|w|}\) bounds for every real derivative. [Drappeau, equations (4.9), (4.10) and (4.15)–(4.17)](https://arxiv.org/pdf/1504.05549v4#page=11)

`half_at_zero` uses the entire original even-weight sequence, beginning at weight two, to give
\[
 \frac{h(0)}2=\frac{1}{2\pi}\int_0^\infty J_0(q)\Phi(q)\,dq.
\]
The equal-cusp and equal-index indicator multiplies this scalar in the trace. All source equations are linear in the given complex test.

## Installation and remaining work

The terminal module is `ImbalancedChen.Part3OriginalPositiveStripThreshold`. `REGISTRY.json` lists the source order, public declarations and immutable dependencies. Install the selected T04 `Part3ActualPositiveCosineProfile` image `d4866d43…` from selection `126c0b0f…` and the previously recorded `Part3OriginalFullModulusTestJets` image `e54e3854…`. Both choices preserve the mathematical declarations consumed here.

The thirteen mathematical sources are uncompiled. This packet was checked by text and immutable source fingerprints. It supplies the scalar identities for the prescribed test. The small-height Bruhat packet limit, geometric and spectral exchanges, the Petersson interpretation of the holomorphic rows, and the uniform marked \(7/32\) budget require their respective suppliers. The dossier records the sharper leading tail in the mathematical derivation. The public Lean estimate used by the scalar consumer is the exponential bound at every derivative order. [Manuscript distribution comparison, section 10](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L461)
