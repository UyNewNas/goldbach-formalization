# Independent source review of the positive strip

**The 13 selected Lean modules pass independent static source review for the prescribed positive scalar strip.** They contain 64 public theorems and 20 public definitions or abbreviations. The proof-text result and the source selection cover the interval \(|\Im\xi|<1\). Elaboration and kernel acceptance remain pending. Formal credit is zero.

Fix an original period-64 marking \(\ell\), \(Y>0\), and \(\Phi(q)=\chi(q/Y)e(\ell(0)q/(64Y))\). The positive Bruhat argument is \(q=4\pi\sqrt{|a|mn}/(c\sqrt r)\). The source works for every \(q\geq0\) at the chosen scale. The original Poisson test, additive marking and positive support floor are retained. [Manuscript parameters](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-S1-Poisson-spectral-return-20261010.txt#L156-L188)

The integer \(J_n\) comes from the existing alternating Gamma series. Absolute convergence permits the product of two exponential Taylor series to be partitioned by the signed difference of the two indices. Splitting the result into odd orders gives both sine expansions used by the author. The positive-argument moments \(m_n=\int J_n(q)\Phi(q)\,dq/q\) have a factorial bound at the given scale. For complex strip arguments the same bound absorbs the factors \(n^r e^{An}\) on each compact set. The two entire representations of \(B\) therefore agree for the actual complex test. The bottom and top traces are respectively \(P+iQ\) and \(P-iQ\), with \(P\) even and \(Q\) odd. Integrating the compact test by parts on the appropriate half-strip gives uniform vertical-edge decay. The marked spectral coefficients enter after this complex-linear calculation.

With the angular Fourier convention \(\widehat f(\xi)=\int f(w)e^{-i\xi w}\,dw\), the width-\(\pi\) shift gives the top trace \(e^{-\pi\xi}\) times the bottom trace. The two vertical integrals tend to zero whenever \(|\Im\xi|<1\). The denominator \(1+e^{-\pi\xi}\) stays nonzero on that open strip. Integration by parts gives \(i\xi\widehat Q=\pi\widehat h\). Thus

\[
 \widehat h(\xi)=\frac{\xi}{\pi}\tanh(\pi\xi/2)\widehat P(\xi).
\]

Here \(P(w)=\int\Phi(q)\cos(q\cosh w)\,dq/q\). The derivative of \(Q\) also uses the ordinary cosine transform \(C_\Phi(s)=\int\Phi(q)\cos(qs)\,dq\). Its lack of a \(1/q\) follows by differentiating the tested sine phase. The global density \(h=Q'/\pi\) is smooth and even. Its derivatives of each fixed order satisfy \(O_{\ell,Y,r}(e^{-|w|})\). The real upper bound follows from the derivatives of the rapidly decreasing cosine transform evaluated at \(\cosh w\), together with the summable odd moment tail. Parity transfers it to the left half-axis.

Inverting the unweighted transform in the positive frequency variable \(s\) splits at \(1\). The low substitution \(s=\sin\theta\) contributes \(\cos\theta\) and the high substitution \(s=\cosh w\) contributes \(\sinh w\). For \(n=2j+1\), the separate rectangle for \(e^{i(q\sin z+nz)}\) has a vanishing left real part and right boundary coefficient \(i^{n+1}=-(-1)^j\). Orthogonality on the quarter interval supplies \(\pi J_n/2\). The high part of the series is dominated by \(e^{-w}\sum_n2n|m_n|\) on \(w>0\). The endpoint \(s=1\) carries zero Lebesgue measure. The resulting identity is pointwise

\[
 \Phi(q)-2\sum_{n\ {\rm odd}} n m_nJ_n(q)
      =\int_{\mathbb R}h(w)\cos(q\cosh w)\,dw,\quad q\geq0.
\]

At \(q=0\), \(\int h=0\). At \(w=0\), the actual holomorphic diagonal gives \(h(0)/2=(2\pi)^{-1}\int J_0(q)\Phi(q)\,dq\). The equal-cusp and equal-index indicator multiplies this scalar in the trace. T04's pinned zero-mode nonvanishing theorem supplies nonzero holomorphic multipliers at sufficiently high odd orders for each \(Y>0\). The subtraction retains all original odd rows at every marking. [Independent calculation](NORMALIZATION.md)

For the positive \(J\) transform, the real weight is \(4\widehat P(2t)\), evaluated at \(t/\pi\) in Mathlib's Fourier convention. At exceptional order \(0<\alpha<1/2\), it is \(4\widehat P(2i\alpha)\). The native division by \(\cosh(\pi t)\) or \(\cos(\pi\alpha)\) gives \(2\pi\widehat h(2t)/(t\sinh(\pi t))\) and \(-2\pi\widehat h(2i\alpha)/(\alpha\sin(\pi\alpha))\), respectively, away from zero. The original continuous measure has the additional fixed factor \(1/(4\pi)\). The threshold numerator is \(4\widehat P(0)\). The published and arXiv typesettings give the same signs and the same \(dq/q\) in (4.9) and (4.10). [Drappeau, equations (4.9), (4.10), (4.13), (4.15)–(4.17), arXiv v4 pp. 11–12](https://arxiv.org/pdf/1504.05549v4)

The final threshold proof differentiates the actual \(2t\)-frequency integral twice in \(t\). Its uniform majorant for order \(r\) is proportional to \(e^{-|w|}(2|w|)^r\), which is integrable for every fixed \(r\). At \(t=0\) the second derivative of its integrand contributes \(-4w^2h(w)\). The product rule on the positive multiplier contributes \(4\widehat P(0)\). Thus the original weight at zero equals \(-4\int w^2h(w)\,dw\). The two divisions in the native formulas use \(t\ne0\) and \(0<\alpha<1/2\), respectively.

The transport lemma assumes holomorphy and decay for its function \(B\), and the package constructs this \(B\) from the original test and proves both requirements. Evaluating the explicit density provides the prescribed geometric result. The positive physical packet approximations, exchanges with the spectral and ordered geometric sums, automorphic Petersson realization, and uniform \(7/32\) bounds remain distinct obligations. The high-frequency density asymptotic in the author’s proof text agrees with the independent calculation. It has no separately counted Lean theorem here. The pinned Mathlib checks and the corrected preliminary proof directions are recorded separately. [Upstream objects](UPSTREAM.json) [Pinned APIs](PINNED_API.json) [Source-by-source audit](SOURCE_AUDIT.json)
