# Independent fixed-weight Petersson normalization at infinity and cusp one

This calculation fixes the interface for the original positive row. It uses the original \(\Gamma_0(z)\) with trivial multiplier, its width-one normalized scaling matrices, \(p>0\), \(h=\mathrm{traceIndex}>0\), and \(k=2r\) with \(r\ge1\). Write \(a_{\mathfrak a,f}(m)\) for the ordinary \(e(mw)\) coefficient of \(f|_k\sigma_{\mathfrak a}\). The reviewed per-form source gives
\[
 R_{\mathfrak a,f}(m)=\frac{\sqrt m\,a_{\mathfrak a,f}(m)}{(4\pi m)^{k/2}} .
\]
The physical scalar product is conjugate-linear in its first argument and integrates \(\overline{f}g\,y^k\,dx\,dy/y^2\) on the actual quotient. The single-form identities supply the coefficients and their phases. A trace theorem must also realize the whole cusp-form space with this scalar product, unfold the positive-frequency representing vector, and identify its Fourier coefficients at the other frame.

## Two evaluations of the Poincaré coefficient

For the weight-\(k\) Poincaré series with seed \(e(mw)\) at cusp \(\mathfrak a\), unfolding its scalar product with \(f\) gives
\[
 \langle P_{\mathfrak a,m},f\rangle=
 a_{\mathfrak a,f}(m)\int_0^\infty y^{k-2}e^{-4\pi m y}\,dy
 =a_{\mathfrak a,f}(m)\frac{\Gamma(k-1)}{(4\pi m)^{k-1}}.
\]
In a full orthonormal basis, the \(n\)-th coefficient of \(P_{\mathfrak a,m}|_k\sigma_{\mathfrak b}\) is consequently \(\Gamma(k-1)(4\pi m)^{1-k}\sum_f\overline{a_{\mathfrak a,f}(m)}a_{\mathfrak b,f}(n)\). The geometric evaluation of that same coefficient is the zero-denominator orbit plus
\[
 2\pi i^{-k}(n/m)^{(k-1)/2}
 \sum_{C>0}\frac{S_{\mathfrak a\mathfrak b}(m,n;C)}{C}
 J_{k-1}(4\pi\sqrt{mn}/C).
\]
Dividing by the displayed power of \(n/m\) and substituting the native \(R\) produces
\[
 \boxed{4\pi\Gamma(k-1)\sum_f\overline{R_{\infty,f}(p)}R_{1,f}(h)
  =\mathbf 1_{z=1,\,p=h}
     +2\pi i^{-k}\sum_{\substack{d\ge1\\(d,z)=1}}
       \frac{S_{\infty,1}(p,h;d\sqrt z)}{d\sqrt z}
       J_{k-1}\!\left(\frac{4\pi\sqrt{ph}}{d\sqrt z}\right).}
\]
At level \(z>1\), an integral matrix carrying infinity to 1 has first column \(\pm(1,1)^t\), incompatible with the lower-left divisibility condition. At level one, the actual cusp-one scaling \(\begin{psmallmatrix}1&0\\1&1\end{psmallmatrix}\) belongs to the group. Its phase is one when \(p=h\). In this formula the group sum already contains the cusp-one translation phase. The outside \(\mathrm{traceBeta}\) factor in the original marked row performs the prescribed conversion to its ordinary Kloosterman coefficient.

## Comparison with the typeset reference

Drappeau's printed (4.7) uses the \(a,\rho\) convention above and the displayed scalar product in §4.1.2 has the raw hyperbolic area. The displayed fixed-weight (4.26), stated only for \(\mathfrak a=\mathfrak b\), prints \(4\Gamma(k-1)\sum_f\overline{R_{\mathfrak a,f}(m)}R_{\mathfrak a,f}(n)\). With the other conventions held fixed this misses a factor of \(\pi\). The discrepancy concerns a normalization in the large-sieve derivation, where a fixed scalar does not affect an order estimate. The exact physical equality needs the scalar from unfolding. The cross-cusp evaluation additionally requires the actual two-frame geometric argument. The positive-sign identity is (4.13), its holomorphic term is (4.15), and the negative-sign continuous and Maass terms are (4.18) and (4.19).

For a compactly supported smooth positive-axis test \(\Phi\), Drappeau's \(\dot\Phi(k)=4i^k\int_0^\infty J_{k-1}(x)\Phi(x)\,dx/x\) multiplies \(\Gamma(k)\) and the \(R\)-product. Hence the holomorphic contribution from the fixed-weight diagonal is \(\mathbf 1_{z=1,p=h}\,(2r-1)(-1)^r \int J_{2r-1}\Phi\,dx/x\,/\,\pi\). The recurrence \(nJ_n=x(J_{n-1}+J_{n+1})/2\) makes the sum over \(r\) telescope. Its \(R\)-th partial sum of Bessel factors equals \(-xJ_0(x)/2+(-1)^R xJ_{2R}(x)/2\). On the fixed compact support the last term tends uniformly to zero by the power series. Thus the summed holomorphic diagonal is \(-\mathbf 1_{z=1,p=h}(2\pi)^{-1}\int J_0\Phi\,dx\). Cancellation with the other parts of the full positive trace belongs to the separate inverse-transform argument. The final (4.13) has no additional free-standing diagonal term.

Define \(n=k-1\), \(e_k=i^k\), \(S_k=\sum_{C>0} S_{\infty,1}J_n/C\), and \(\Delta_k=\delta+2\pi S_k/e_k\). Write \(H=\sum_k n\dot\Phi(k)\Delta_k/(4\pi)\) for the holomorphic **spectral** contribution and \(G_{\rm hol}=\sum_k n\dot\Phi(k)S_k/(2e_k)\) for its Bessel **geometric** projection. With \(D=\delta(2\pi)^{-1}\int J_0\Phi\,dx\), the preceding identity reads \(H=G_{\rm hol}-D\), equivalently \(G_{\rm hol}=H+D\). In the same orientation the scalar remainder must yield \(G_{\rm rem}=E+M-D\) to obtain \(G_{\rm hol}+G_{\rm rem}=H+E+M\). The fixed-weight calculation establishes the first pair of identities once its Petersson inputs and series interchanges hold. The equality for \(G_{\rm rem}\) requires its own inverse-transform proof.

## Source obligations and the weight-two endpoint

At the pinned baseline, \(\mathrm{OriginalHolomorphicCuspFrames}\) gives the normalization for each actual form. Mathlib's \(\mathrm{UpperHalfPlane.petersson}\) is a pointwise integrand. To obtain a positive definite integral one can use the finite union of modular fundamental cells, the cusp decay of the transformed form on each cell, and full support or interior positivity to detect a nonzero holomorphic function. A short finite-dimensionality argument uses the existing norm to full level. The finite-dimensional full-level space of weight \(k[\mathrm{SL}_2(\mathbb Z):\Gamma_0(z)]\) is separated by finitely many point evaluations, since the common kernel of all evaluations is zero. If a level-\(z\) form vanishes at those points, its norm also vanishes there by the identity coset factor. Injectivity of the norm at zero gives \(f=0\). The finite evaluation map on the level-\(z\) space is complex-linear, yielding finite dimensionality once the actual algebraic space is fixed.

The elementary absolute convergence of holomorphic exponential Poincaré series starts at \(k>2\). For \(k=2\) the naive absolute bound on the parabolic cosets fails. Directly on the geometric side \(J_1(x)=O(x)\) at the origin, so a saving over the trivial Kloosterman estimate yields absolute convergence of the positive-modulus series. A separate justified limiting or grouped argument still has to connect that series to the physical weight-two reproducing vector. Existence of a basis, a per-form Fourier identity, and absolute convergence of the final Bessel series address different steps of this identification.

The derivation uses the locally pinned Drappeau journal PDF, pp. 12–16, formulas (4.7), (4.9), (4.13)–(4.19) and (4.26), together with the native frame source. The printed (4.26) was checked on the rendered page.

## Cross-cusp phases and weight two

For \(z\ge1\) and \((d,z)=1\), the source theorem `cuspOneMatrixSum_eq_phase_mul_kloosterman` identifies the actual positive phase as \(e(h/z)S_d(p\overline z,h)\), where \(\overline z\) is the inverse of \(z\) modulo this particular \(d\). Its scale is \(C=d\sqrt z\). This is the same matrix phase \(e(pA/C+hD/C)\) that comes from extracting the positive \(h\)-coefficient of the periodized exponential. The level-one shift is integral. The zero lower-left class then contributes its horizontal coefficient \(\mathbf1_{p=h}\).

At an arbitrary integral cusp matrix \(g=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\), one can use the common period \(z\). For a reduced bottom row \((C,D)\) of \(\gamma g\), \(\gamma\in\Gamma_0(z)\) imposes \(Cd-Dc\equiv0\pmod z\). Expanding this condition in the \(z\) additive characters and writing \(D=D_0+Cj\) gives the finite phase

\[
\sum_{\substack{t\bmod z\\z\mid n-tcC}}e(tCd/z)S_C\!\left(p,\frac{n-tcC}{z}\right).
\]

A single summable arithmetic majorant for fixed \(p\ne0\), all \(n\in\mathbb Z\) including zero, and arbitrary unit twists of \(p\) therefore covers every one of the finitely many cusp representatives. The pinned mathlib theorem `EisensteinSeries.qExpansion_identity_pnat` gives the periodization of \((w+\ell)^{-j}\) for every integer \(j\ge2\), including the limiting weight-two summand. After expanding \(\exp(-2\pi i p/(C^2w))\), the positive \(h\)-coefficient has the expected factor \(2\pi i^{-k}(h/p)^{(k-1)/2}J_{k-1}(4\pi\sqrt{ph}/C)/C\). The equality with the Fourier coefficient of the modular Poincaré vector additionally requires the justified denominator and horizontal limit exchanges.

For the Hecke deformation by \(\operatorname{Im}(\gamma w)^s\), the unfolded integral for \(s>0\) near lower height zero has absolute majorant \(y^{k/2+s-2}\) from the global cusp-form bound. For a compact range of \(s\downarrow0\), a grouped bound \(O(y^{1-k})\) for the nonidentity part on each cusp region \(y\ge1\) would dominate its pairing against \(f\) by \(O(y^{-1-k/2})\,dx\,dy\). The identity class is exponentially decreasing there. Thus weight two allows the required pairing limit once the cusp-uniform grouped estimate, local convergence and automorphy are proved for the actual deformation. These estimates specify the analytic evidence a full weight-two trace needs; the arithmetic bound and per-form Riesz calculation by themselves apply to smaller claims.
