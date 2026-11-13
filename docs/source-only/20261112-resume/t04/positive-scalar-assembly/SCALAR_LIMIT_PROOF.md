# The complementary positive-sign marked trace

Fix the original arguments \(D,r,k,z,\mathrm{upper},\mathrm{negativeM},J,j,\ell,Y>0\). Assume the licensed nonzero residue and the actual positive trace sign. Write \(p>0\) for a common Poisson mark, \(b=\operatorname{traceIndex}(n)>0\) for a source mark, \(C=d\sqrt z\), \(x=4\pi\sqrt{pb}/C\), and \(B_n=\operatorname{traceBeta}(n)\). In this note \(E\) denotes the continuous part of the marked spatial resolution, and \(M_{\mathrm{disc}}\) its physical Maaß sum. Both retain the original infinity marking conjugated against the source marking. The finite marking sums and \(1/(4\pi)\) can be left inside every limit.

Let \(\Phi=\mathrm{spectralTest}(\ell,Y)\) and \(m_l=\int_0^\infty J_l(q)\Phi(q)dq/q\). The actual strip construction gives the smooth even ratio profile \(h\) of integral zero and
\[
 \Phi_c(q)=\Phi(q)-\sum_{l\ {\rm positive\ odd}}2l m_lJ_l(q)
          =\int_{\mathbb R} h(w)\cos(q\cosh w)dw,\qquad
 h(0)/2=(2\pi)^{-1}\int_0^\infty J_0(q)\Phi(q)dq.
\]
Every derivative of \(h\) is bounded by its own constant times \(e^{-|w|}\). In angular Fourier convention the transform of \(h\) at \(2t\), multiplied by \(2\pi/(t\sinh\pi t)\), is the prescribed positive numerator divided by \(\cosh\pi t\). At \(2i\alpha\) its multiplier is \(-2\pi/(\alpha\sin\pi\alpha)\), giving the prescribed complementary numerator divided by \(\cos\pi\alpha\). The threshold is \(-4\int w^2h(w)dw\).

Take an even nonnegative smooth compact bump \(\eta\) of integral one and an even smooth plateau \(\chi\) supported in \([-2,2]\) which equals one on \([-1,1]\). Put
\[
 h_n(w)=\chi(w/(n+1))h(w)
           -\eta(w)\int\chi(v/(n+1))h(v)\,dv .
\]
This profile is smooth, compact and even, has integral zero and tends to \(h\) pointwise. The correcting scalar tends to zero by dominated convergence. Leibniz's rule, \((n+1)^{-j}\le1\), compactness of the derivatives of \(\eta,\chi\), and the bounds for \(h\) give \(|h_n^{(j)}(w)|\le C_j e^{-|w|}\) uniformly in \(n\).

For \(a,b'>0\) put \(p'=ab'\), \(w=\log(a/b')/2\), and
\[
 H_{R,n}(a,b')=\sqrt{p'}\,\eta(\log p'+R)h_n(w).
\]
Its support is in a positive compact rectangle for each fixed \(R,n\). It enters the original trace in the order \(\psi(a)\overline{\phi(b')}\). In coordinates \(s=\log p'+R\), \(a=e^{(s-R)/2+w}\), \(b'=e^{(s-R)/2-w}\), the determinant between the two log heights and \((s,w)\) has absolute value one. Each physical radial probe contributes \(2\sqrt yK_\nu(2\pi y)dy/y^2\), giving the spectral factor
\[
 F_{R,n}(\nu)=4\int_{\mathbb R^2}\eta(s)h_n(w)K_\nu(2\pi a)K_\nu(2\pi b')\,ds\,dw.
\]
A genuine index has real or imaginary order. The conjugate on its left original radial probe leaves each K factor real, by conjugate-order and even-order symmetry.

**Extension of the original two-probe pretrace.** Expand the smooth compact function \(H_{R,n}(e^u,e^v)\) by the existing period-64 double Fourier reconstruction on the integer log windows. There are finitely many active centers. On each center the twice-integrated Fourier series has coefficients bounded by a constant times \((1+|k|)^{-2}(1+|l|)^{-2}\). The atom \(\psi_{ik}(a)\overline{\phi_{jl}(b')}\) has modulus bounded by the same fixed compact windows independently of the frequencies. The actual signed-Poincaré norm inequality for the two marked packets and Hilbert Cauchy bound the sum over all discrete orders of each absolute physical product and the full integral over every incoming singular cusp by a common constant for these centers. Consequently the spectral products can be summed first over the frequencies or first over the automorphic spectrum. On the geometric side all participating heights are in one compact positive rectangle \([c,C_0]^2\). Orbital support implies \(ab'\le(x/(4\pi))^2\), furnishing one finite modulus set before summing that Fourier series. At each of these moduli, \(a\) is in the rectangle and \(ab'=(x/(4\pi))^2/(1+(X/a)^2)\) bounds \(|X|\). The geometric kernel has absolute integrable majorant \(1_{[c,C_0]}(a)a^{-2}1_{[-L,L]}(X)\). The diagonal is bounded by \(1_{[c,C_0]}(a)a^{-2}\). These estimates prove both Fubini exchanges and give the original trace for this \(H_{R,n}\) with its native normalizations.

**The orbital integral.** Put \(k_0=(x/(4\pi))^2\), \(\sigma=X/a\), and \(p'=k_0/(1+\sigma^2)\). The two signs of \(\sigma\) combine to a cosine with phase \(2\pi(a+b')\sigma\). At \(a=\sqrt{p'}e^w\) one has \(a+b'=2\sqrt{p'}\cosh w\). Thus its phase is \(4\pi\sqrt{k_0-p'}\cosh w\) for \(\sigma>0\). Here \(dX\,da/a^2=d\sigma\,da/a=d\sigma\,dw\). The inverse map has derivative absolute value \(k_0/[2p'\sqrt{p'}\sqrt{k_0-p'}]\). The original orbital prefactor \(4\pi/x=1/\sqrt{k_0}\), the factor two from \(\pm\sigma\), and the factor \(\sqrt{p'}\) in \(H_{R,n}\) give
\[
 \Phi_{R,n}(x)=\int_{\{s:p'<k_0\}}\eta(s)\sqrt{k_0/(k_0-p')}\,
                  V_n(4\pi\sqrt{k_0-p'})\,ds,\quad p'=e^{s-R},
 \qquad V_n(v)=\int h_n(w)\big(\cos(v\cosh w)-1\big)dw.
\]
The subtracted one integrates to zero. At \(z=1,p=b\) the source phase equals one. Both scaled seeds supply \(p^{-1}\) and \(a=py\) gives \(dy/y^2=p\,da/a^2\). The remaining diagonal is \(\int H_{R,n}(a,a)da/a^2=h_n(0)/2\) by \(s=2\log a+R\). All other pairs have zero identity cell. In particular an unweighted extra factor \(p\), a second source phase, or a half-line spectral normalization would change this equality.

**Height limit at fixed ratio window.** The five preceding sources prove uniform centered error \(O_n(e^{-R/4})\) on the complex order disk of radius \(3/4\), pointwise convergence at every fixed imaginary order outside it, and \(\cosh(\pi t)|F_{R,n}(it)|\ll_n |t|^{-3}\) for \(|t|\ge1,\ R\ge0\). The limit is \(L_n(\nu)=2\Gamma(\nu)\Gamma(-\nu)\int h_n\cosh(2\nu w)\,dw\) off zero, with \(L_n(0)=-4\int w^2h_n(w)dw\). For \(3/4\le|t|\le1\) the actual imaginary-order bound \( |K_{it}(x)|\le|\Gamma(it)|\,\mathrm{expMass}(B)\) applies uniformly for the two height arguments \(x\le B\). The remaining small interval is covered by the disk. On the cuspidal indices with \(\lambda<1/4\), the multiplicity-complete sublevel at this fixed level is finite. Positivity of each cuspidal eigenvalue gives its individual \(\alpha<1/2\). Every actual exceptional term therefore passes to its own limit. [Original eigenvalue positivity](https://github.com/UyNewNas/goldbach-formalization/blob/ca092596f3612af8b4da25b279ce9210091ee0cb/docs/source-only/20261110-yellow-closure-10t/t08_actual_spectral_supplier/Part3OriginalExceptionalJNativeCompletion.lean)

For the real spectrum, a unit band \(j\le |t|\le j+1\) costs \(O_{z,p,b}(1+j)\) for the original \(\cosh(\pi t)^{-1}\)-weighted absolute cross-products, by Cauchy applied to the two actual diagonal band costs. The majorant \((1+j)^{-3}\) is uniform in sufficiently large \(R\) at fixed \(n\). The sum of its band charges is finite. This justifies dominated convergence for the complete regular discrete spectrum and the full continuous line. A fixed \(x>0\) gives \(\Phi_{R,n}(x)\to V_n(x)\) by the compact \(s\) support. Taylor's real cosine bound gives \(|V_n(v)|\le C_n v^2\). The displayed orbital integral then satisfies \(|\Phi_{R,n}(x)|\le C_n x^2\) for every \(R\). The resulting \(d^{-3}\) geometric price times \(|S|\ll d\) is summable even by the trivial Kloosterman bound.

**Removal of the ratio cutoff.** The angular integrals for \(h_n\) converge to those for \(h\) at every actual frequency. For an exceptional height the dominated integrand has exponent \(-(1-2\alpha)|w|\), with a separate positive margin for each of the finitely many indices. At zero the second moments converge. To control the real line uniformly in \(n\), the identity
\[
 L_n(it)=\frac{2\pi}{t\sinh\pi t}\widehat h_n(2t)
\]
and the two integrations by parts in the regular Fourier integral give \(\cosh(\pi t)|L_n(it)|\ll |t|^{-3}\) for \(|t|\ge1\). At \(|t|\le1\), the centered kernel has absolute value at most \(4w^2\), by \(|\sin v|\le |v|\) and \(\sinh x\ge x\) for \(x\ge0\). The uniform integral of \(w^2e^{-|w|}\) and the preceding fixed-level band majorant therefore give the second dominated spectral limit. The continuous term has the actual \(\int_{\mathbb R}\widetilde\Phi(t)\sum_a\overline{M_a(t)}N_a(t)\,dt/(4\pi\cosh(\pi t))\).

Geometrically \(V_n(x)\to\Phi_c(x)\) by dominated convergence. For \(0<x\le1\), split the integral at \(|w|=\log(1/x)\), using \(|\cos v-1|\le\min(2,v^2/2)\), \(\cosh w\le e^{|w|}\), and \(|h_n(w)|\le C e^{-|w|}\). Both pieces are \(O(x)\) uniformly in \(n\), while the full integral is uniformly bounded for \(x\ge1\). The fixed nonzero first-mark arithmetic supplier gives \(\sum_d B_p(d)d^{-2}<\infty\) for the corresponding unit twist, including its actual \(\infty/1\) sum. It dominates the original \(S/C\) times \(V_n(4\pi\sqrt{pb}/C)\). Thus both geometric limits take place in the absolute modulus sum.

With \(D_{p,b}=\mathbf1_{z=1,p=b}(2\pi)^{-1}\int J_0\Phi\), the twice-limited identity is
\[
 \sum_{n,p}W_p B_n\left(D_{p,b}+\sum_d S_{p,b}(d)\Phi_c(4\pi\sqrt{pb}/C)/C\right)
 = M_{\mathrm{disc}}+E.
\]
This is \(G_{\mathrm{rem}}=M_{\mathrm{disc}}+E-D\) with the original finite marking on \(D\). The even-weight Petersson contribution in the same conventions satisfies \(G_{\mathrm{hol}}=H+D\), so the two identity cells cancel in the total original positive trace. The latter addition requires its separate Petersson supplier, including weight two. The same-source kernel checks and the estimates uniform in level and marks required for the \(7/32\) energy are separate tasks.

