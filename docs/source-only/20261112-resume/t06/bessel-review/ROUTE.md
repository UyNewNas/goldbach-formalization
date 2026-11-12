# Opposite-sign Kuznetsov normalization

At the published geometric pretrace revision `4733b07d186b2b6aad89e5b9b782c35cc27ebd37`, write \(\Phi=\mathrm{orbitTest}(-1,\psi,\phi)\) and \(k=(u/(4\pi))^2\). The geometric test has an outer conjugation. In its two real integration variables set \(a=Y,\ s=X/a,\ b=k/[a(1+s^2)]\), then \(s=\sinh v\). The integrand contains \(\psi(a)\overline{\phi(b)}\), and its phase is \(\exp(i(A-B)\sinh v)\) with \(A=2\pi a, B=2\pi b\). The substitutions give

\[
\frac{du}{u}=\frac{db}{2b},\quad
\frac{dX\,dY}{Y^2}=\frac{da\,ds}{a},\quad
\frac{4\pi}{u}=\frac1{\sqrt{ab(1+s^2)}},\quad
u=2\sqrt{AB}\cosh v.
\]

Their product has density \(da\,db\,dv/[2(ab)^{3/2}]\). In the inner \(v\)-integral the positive-argument identity needed for order \(\nu\) is

\[
\int_{\mathbb R} e^{i(A-B)\sinh v}K_{2\nu}(2\sqrt{AB}\cosh v)\,dv=K_\nu(A)K_\nu(B).
\]

The cosine-Laplace expansion of \(K_{2\nu}\) introduces a second real variable \(w\). The existing horizontal contour shift at order zero gives the inner integral \(2K_0(\sqrt{4AB\cosh^2 w+(A-B)^2})\). Its argument squared equals \(A^2+B^2+2AB\cosh(2w)\). The pre-existing unequal-argument product formula supplies the remaining integral. For fixed order, absolute Fubini on compact positive \(a,b\) follows from separation by a positive support floor. With \(c=2\sqrt{A_0B_0}>0\), the absolute integrand in \(v,w\) is bounded by

\[
e^{-c\cosh v/2}\,e^{-c\cosh w/2+2|\operatorname{Re}\nu|\,|w|}.
\]

The old physical order probe is \(P_\psi(\nu)=2\int_0^\infty \overline{\psi(a)}K_\nu(2\pi a) da/a^{3/2}\). Thus \(8\int K_{2\nu}(u)\Phi(u)du/u=\overline{P_\psi(\bar\nu)}P_\phi(\nu)\). The two orders on the right may be identified when \(\nu\) is real or purely imaginary because \(K_{-\nu}=K_\nu\). For \(\nu=it\) the earlier spatial density becomes the induced Kuznetsov transform \(H_\Phi(t)=8\cosh(\pi t)\int_0^\infty K_{2it}(q)\Phi(q)dq/q\) in the convention \(dt/(4\pi\cosh(\pi t))\).

For the manuscript cutoff \(F(q)=\mathrm{spectralTest}\,\ell\,Y\,q\), the fixed source proves smoothness and compact support inside \((Y/16,16Y)\) when \(Y>0\). Therefore \(r\mapsto F(e^r)\) is an actual compact smooth radial test. The pointwise KL inversion at \(r=\log x\) applies at each \(x>0\). In the old inversion, \(d\tau=2dt\) and the weight is \((2/\pi^2)\tau\sinh(\pi\tau)\). In the arithmetic normalization this gives

\[
F(x)=\frac{2}{\pi^2}\int_0^\infty t\sinh(\pi t)H_F(t) K_{2it}(x)\,dt.
\]

The pointwise inversion is a scalar identity. An extension of the *automorphic trace* to the manuscript test also needs a passage to the limit for the actual geometric evaluations and the signed spectral measure. For fixed nonzero markings the geometric arguments are a sequence tending to zero. Compact support uniformly separated from zero reduces this to finitely many moduli. Without such a common support bound, an independently summable tail estimate is needed. On the spectral side the required convergence concerns the sums of the weighted native basis coefficients and the matching integral over every singular cusp. The radial KL norm and the preceding physical Hilbert projection do not by themselves control this signed measure. Full same-sign arithmetic traces additionally involve holomorphic forms. The manuscript's regular and exceptional sieve inequalities and its all-cost exponent require separate estimates.

Drappeau (4.11) prints the prefactor \(8i^{-\kappa}\cosh(\pi t)\). The manuscript uses weight zero, so this is exactly the derived prefactor. In (4.18) and (4.19) the continuous and cuspidal terms both carry \(\sqrt{mn}\) times the product of Whittaker amplitudes, with \(dt/(4\pi\cosh(\pi t))\) in the continuous term. The source's \(R=\sqrt{|n|}\rho\) gives these frequency factors. [Drappeau, pp. 11–12](https://arxiv.org/pdf/1504.05549v4#page=11)

Pascadi (3.18) prints the opposite-sign transform with prefactor \(4/\pi\), while (3.15) defines the Fourier amplitudes using \(\sqrt y\,\rho_P K_P\) and refers to Deshouillers–Iwaniec p. 264 for the normalization of \(K_P\). The present physical formula uses \(2\sqrt y\,R K_{\rm std}\) with the actual cosine-Laplace kernel. For the same spatial measure, if \(K_P=cK_{\rm std}\) for a positive constant \(c\), matching Fourier sections gives \(\rho_P=2R/c\). The resulting opposite-sign multiplier in the native product would be \(16/(\pi c)\). Identifying this with the derived coefficient \(8\) needs \(c=2/\pi\) or an explicitly verified change of the other normalization data. This is a condition for identifying two printed conventions and does not assume that value of \(c\). [Pascadi, §3.3](https://arxiv.org/html/2404.04239v3#S3.SS3)
